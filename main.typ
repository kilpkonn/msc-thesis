#import "template.typ": *

#show: project.with(
  title: "Term Search in Rust",
  title_estonian: "Avaldise otsing programmeerimiskeeles Rust",
  thesis_type: "Master's thesis",
  thesis_type_estonian: "Magistritöö",
  authors: (
    (
      name: "Tavo Annus",
      student_code: "211564IAPM"
    ),
  ),
  supervisors: (
    (
      name: "Philipp Joram",
      degree: "MSc",
    ),
  ),
  location: "Tallinn",
  date: "May 12, 2024",
  dev: true,
)

= Introduction
Rust#cite-footnote("Rust", "2024-04-06","https://www.rust-lang.org/" ,"https://web.archive.org/web/20240409193051/https://www.rust-lang.org/") is a programming language for developing reliable and efficient systems.
The language was created by Graydon Hoare, later developed at Mozilla for Firefox, but is now gaining popularity and has found its way to the Linux kernel#cite-footnote("Linux 6.1-rc1", "2024-04-06", "https://lkml.org/lkml/2022/10/16/359", "https://web.archive.org/web/20240408110623/https://lkml.org/lkml/2022/10/16/359").
It differs from other popular systems programming languages such as C and C++ by focusing more on the reliability and productivity of the programmer.
Rust has an expressive type system that guarantees a lack of undefined behavior at compile type.
It is done with a novel ownership model and is enforced by a compiler tool called borrow checker.
The borrow checker rejects all programs that may contain illegal memory accesses or data races.

We will call the set of programs that can be compiled valid, as they are guaranteed to not cause undefined behavior.
Many programming languages with type systems that guarantee the program to be valid have tools that help the programmer with term search i.e. by searching for valid programs (usually called expressions in Rust) that satisfy the type system.
Rust, however, does not have tools for term search, although the type system makes it a perfect candidate for one.
Consider the following Rust program in @into-example-1:
#figure(
sourcecode()[
```rs
enum Option<T> { None, Some(T) }

fn wrap(arg: i32) -> Option<i32> {
    todo!();
}
```],
caption: [
    Rust function to wrap `i32` in `Option`
  ],
) <into-example-1>


From the types of values in scope and constructors of ```rust Option```, we can produce the expected result for ```rust todo!()``` by applying the constructor ```rust Some``` to ```rust arg``` and returning it.
By combining multiple type constructors as well as functions in scope or methods on types, it is possible to produce more complex valid programs.

== Motivation
Due to Rust's expressive type system, programmers might find themselves quite often wrapping the result of some function behind multiple layers of type constructors. For example, in the web backend framework `actix-web`#cite-footnote("Actix", "2024-04-06", "https://actix.rs/", "https://web.archive.org/web/20240329223953/https://actix.rs/"), a typical JSON endpoint function might look something like shown in @motivation-example-1.
#figure(
sourcecode()[
```rs
struct FooResponse { /* Struct fields */ }

#[get("/foo")]
async fn foo() -> Option<Json<FooResponse>> {
    let service_res = service.foo(); // Get a response from some service
    Some(Json(FooResponse {
        /* Fill struct fields from `service_res` */
    }))
}
```],
caption: [
    Example endpoint in `actix-web` framework
  ],
) <motivation-example-1>

We can see that converting the result ```rust service_res``` from the service to ```rust FooResponse``` and wrapping it in ```rust Some(Json(...))``` can be automatically generated just by making the types match.
This means that term search can be used to reduce the amount of code the programmer has to write.

When investigating common usage patterns among programmers using large language models for code generation, @how-programmers-interact-with-code-generation-models[p. 19] found two patterns:
1. Language models are used to reduce the amount of code the programmer has to write therefore making them faster.
  They call it the _acceleration mode_.
2. Language models are used to explore possible ways to complete incomplete programs.
  This is commonly used when a programmer is using new libraries and is unsure how to continue.
  They call this usage pattern _exploration mode_.

We argue that the same patterns can be found among programmers using term search.

In acceleration mode, term search is not as powerful as language models, but it can be more predictable as it has well-defined tactics that it uses rather than deep neural networks.
There is not so much "wow" effect - it just produces code that one could write by trying different programs that type-check.

However, we expect term search to perform well in _exploration mode_.
@how-programmers-interact-with-code-generation-models[p. 10] finds that programmers tend to explore only if they have confidence in the tool.
As term search only produces valid programs based on well-defined tactics, it is a lot easier to trust it than code generation based on language models that have some uncertainty in them.

== Research Objectives
The main objective of this thesis is to implement a tactics-based term search for the programming language Rust.
The algorithm should:
- only produce valid programs, i.e. programs that compile
- finish fast enough to be used interactively while typing
- produce suggestions for a wide variety of Rust programs
- not crash or cause other issues on any Rust program

Other objectives include:
- Evaluating the fitness of tactics on existing large codebases
- Investigating term search usability for auto-completion


== Contributions of the thesis
In this thesis, we make the following contributions:
- @background gives an overview of term search algorithms used in other languages and autocompletion tools used in Rust and mainstream programming languages. We also introduce some aspects of the Rust programming language that are relevant for the term search.
- @design introduces term search to Rust by extending the official language server of the Rust programming language, `rust-analyzer`. 
  We discuss the implementation of the algorithm in detail as well as different use cases.
  In @tactics, we describe the capabilities of our tool.
- @evaluation evaluates the performance of the tool. We compare it to mainstream tools, some machine learning based methods and term search tools in other programming languages.
- @future-work describes future work that would improve our implementation. This includes technical challenges, but also describes possible extensions to the algorithm.

We have upstreamed our implementation of term search to the `rust-analyzer` project.
It is part of the official distribution since version `v0.3.1850`#cite-footnote("Rust Analyzer Changelog #221", "2024-04-06", "https://rust-analyzer.github.io/thisweek/2024/02/19/changelog-221.html", "https://web.archive.org/web/20240412220709/https://rust-analyzer.github.io/thisweek/2024/02/19/changelog-221.html"), released on February 19th 2024.
An archived version can be found at the Software Heritage Archive #link("https://archive.softwareheritage.org/browse/revision/6b250a22c41b2899b0735c5bc607e50c3d774d74/?origin_url=https://github.com/kilpkonn/rust-analyzer&snapshot=25aaa3ceeca154121a5c2944f50ec7b17819a315")[`swh:1:rev:6b250a22c41b2899b0735c5bc607e50c3d774d74`].

= Background <background>
In this chapter, we will take a look at the type system of the Rust programming language to understand the context of our task.
Next, we will take a look at what the term search is and how it is commonly used.
Later, we will study some implementations for term search to better understand how the algorithms for it work.
In the end, we will briefly cover how _autocompletion_ is implemented in modern tools to give some context of the framework we are working in and tools that we are improving on.

== The Rust language
Rust is a general-purpose systems programming language first released in 2015#cite-footnote("Announcing Rust 1.0", "2024-04-06", "https://blog.rust-lang.org/2015/05/15/Rust-1.0.html", "https://web.archive.org/web/20240406065426/https://blog.rust-lang.org/2015/05/15/Rust-1.0.html").
It takes lots of inspiration from functional programming languages, namely, it supports algebraic data types, higher-order functions, and immutability.

=== Type system
Rust has multiple different kinds of types.
There are scalar types, references, compound data types, algebraic data types, function types, and more.
In this section we will discuss types that are relevant for the term search implementation we are building.
We will ignore some of the more complex data types such as function types as implementing term search for them is out of scope for this thesis.

Scalar types are the simplest data types in Rust.
A scalar type represents a single value.
Rust has four primary scalar types: integers, floating-point numbers, booleans, and characters.

Compound types can group multiple values into one type.
Rust has two primitive compound types: arrays and tuples.
An array is a type that can store a fixed amount of elements of the same type.
Tuple, however, is a type that groups values of different types.
Examples for both array and tuple types can be seen in @rust-types on lines 2 and 3.

Reference types are types that contain no other data than a reference to some other type.
An example of a reference type can be seen in @rust-types on line 4.

#figure(
sourcecode()[```rs
let a: i32 = 0; // Scalar type for 32 bit signed integer
let b: [u8, 3] = [1, 2, 3]; // Array type that stores 3 values of type `u8`
let c: (bool, char, f32) = (true, 'z', 0.0); // Tuple that consists of 3 types
let d: &i32 = &a; // Reference type to `i32`
```],
caption: [
    Types in Rust
  ],
) <rust-types>

Rust has two kinds of algebraic types: _structures_ (also referred as `struct`s) and _enumerations_ (also referred as `enum`s).
Structures are product types, and enumerations are sum types.
Each of them comes with their own type constructors.
Structures have one type constructor that takes arguments for all of its fields.
Enumerations have one type constructor for each of their variants.

Both of them are shown in @rust-type-constructor.

#figure(
sourcecode()[```rs
// Product type, has values for both `x` and `y`
struct Foo {
  x: i32,
  y: bool,
}

// Sum type, has values for either constructor `A` or `B`
enum Bar {
  A(i32),
  B(bool),
}

fn main() {
  let foo = Foo { x: 1, y: true };  // Initialize struct
  let bar = Bar::B(false);          // Initialize enum with one of it's variants
}
```],
caption: [
    Sum and product types in Rust
  ],
) <rust-type-constructor>

To initialize a `struct`, we have to provide terms for each of the fields it has, as shown on line 12.
For `enum`, we choose one of the variants we wish to construct and only need to provide terms for that variant.
Note that structures and enumeration types may both depend on generic types, i.e. types that are specified at the call site rather than being hard-coded to the type signature.
For example, in @rust-type-constructor-generics, we made the struct ```rust Foo``` generic over `T` by making the field `x` be of generic type `T` rather than some concrete type.
A common generic enum in Rust is the ```rust Option``` type which is used to represent optional values.
The ```rust None``` constructor takes no arguments and indicates that there is no value.
Constructor ```rust Some(T)``` takes one term of type `T` and indicates that there is some value stored in `Option`.
Initializing structs and enums with different types is shown in the `main` function at the end of @rust-type-constructor-generics.

#figure(
sourcecode()[```rs
struct Foo<T> {
  x: T,
  y: bool,
}

enum Option<T> {
  Some(T),
  None,
}

fn main() {
  let foo_bool: Foo<bool> = Foo { x: true, y: true};
  let foo_int: Foo<i32> = Foo { x: 123, y: true};
  let option_str: Option<&str> = Some("some string");
  let option_bool: Option<bool> = Some(false);
}
```],
caption: [
    Sum and product types with generics
  ],
) <rust-type-constructor-generics>

=== Type unification
It is possible to check for either syntactic or semantic equality between the two types.
Two types are syntactically equal if they have the same syntax.
Syntactic equality is a very restrictive way to compare types.
A much more permissive way to compare types is semantic equality.
Semantic equality of types means that two types contain the same information and can be used interchangeably.

Using syntactic equality to compare types can cause problems.
Rust high-level intermediate representation (HIR) has multiple ways to define a type.
This means that the same type can be defined in multiple ways that are not syntactically equal.

For example, in the program ```rust type Foo = i32```, the type ```rust Foo``` and the type ```rust i32``` are not syntactically equal.
However, they are semantically equal, as ```rust Foo``` is an alias for ```rust i32```.
This means that the types unify even though they are syntactically different.


To check for semantic equality of types we see if two types can be unified.
Rust's type system is based on a Hindley-Milner type system @affine-type-system-with-hindley-milner, therefore the types are compared in a typing environment.
In Rust, the _trait solver_ is responsible for checking the unification of types#cite-footnote("Rust Compiler Development Guide, The ty module: representing types", "2024-04-06", "https://rustc-dev-guide.rust-lang.org/ty.html", "https://web.archive.org/web/20231205205735/https://rustc-dev-guide.rust-lang.org/ty.html").
The trait solver works at the HIR level of abstraction, and it is heavily inspired by Prolog engines.
The trait solver uses "first-order hereditary harrop" (FOHH) clauses, which are Horn clauses that are allowed to have quantifiers in the body @proof-procedure-for-the-logic-of-hereditary-harrop-formulas.

Unification of types `X` and `Y` is done by registering a new clause `Unify(X, Y)` (the #emph[goal]) and solving for it.
Solving is done by a Prolog-like engine, which tries to satisfy all clauses registered in the typing environment. 
If a contradiction is found between the goal and the clauses, there is no solution, and the types `X` and `Y` do not unify.
If a solution is found, it contains a set of subgoals that still need to be proven.
If we manage to recursively prove all the subgoals, then we know that `X` and `Y` unify.
If some goals remain unsolved but there is also no contradiction, then simply more information is needed to guarantee unification.
How we treat the last case depends on the use case, but in this thesis, for simplicity, we assume that the types do not unify.
An example of unification can be seen in @rust-type-unification.

#figure(
sourcecode(highlighted: (14,))[
```rs
trait HasAnswer {
  type Answer;
  fn get_answer(&self) -> Self::Answer;
}

struct Life { /* fields */ }
impl HasAnswer for Life {
  type Answer = u8;
  fn get_answer(&self) -> Self::Answer { 42 }
}

fn main() {
  let life = Life { /* fields */ };
  let ans: u8 = life.get_answer();
  assert!(ans == 42);
}
```],
caption: [
    A unification problem for the return type of `life.get_answer()`.
    The goal is#linebreak()`Unify(<Life as HasAnswer>::Answer, u8)`.
    In context is `Implemented(Life: HasAnswer)` and `AliasEq(<Life as HasAnswer>::Answer = u8)`.
    From these clauses, we can solve the problem.
  ],
) <rust-type-unification>

=== Borrow checking
Another crucial step for the Rust compiler is borrow checking#cite-footnote("Rust Compiler Development Guide, MIR borrow check", "2024-04-06", "https://rustc-dev-guide.rust-lang.org/borrow_check.html", "https://web.archive.org/web/20230324181544/https://rustc-dev-guide.rust-lang.org/borrow_check.html").
The main responsibilities of the borrow checker are to make sure that:
- All variables are initialized before being used
- No value is moved twice or used after being dropped
- No value is moved while borrowed
- No immutable variable can be mutated
- There can be only one mutable borrow

Some examples of kinds of bugs that the borrow checker prevents are _use-after-free_ and _double-free_

The borrow checker works at the Middle Intermediate Representation (MIR) level of abstraction.
The currently used model for borrows is Non-Lexical Lifetimes (NLL).
The borrow checker first builds up a control flow graph to find all possible data accesses and moves.
Then it builds up constraints between lifetimes.
After that, regions for every lifetime are built up.
A region for a lifetime is a set of program points at which the region is valid.
The regions are built up from constraints:
- A liveness constraint arises when some variable whose type includes a region R is live at some point P. This simply means that the region R must include the point P.
- Outlives constraint ```rust 'a: 'b``` means that the region of ```rust 'a``` has to also be a superset of the region of ```rust 'b```.
From the regions, the borrow checker can calculate all the borrows at every program point.
An extra pass is made over all the variables, and errors are reported whenever aliasing rules are violated.

Rust also has a concept of two-phased borrows that splits the borrow into two phases: reservation and activation.
These are used to allow nested function calls like ```rust vec.push(vec.len())```.
These programs would otherwise be invalid, as in the example above ```rust vec.len()``` is immutably borrowed while ```rust vec.push(...)``` takes the mutable borrow.
The two-stage borrows are treated as follows:
- It is checked that no mutable borrow conflicts with the two-phase borrow at the reservation point (`vec.len()` for the example above).
- Between the reservation and the activation point, the two-phase borrow acts as a shared borrow.
- After the activation point, the two-phase borrow acts as a mutable borrow.

There is also an option to escape the restrictions of the borrow checker by using ```rust unsafe``` code blocks.
In an ```rust unsafe``` code block, the programmer has the sole responsibility to guarantee the validity of aliasing rules with no help from the borrow checker.


== Term search <term-search>
Term search is the process of generating terms that satisfy some type in a given context.
In automated theorem proving, this is usually known as proof search.
In Rust, we call it a term search, as we don't usually think of programs as proofs.

The Curry-Howard correspondence is a direct correspondence between computer programs and mathematical proofs.
The correspondence is used in proof assistants such as Coq and Isabelle and also in dependently typed languages such as Agda and Idris.
The idea is to state a proposition as a type and then prove it by producing a value of the given type, as explained in @propositions-as-types.

For example, if we have an addition on natural numbers defined in Idris as shown in @idirs-add-nat.
#figure(
sourcecode()[
```hs
add : Nat -> Nat -> Nat
add Z     m = m
add (S k) m = S (add k m)
```],
caption: [
    Addition of natural numbers in Idris
  ],
) <idirs-add-nat>
We can prove that adding any natural number `m` to 0 is equal to the natural number `m`.
For that, we create a declaration `add_zero` with the type of the proposition and prove it by defining a program that satisfies the type.
#figure(
sourcecode()[
```hs
add_zero : (m : Nat) -> add Z m = m  -- Proposition
add_zero m = Refl                     -- Proof
```],
caption: [
    Prove $0 + n = n$ in Idris
  ],
) <idirs-plus-reduces-z>
The example above is quite trivial, as the compiler can figure out from the definition of `add` that ```hs add Z m``` is defined to be `m` according to the first clause in the definition of `add`
Based on that we can prove `add_zero` by reflexivity.
However, if there are more steps required, writing proofs manually gets cumbersome, so we use tools to automatically search for terms that inhabit a type i.e. proposition.
For example, Agda has a tool called Agsy that is used for term search, and Idris has this built into its compiler.

=== Term search in Agda
Agda @dependently-typed-programming-in-agda is a dependently typed functional programming language and proof assistant.
It is one of the first languages that has sufficiently good tools for leveraging term search for inductive proofs.
We will be more interested in the proof assistant part of Agda, as it is the one leveraging the term search to help the programmer come up with proofs. 
As there are multiple options, we picked two that seem the most popular or relevant for our use case.
We chose Agsy as this is the well-known tool that is part of the Agda project itself, and Mimer, which attempts to improve on Agsy.

==== Agsy <agsy>
Agsy is the official term search based proof assistant for Agda.
It was first published in 2006 in @tool-for-automated-theorem-proving-in-agda and integrated into Agda in 2009#cite-footnote("Agda, Automatic Proof Search (Auto)", "2024-04-06", "https://agda.readthedocs.io/en/v2.6.4.1/tools/auto.html", "https://web.archive.org/web/20240410183801/https://agda.readthedocs.io/en/v2.6.4.1/tools/auto.html").

We will be looking at the high-level implementation of its algorithm for term search.
In principle, Agsy iteratively refines problems into more subproblems until enough subproblems can be solved.
This process is called iterative deepening.
This is necessary as a problem may, in general, be refined to infinite depth.

The refinement of a problem can produce multiple branches with subproblems.
In some cases, we need to solve all the subproblems.
In other cases, it is sufficient to solve just one of the subproblems to solve the "top-level" problem.
An example where we need to solve just one of the subproblems is when we try different approaches to come up with a term.
For example, we can either use some local variable, function or type constructor to solve the problem as shown in @agsy_transformation_branches.

#figure(
  image("fig/agsy_transformation_branches.svg", width: 60%),
  caption: [
    Solving the top-level problem requires solving _at least one_ of the subproblems
  ],
) <agsy_transformation_branches>

In case we use type constructors or functions that take multiple arguments, we need to solve all the subproblems of finding terms for arguments.
The same is true for case splitting: we have to solve subproblems for all the cases.
For example, shown in @agsy_all_branches we see that function ```hs foo : (A, B, C) -> Foo```
can only be used if we manage to solve the subproblems of finding terms of the correct type for all the arguments.

#figure(
  image("fig/agsy_all_branches.svg", width: 60%),
  caption: [
    Solving the top-level problem requires solving _all_ of the subproblems
  ],
) <agsy_all_branches>

Agsy uses problem collections (```hs PrbColl```) to model the subproblems that need to be all solved individually for the "top-level" problem to be solved.
Solution collections (```hs SolColl```) are used to keep track of solutions for a particular problem collection.
A solution collection has a solution for each of the problems in a corresponding problem collection.

The intuition for the tool is the following:
1. Given a problem, we create a set of possible subproblem collections out of which we need to solve _at least one_, as shown in @agsy_transformation_branches.
2. We attempt to solve _all_ the subproblem collections by recursively solving all the problems in the collection
3. If we manage to solve _all_ the problems in the collection, we use it as a possible solution, otherwise, we discard it as a dead end.

The algorithm itself is based on depth-first search (DFS) and consists of two subfunctions.
Function ```hs search: Problem -> Maybe [Solution]``` is the main entry point that attempts to find a set of solutions for a problem.
The function internally makes use of another function ```hs searchColl: PrbColl -> Maybe [SolColl]``` that attempts to find a set of solution collections for a problem collection.
The pseudocode for the `search` and `searchColl` functions can be seen in @agsy-snippet.

We model Problem collections as a list of subproblems together with a _refinement_ that produces those problems.
A refinement is a recipe to transform the problem into zero or more subproblems.
For example, finding a pair ```hs (Bool, Int)``` can be refined to two subproblems: finding a term of type ```hs Bool``` and another of type ```hs Int``` and applying the tuple constructor ```hs (_,_)```.
If we refine the problem without creating any new subproblems, then we can call the problem solved.
Otherwise, all the subproblems need to be solved for the solution to hold.
The refinement is stored so that, on a successful solution, we can construct the term solving the top-level problem from the solution collection.

The `search` algorithm starts by refining the problem into new problem collections.
Refining is done by tactics.
Tactics are essentially just a way of organizing possible refinements.
An example tactic that attempts to solve the problem by filling it with locals in scope can be seen in @agsy-example-tactic.

In case refining does not create any new problem collections, the base case is reached, and the problem is trivially solved (line 9 in @agsy-snippet).
When there are new problem collections, we try to solve _any_ of them.
In case we cannot solve any of the problem collections, then the problem is unsolvable, and we give up by returning ```hs Nothing``` (line 15).
Otherwise, we return the solutions we found.

We solve problem collections by using the `searchColl` function.
Problem collections where we can't solve all the problems cannot be turned into solution collections as there is no way to build a well-formed term with problems remaining in it.
We only care about cases where we can fully solve the problem, so we discard them by returning ```hs Nothing```.
On line 14 of @agsy-snippet we filter out unsuccessful solutions.

For successful solution collections, we substitute the refinements we took into the problem to get back the solution.
The solution is a well-formed term with no remaining subproblems, which we can return to the callee.

#figure(
sourcecode()[```hs
newtype ProbColl = (Refinement, [Problem])
newtype SolColl  = (Refinement, [Solution])

-- Find solutions to a problem
search :: Problem -> Maybe [Solution]
search p =
  case (createRefs p) of
    -- ↓ No new problems, trivially solved
    [] -> Just [TrivialSolution]
    -- ↓ Refinement created at least one subproblem
    subproblems ->
      -- Recursively solve subproblems; discard solution
      -- collections that are not fully solved.
      case (dropUnsolved $ map searchColl subproblems) of
        [] -> Nothing
        sols -> Just $ map (substitute p) sols
  where
    dropUnsolved :: [Maybe [SolColl]] -> [SolColl]
    dropUnsolved = flatten . catMaybes
        
-- Find a solution to every problem in problem collection
searchColl :: ProbColl -> Maybe [SolColl]
searchColl = sequence $ fmap search

-- Create refinements for problem
createRefs :: Problem -> [ProbColl]
createRefs p = flatten [tactic1 p, tactic2 p, tacticN p]

-- Create a solution to a problem from a refinement
-- and solutions to subproblems.
substitute :: Problem -> SolColl -> Solution
substitute = {- elided -}
```],
caption: [
    A high-level overview of the term search algorithm used in Agsy
  ],
) <agsy-snippet>

An example of a tactic can be seen in @agsy-example-tactic.
#figure(
sourcecode()[```hs
-- Suggest locals for solving any problem
tacticLocal :: Problem -> [ProbColl]
tacticLocal p = 
  let locals = localsInScope p
  in
    map (\l -> (Refinement::SubstituteLocal p l, [])) $
    filter (\l -> couldUnify p l) locals
```
],
caption: [
    An example tactic that attempts to solve the problem by using locals in scope
  ],
) <agsy-example-tactic>

As described above, the algorithm is built around DFS.
However, the authors of @tool-for-automated-theorem-proving-in-agda note that while the performance of the tool is good enough to be useful, it performs poorly on larger problems.
They suggest that more advanced search space reduction techniques can be used, as well as writing it in a language that does not suffer from automatic memory management.
It is also noted that there seem to be many false subproblems that can never be solved, so they suggest a parallel algorithm that could potentially prove the uselessness of those subproblems and reduce the search space.

==== Mimer
Mimer @mimer is another proof-assistant tool for Agda that attempts to address some of the shortcomings in Agsy.
As of February 2024, Mimer has become part of Agda#cite-footnote("Agda GitHub pull request, Mimer: a drop-in replacement for Agsy", "2024-04-06", "https://github.com/agda/agda/pull/6410", "https://web.archive.org/web/20240410183837/https://github.com/agda/agda/pull/6410") and will be released as a replacement for Agsy.
According to its authors, it is designed to handle many small synthesis problems rather than complex ones.
Mimer is less powerful than Agsy as it doesn't perform case splits.
On the other hand, it is designed to be more robust.
Other than not using case splits, the main algorithm follows the one used in Agsy and described in @agsy.

The main differences from the original Agsy implementation are:
1. Mimer uses memoization to avoid searching for the same term multiple times.
2. Mimer guides the search with branch costs.

Branch costs are a heuristic to hopefully guide the search to an answer faster than randomly picking branches.
Mimer gives lower costs to branches that contain more local variables and fewer external definitions.
The rationale for that is that it is more likely that the user wishes to use variables from the local scope than from outside of it.
However, they noted that the costs of the tactics need to be tweaked in future work, as this was not their focus.

=== Term search in Standard ML <standardml>
As a part of the RedPRL#cite-footnote("The red* family of proof assistants", "2024-04-06", "https://redprl.org/", "https://web.archive.org/web/20240316102035/https://redprl.org/") @redprl project, @algebraic-foundations-of-proof-refinement implements term search for Standard ML.

The algorithm suggested in @algebraic-foundations-of-proof-refinement keeps track of subproblems in an ordered sequence in which each induces a variable of the appropriate sort which the rest of the sequence may depend on.
This sequence is also called a telescope @telescopic-mappings-typed-lamda-calc.
The telescope is required to work on type systems with dependent types.
In contrast, typesystems without dependent types can use ordinary ```hs List``` data structure as there are no relations between subproblems.
This is also the case for Rust, so we will later resort to using `list` for its simplicity.

To more effectively propagate substitutions to subproblems in the telescope @algebraic-foundations-of-proof-refinement suggests using BFS instead of DFS.
The idea is to run all the tactics once on each subproblem, repeatedly.
This way, substitutions propagate along the telescope of subproblems after every iteration.
In the case of DFS, we would propagate the constraints only after exhausting the search on the first subproblem in the sequence.
To better understand the difference between the BFS approach suggested and the DFS approach, let's see how each of them works.

First, let's consider the DFS approach as a baseline.
The high-level algorithm for DFS is to first generate possible ways to refine the problem into new subproblems and then solve each of the subproblems fully before continuing to the next subproblem. 
In the snippet below, tactics create problem collections that are options we can take to refine the problem into new subproblems.
After that, we attempt to solve each set of subproblems to find the first problem collection where we manage to solve all the subproblems.
That problem collection effectively becomes our solution.
In @standardml-dfs-code we can see that the DFS fits functional style very well, as for all the subproblems, we can just recursively call the same `solve` function again.
Note that in the listing, the constraints are propagated to remaining problems only after the problem is fully solved.
#figure(
sourcecode()[```hs
solve :: Problem -> Maybe Solution
solve problem = 
  let 
    pcs: [ProblemCollection] = tactics problem  -- Generate possible refinements
  in
    head [combineToSolution x | Just x <- map solveDFS pcs] -- Find first solution

solveDFS :: ProblemCollection -> Maybe SolutionCollection
solveDFS [] = Just [] -- No subproblems => Empty solution collection
solveDFS (p:ps) = do
  sol <- solve p                      -- Return `Nothing` for no solution
  ps' <- propagateConstraints sol ps  -- Propagate constraints
  rest <- solvesolveDFS ps'           -- Attempt to solve other subproblems
  return sol : rest
```],
caption: [
    Pseudocode for DFS search
  ],
) <standardml-dfs-code>

Now let's look at how the BFS algorithm suggested in @algebraic-foundations-of-proof-refinement works.
The high-level algorithm for BFS is to generate possible ways to refine the problem into new subproblems and then incrementally solve all the subproblems in parallel.
The pseudocode for it can be seen in @standardml-bfs-code.

The algorithm starts by converting the given problem to a singleton problem collection.
Now the produced collection is fed into `solveBFS` function, which starts incrementally solving the problem collections.
In this example, we are using a queue to keep track of the problem collections we are solving.
Internally, the `solveBFS` function loops over the elements of the queue until either a solution is found or the queue becomes empty.
In the snippet, we check the status of the problem collection with a `status` function that tells us the status of the problem collection.
The status is either:
 - *AllSolved* for problem collections that do not have any unresolved subproblems in them and are ready to be converted into solutions.
 - *NoSolution* for problem collections that have remaining unresolved subproblems that we are unable to make any progress on.
 - *RemainingProblems* for all the problem collections that we can make progress on by incrementally stepping the problem further.
 In case of ```hs AllSolved``` we return the solution as we are done with the search.
 In case of ```hs NoSolution``` we discard the problem from the queue.
 Otherwise, (in the case of ```hs RemainingProblems```) we step the problem collection at the head of the queue and push the results back to the back of the queue.
 Now we are ready to keep iterating the loop again with the new problem collection at the head of the queue.

 Stepping the problem collection steps (or adds atomic refinements) to all problems in the problem collection and propagates the constraints to rest of the subproblems if refinements produce any new constraints.
 As the problem can generally be refined in multiple ways, the function returns a list of problem collections that are all possible successors to the input problem collection.
 Propagating the constraints is done in the `propagateConstraints` function.
 The function adds new constraints arising from the head element refinements to all subproblems in the problem collection.

#figure(
sourcecode()[```hs
solve :: Problem -> Maybe Solution
solve problem = 
  let 
    pcs: [ProblemCollection] = toSingletonCollection problem
  in
    fmap combineToSolution (solveBFS pcs) -- Find first solution

solveBFS :: [ProblemCollection] -> Maybe SolutionCollection
solveBFS pcs =
    loop (toQueue pcs)
  where
    loop :: Queue ProblemCollection -> Maybe SolutionCollection
    loop [] = Nothing -- Empty queue means we didn't manage to find solution
    loop (pc:queue) = do
      case status pc of
        AllSolved         -> return toSolutionCollection ps' -- Solution found
        NoSolution        -> loop queue        -- Unable to solve, discard
        RemainingProblems ->                   -- Keep iteratively solving
          let
            pcs: [ProblemCollection] = step pc
            queue': Queue ProblemCollection = append queue pcs
          in 
            loop queue'

step :: ProblemCollection -> [ProblemCollection]
step [] = []
step (p:ps) = 
  let
    pcs: [ProblemCollection] = tactics p  -- Possible ways to refine head
  in
    -- Propagate constraints and step other goals
    flatten . map (\pc -> step $ propagateContstraints ps (extractConstraints pc)) pcs

propagateConstraints :: ProblemCollection -> Constraints -> ProblemCollection
propagateConstraints ps constraints = fmap (addConstraints constraints) ps
```],
caption: [
    Pseudocode for BFS search
  ],
) <standardml-bfs-code>

Consider the example where we are searching for a goal ```hs ?goal :: ([a], a -> String)``` that is a pair of a list of some type and a function of that type to `String`.
Similar goals in everyday life could arise from finding a list together with a function that can map the elements to strings to print them (`show` function).

Note that in this example, we want the first member of the pair to be list, but we do not care of the types inside the list.
The only requirement is that the second member of the pair can map the same type to ```hs String```.
We have the following items in scope:
```hs
bar : Bar
mk_foo : Bar -> Foo
mk_list_foo : Foo -> [Foo]
mk_list_bar : Bar -> [Bar]
show_bar  : Bar -> String
```

To simplify the notation, we name the goals as ```hs ?<number>```, for example, ```hs ?1``` for goal 1.

First, we can split the goal of finding a pair into two subgoals: ```hs [?1 : [a], ?2 : a -> String]```.
This is the same step for BFS and DFS, as there is not much else to do with ```hs ?goal``` as there are now functions
that take us to a pair of any types except using the pair constructor.
At this point, we have two subgoals to solve
```hs
(?1 : [a], ?2 : a -> String)
```

Now we are at the point where the differences between DFS and BFS start playing out.
First, let's look at how the DFS would handle the goals.
We start by focusing on ```hs ?1```.
We can use `mk_list_foo` to transform the goal into finding something of the type ```hs Foo```.
Now we have the following solution and goals:

```hs
(mk_list_foo(?3 : Foo), ?2 : a -> String)
```

Note that although the `a` in ```hs ?s2``` has to be of type ```hs Foo```, we have not propagated this knowledge there yet as we are focusing on ```hs ?3```.
We only propagate the constraints when we discard the hole as filled.
We use `mk_foo` to create a new goal ```hs ?4 : Bar``` which we solve by providing `bar`.
Now we propagate the constraints to the remaining subgoals, ```hs ?2``` in this example.
This means that the second subgoal becomes ```hs ?2 : Foo -> String``` as shown below.

```hs
(mk_list_foo(mk_foo(?4 : Bar), ?2 : a -> String)
(mk_list_foo(mk_foo(bar)), ?2 : Foo -> String)
```
However, we cannot find anything of type ```hs Foo -> String``` so we have to revert all the way to ```hs ?1```.
This time we use `mk_list_bar` to fill ```hs ?1``` meaning that the remaining subgoal becomes ```hs ?2 : Bar -> String```.
We can fill it by providing `show_bar`.
As there are no more subgoals remaining the problem is solved with the steps shown below.

```hs
(mk_list_bar(?3 : Bar), ?2 : a -> String)
(mk_list_bar(bar), ?2 : Bar -> String)
(mk_list_bar(bar), show_bar)
```

An overview of all the steps we took can be seen in the @standardml-dfs-steps.
#figure(
sourcecode()[```hs
?goal : ([a], a -> String)
(?1 : [a], ?2 : a -> String)
(mk_list_foo(?3 : Foo), ?2 : a -> String)
(mk_list_foo(mk_foo(?4 : Bar), ?2 : a -> String)
(mk_list_foo(mk_foo(bar)), ?2 : Foo -> String) -- Revert to ?1
(mk_list_bar(?3 : Bar), ?2 : a -> String)
(mk_list_bar(bar), ?2 : Bar -> String)
(mk_list_bar(bar), show_bar)
```],
caption: [
    DFS algorithm steps
  ],
) <standardml-dfs-steps>

Now let's take a look at the algorithm that uses BFS to handle the goals.
The first iteration is the same as described above, after which we have two subgoals to fill.
```hs
(?1 : [a], ?2 : a -> String)
queue = [[?1, ?2]]
```

As we are always working on the head element of the queue, we are still working on ```hs ?1```.
Once again, we use `mk_list_foo` to transform the first subgoal to ```hs ?3 : Foo```, but this time we also insert another problem collection into the queue, where we use `mk_list_bar` instead.
We also propagate the information to other subgoals so that we constrain ```hs ?2``` to either ```hs Foo -> String``` or ```hs Bar -> String```.
```hs
(mk_list_foo(?3 : Foo), ?2 : Foo -> String)
(mk_list_bar(?4 : Bar), ?2 : Bar -> String)

queue = [[?3, ?2], [?4, ?2]]
```

In the next step, we search for something of type ```hs Foo``` for ```hs ?3``` and a function of type ```hs Foo -> String``` in ```hs ?2```.
We find `bar` for the first goal, but not anything for the second goal.
This means we discard the branch as we are not able to solve the problem collection.
Note that at this point we still have ```hs ?4``` pending, meaning we have not yet exhausted the search in the current "branch".
Reverting now means that we save some work that was guaranteed to have no effect on the overall outcome.
The search space becomes
```hs
(mk_list_foo(mk_foo(?4 : Bar)), ?2 : <impossible>) -- discarded
(mk_list_bar(?4 : Bar), ?2 : Bar -> String)

queue = [[?4, ?2]]
```
Now we focus on the other problem collection.
In this iteration, we find solutions for both of the goals.
As all the problems in the problem collection get solved, we can turn the problem collection into a solution and return it.
```hs
(mk_list_bar(?5 : Bar), ?2 : Bar -> String)
(mk_list_bar(bar), show_bar)
```

An overview of all the steps we took can be seen in @standardml-bfs-steps.
Note that from line 3 to line 5, there are two parallel branches, and the order between branches is arbitrary.
#figure(
sourcecode()[```hs
?goal : ([a], a -> String)
(?1 : [a], ?2 : a -> String)
(mk_list_foo(?3 : Foo), ?2 : Foo -> String)        -- Branch 1
(mk_list_foo(mk_foo(?4 : Bar)), ?2 : <impossible>) -- Discard branch 1
(mk_list_bar(?5 : Bar), ?2 : Bar -> String)        -- Branch 2
(mk_list_bar(bar), show_bar)
```],
caption: [
    BFS algorithm steps
  ],
) <standardml-bfs-steps>

In the example above, we see that BFS and propagating constraints to other subgoals can help us cut some search branches to speed up the search.
However, this is not always the case.
BFS is faster only if we manage to cut the proof before exhausting the search for the current goal.
In case the first goal we focus on cannot be filled, DFS is faster as it doesn't do any work on filling other goals.

=== Term search in Haskell
Wingman#cite-footnote("Hackage, Wingman plugin for Haskell Language Server", "2024-04-06", "https://hackage.haskell.org/package/hls-tactics-plugin", "https://web.archive.org/web/20240313211704/https://hackage.haskell.org/package/hls-tactics-plugin") is a plugin for Haskell Language Server that provides term search.
For term search Wingman uses library called Refinery#cite-footnote("Github Refinery repository", "2024-04-06", "https://github.com/TOTBWF/refinery", "https://web.archive.org/web/20230615122227/https://github.com/TOTBWF/refinery") that is also based on @algebraic-foundations-of-proof-refinement similarly to the Standard ML tool we described in @standardml.

As we described the core ideas in @standardml, we won't cover them here.
However, we will take a look at some implementation details.

The most interesting implementation detail for us is how BFS is achieved.
Refinery uses the interleaving of subgoals generated by each tactic to get the desired effect.
Let's look at the example to get a better idea of what is going on.
Suppose that at some point of the term search we have three pending subgoals: `[`#text(red)[`?1`]`, ?2, ?3]` and we have some tactic that produces two new subgoals `[`#text(blue)[`?4`]`, `#text(blue)[`?5`]`]` when refining #text(red)[`?1`].
The DFS way of handling it would be
#block()[
`[`#text(red)[`?1`]`, ?2, ?3] -> tactic -> [`#text(blue)[`?4`]`, `#text(blue)[`?5`]`, ?2, ?3]`
]
However, with interleaving, the goals are ordered in the following way:
#block()[
`[`#text(red)[`?1`]`, ?2, ?3] -> tactic -> [?2, `#text(blue)[`?4`]`, ?3, `#text(blue)[`?5`]`]`
]
Note that there is also a way to insert the new goals at the back of the goals list, which is the BFS way.
#block()[
`[`#text(red)[`?1`]`, ?2, ?3] -> tactic -> [?2, ?3, `#text(blue)[`?4`]`, `#text(blue)[`?5`]`]`
]
However, in Refinery, they have decided to go with interleaving, as it works well with tactics that produce infinite amounts of new holes due to not making any new process.
Note that this works especially well because of the lazy evaluation in Haskell.
In the case of eager evaluation, the execution would still halt on producing all the subgoals, so interlining would now have an effect.


=== Term search in Idris2
Idris2 (@idris2-design-and-implementation) is a dependently typed programming language that has term search built into its compiler.
Internally, the compiler makes use of a small language they call TT.
TT is a dependently-typed λ-calculus with inductive families and pattern-matching definitions.
The language is kept as small as reasonably possible to make working with it easier.

As the term search algorithm also works on TT, we will take a closer look at it.
More precisely, we will look at what they call $"TT"_"dev"$, which is TT extended with hole and guess bindings.
The guess binding is similar to a let binding, but without any reduction rules for guess bindings.
Using binders to represent holes is useful in a dependently-typed setting since one value may determine another.
Attaching a guess (a generated term) to a binder ensures that instantiating one such variable also instantiates all of its dependencies.

$"TT"_"dev"$ consists of terms, bindings and constants as shown in @idris-tt-syntax.
#figure(
sourcecode(numbering: none)[```
Terms, t ::= c (constant)
    | x (variable)
    | b. t (binding)
    | t t (application)
    | T (type constructor)
    | D (data constructor)

Binders, b ::= λ x : t (abstraction)
    | let x -> t : t (let binding)
    | ∀x : t (function space)
    | ?x : t (hole binding)
    | ?x ≈ t : t (guess)

Constants, c ::= Type (type universes)
    | i (integer literal)
    | str (string literal)
```],
caption: [
    $"TT"_"dev"$ syntax, following @idris2-design-and-implementation[Fig. 1 & Fig. 6] / © Cambridge University Press 2013
  ],
) <idris-tt-syntax>

Idris2 makes use of priority queue of holes and guess binders to keep track of subgoals to fill.
The goal is considered filled once the queue becomes empty.

In the implementation, the proof state is captured in an elaboration monad, which is a state monad with exceptions.
The general flow of the algorithm is the following:
1. Create a new proof state.
2. Run a series of tactics to build up the term.
3. Recheck the generated term.

The proof state contains the context of the problem (local and global bindings), the proof term, unsolved unification problems, and the holes queue.
The main parts of the state that change during the proof search are the holes queue and sometimes the unsolved unification problems.
The holes queue changes as we try to empty it by filling all the holes.
Unsolved unification problems only change if new information about unification becomes available when instantiating terms in the proof search.
For example, we may have a unification problem `Unify(f x, Int)` that cannot be solved without new information.
Only when we provide some concrete `f` or `x` the problem can be solved further.

Tactics in Idris2 operate on the sub-goal given by the hole at the head of the hole queue in the proof state.
All tactics run relative to context, which contains all the bindings in scope.
They take a term (that is, hole or guess binding) and produce a new term that is of suitable type.
Tactics are also allowed to have side effects that modify the proof state.

Next, let's take a look at the primitive building blocks that are used by tactics to create and fill holes.

Operation `claim` is used to create new holes in the context of a current hole.
The operation creates a new hole binding to the head of the holes queue.
Note that the binding is what associates the generated hole with the current hole.

Operation `fill` is used to fill a goal with value. 
Given the value `v`, the operation attempts to solve the hole by creating a guess binder with `v`.
It also tries to fill other goals by attempting to unify `v` with the types of holes.
Note that the `fill` operation does not destroy the hole yet, as the guess binding it created is allowed to have more holes in it.

To destroy holes, the operation `solve` is used.
It operates on guess bindings and checks if they contain any more holes.
If they don't, then the hole is destroyed and substituted with the value from the guess binder.

The two-step process, with `fill` followed by `solve`, allows the elaborator to work safely with incomplete terms.
This way, incomplete terms do not affect other holes (by adding extra constraints) until we know we can solve them.
Once a term is complete in a guess binding, it may be substituted into the scope of the binding safely.
In each of these tactics, if any step fails, or the term in focus does not solve the problem, the entire tactic fails.
This means that it roughly follows the DFS approach described in @standardml.


=== Term search in Elm with Smyth
Smyth#cite-footnote("Smyth", "2024-04-06", "https://uchicago-pl.github.io/smyth/", "https://web.archive.org/web/20231005015038/https://uchicago-pl.github.io/smyth/") is a system for program sketching in a typed functional language, approximately Elm.
In @smyth, they describe that it uses evaluation of ordinary assertions that give rise to input-output examples, which are then used to guide the search to complete the holes.
Symth uses type and example directed synthesis as opposed to other tools in Agda only using type guided search for terms.
The general idea is to search for terms that satisfy the goal type as well as example outputs for the term given in assertions.
It is also based on a DFS, but is optimized for maximal use memoization.
The idea is to maximize the amount of terms that have same typing environment and can therefore be reused.
This is done by factorizing the terms into smaller terms that carry less context with them.
Smyth has many other optimizations, but they focus on using the information from examples and are therefore not interesting for us as they focus on optimizing the handling of data provided by examples.

== Program synthesis in Rust
RusSol is a proof-of-concept tool to synthesize Rust programs from both function declarations and pre- and post-conditions.
It is based on separation logic as described in @rust-program-synthesis, and it is the first synthesizer for Rust code from functional correctness specifications.
Internally, it uses SuSLik’s @suslik general-purpose proof search framework.
RusSol itself is implemented as an extension to `rustc`, the official rust compiler.
It has a separate command-line tool, but internally, it reuses many parts of the compiler.
Although the main use case for RusSol is quite different from our use case, they share a lot of common ground.

The idea of the tool is to specify the function declaration as follows and then run the tool on it to synthesize the program to replace the ```rust todo!()``` macro on line 5 in @russol-input.

#figure(
sourcecode(highlighted: (5,))[```rs
#[requires(x < 100)]
#[ensures(y && result == Option::Some(x))]
#[ensures(!y && result == Option::None)]
fn foo(x: &i32, y: bool) -> Option<i32> {
  todo!()
}
```],
caption: [
    RusSol input program
  ],
) <russol-input>
From the preconditions (`requires` macro) and post-conditions (`ensures` macro), it is able to synthesize the body of the function.
For the example in @russol-input, the output is shown in @russol-output.
#figure(
sourcecode(numbering: none)[```rs
match y {
  true => Some(x),
  false => None
}
```],
caption: [
    RusSol output for `todo!()` macro
  ],
) <russol-output>
It can also insert ```rust unreachable!()``` macros in places that are never reached during program execution.

RusSol works at the HIR level of abstraction.
It translates the information from HIR to separation logic rules that SuSLik can understand and feeds them into it.
After getting a successful response, it turns the response back into Rust code, as shown in @russol-workflow.
#figure(
  image("fig/russol-suslik.png", width: 100%),
  caption: [
    "RusSol workflow" by @rust-program-synthesis / #link("https://creativecommons.org/licenses/by/4.0/ ")[CC BY 4.0]
  ],
) <russol-workflow>

All the programs synthesized by RusSol are guaranteed to be correct by construction.
This is achieved by extracting the programs from separation logic derivations.
However, in @rust-program-synthesis, they noted that they cannot prove the correctness of separation logic rules for Rust as, at this point, Rust lacks formal specification.
Nevertheless, the tool was tested on 100 different crates and managed to always produce a valid code.

As the tool uses an external engine to synthesize the programs, we will not dive into its inner workings.
However, we will take a look at the notes by the authors of @rust-program-synthesis, as they are very relevant to us.

The authors found that quite often the types are descriptive enough to produce useful programs, and the pre- and post-conditions are not required.
This aligns with our intuition that synthesizing terms from types can be useful in practice.

The authors of RusSol pointed out the main limitations of the tool, which are:
1. It does not support traits.
2. It does not support conditionals as it lacks branch abduction.
3. It does not synthesize arithmetic expressions.
4. It does not support ```rust unsafe``` code.

They also noted that the first three of them can be solved with some extra engineering effort, but the last one requires more fundamental changes to the tool.

From the benchmarks on the top 100 crates on crates.io, it was measured that it takes about 0.5s on average to synthesize non-primitive expressions.
Quite often, the synthesis time was 2-3s and sometimes reached as high as 18.3s.
This is fast enough to use for filling holes, but too slow to use for autocompletion.

== Autocompletion
Autocompletion is predicting of what the user is typing and then suggesting the predictions to user.
In case of programming the suggestions are usually derived form context and may be just a word from current buffer or maybe functions reachable in the current context.
It is nowadays considered one of the basic features that any integrated development environment (IDE) has built in.

We will explore the LSP protocol in @lsp-protocol to have a basic understanding of the constraints and features of the framework we are working in.
This is essential to later understand some of our design choices for implementation, as described in @design.

Let's take a look at some of the popular autocompletion tools and their autocompletion-related features to get some intuition of what the common approach is for implementing them.
We will be mostly looking at the kind of semantic information the tools used to provide suggestions.

==== Clangd
Clangd#cite-footnote("Clangd, what is clangd?", "2024-04-06", "https://clangd.llvm.org/", "https://web.archive.org/web/20240324053051/https://clangd.llvm.org/") is a popular autocompletion tool for C/C++.
It is a language server extension to the clang compiler and, therefore, can be used in many editors.
It suggests functions, methods, variables, etc. are available in the context, and it can handle some mistyping and abbreviations of some words.
For example, using a snake case instead of a camel case still yields suggestions.

For method calls, it does understand the receiver type and only suggests methods and fields that exist for the type.
However, it does not try to infer the expected type of expression that is being completed and therefore is unable to prioritize methods based on that.
All in all, it serves as a great example of an autocompletion tool that has a semantic understanding of the program but does not provide any functionality beyond the basics.

==== Pyright
Pyright#cite-footnote("GitHub pyright repository", "2024-04-06", "https://github.com/microsoft/pyright", "https://web.archive.org/web/20240403213050/https://github.com/microsoft/pyright") is a popular language server for Python.
It suggests all the items that are available in scope for autocompletion, and it also suggests the methods and fields that are on the receiver type.

While it tries to provide more advanced features than `clangd`, it does not get much further due to Python being a dynamically typed language.
There simply isn't that much information available before running the program.
This seems to be a general limitation of all Python autocompletion tools.

==== Intellij
Intellij#cite-footnote("IntelliJ IDEA", "2024-04-06", "https://www.jetbrains.com/idea/", "https://web.archive.org/web/20240409180113/https://www.jetbrains.com/idea/") is an IDE by JetBrains for Java.
Similarly to all other JetBrains products, it does not use LSP but rather has all the tooling built into the product.
It provides the completion of all the items in scope as well as the methods and fields of receiver type.
They call them "basic completions".
The tool also has an understanding of expected type, so it attempts to order the suggestions based on their types.
This means that suggestions with expected type appear first in the list.

In addition to "basic completion", they provide "type-matching completions", which are very similar to basic completion but filter out all the results that do not have matching types.
There is also what they call "chain completion", which expands the list to also suggest chained method calls.
Together with filtering out only matching types, it gives similar results to what term search provides.
However, as this is implemented differently, its depth is limited to two, which makes it less useful.
It also doesn't attempt to automatically fill all the arguments, so it works best with functions that take no arguments.
For Java, it is quite useful nonetheless, as there are a lot of getter functions.

In some sense, the depth limit of two (or three together with the receiver type) is mainly a technical limitation, but it is also caused by Java using interfaces in a different way than what Rust does with traits.
Interfaces in Java are meant to hide the internal representation of classes, which in some cases limits what we can provide just based on types.
For example, if we are expected to give something that implements `List`, we cannot really prefer `ArrayList` to `LinkedList` just based on types.
More common usage of static dispatch in Rust means that we more often know the concrete type and therefore can also provide more accurate suggestions based on it.
In Java, there is often not enough information to suggest longer chains, as there are likely too many irrelevant suggestions.

==== Rust-analyzer <rust-analyzer>
Rust-analyzer#cite-footnote("rust-analyzer", "2024-04-06", "https://rust-analyzer.github.io/", "https://web.archive.org/web/20240406183402/https://rust-analyzer.github.io/") is an implementation of the Language Server Protocol for the Rust programming language. 
It provides features like completion and go-to definition/references, smart refactoring, etc.
This is also the tool we are extending with term search functionality.

Rust-analyzer provides all the "basic completions" that IntelliJ provides and also supports ordering suggestions by type.
However, it does not support method chains, so in that regard, it is less powerful than IntelliJ for Java.
Filtering by type is also not part of it, but as it gathers all the information to do it, it can be implemented rather trivially.

Other than autocompletion, it does have an interesting concept of typed holes.
They are `_` (underscore) characters at expression positions that cause the program to be rejected by the compiler.
Rust-analyzer treats them as holes in the program that are supposed to become terms of the correct type to make the program valid.
Based on that concept, it suggests filling them with variables in scope, which is very similar to what term search does.
However, it only suggests trivial ways of filling holes, so we are looking to improve on it a lot.

=== Language Server Protocol <lsp-protocol>
Implementing autocompletion for every language and for every IDE results in a $O(N * M)$ complexity where N is the number of languages supported and M is the number of IDEs supported.
In other words, one would have to write a tool for every language-IDE pair.
This problem is very similar to the problem of compiler design with N languages and M target architectures.
The problem can be reduced from $O(N*M)$ to $O(N+M)$ by separating the compiler to the front- and backend @compiler-design[Section 1.3].
The idea is that there is a unique front end for every language that lowers the language-specific constructs to an intermediate representation that is a common interface for all of them.
To get machine code out of the intermediate representation, there is also a unique back end for every target architecture.

Similar ideas can also be used in building language tools.
Language server protocol (LSP) has been invented to do exactly that.
The Language Server Protocol#cite-footnote("Language Server Protocol", "2024-04-06", "https://microsoft.github.io/language-server-protocol/", "https://web.archive.org/web/20240406114122/https://microsoft.github.io/language-server-protocol/") (LSP) is an open, JSON-RPC-based#cite-footnote("JSON-RPC 2.0 Specification", "2024-04-06", "https://www.jsonrpc.org/specification", "https://web.archive.org/web/20240409000305/https://www.jsonrpc.org/specification") protocol for use between editors and servers that provide language-specific tools for a programming language.
The protocol takes the position of intermediate representation: frontends are the LSP clients in IDEs, and the backends are LSP servers.
We will refer to LSP clients as just clients and LSP servers as just servers.
As the protocol is standardized, every client knows how to work with any server.
LSP was first introduced to the public in 2016, and now many#cite-footnote("The Language Server Protocol implementations: Tools supporting the LSP", "2024-04-06", "https://microsoft.github.io/language-server-protocol/implementors/tools/", "https://web.archive.org/web/20240226024547/https://microsoft.github.io/language-server-protocol/implementors/tools/") modern IDEs support it.

Some of the common functionalities provided by LSP servers include  @editing-support-for-languages-lsp:
- Go to definition / reference
- Hover
- Diagnostics (warnings / errors)
- Autocompletion
- Formatting
- Refactoring routines (extract function, etc.)
- Semantic syntax highlighting
Note that the functionalities are optional, and the language server can choose which to provide.

The high-level communication between client and server is shown in @lsp-data-flow.
The idea is that when the programmer works in the IDE, the client sends all text edits to the server.
The server can then process the updates and send new autocompletion suggestion, syntax highlighting and diagnostics back to the client so that it can update the information in the IDE.
#figure(
  image("fig/lsp_data_flow.svg", width: 100%),
  caption: [
    LSP client notifies the server from changes and user requests.
    The server responds by providing different functionalities to the client.
  ],
) <lsp-data-flow>
The important thing to note here is that the client starts the server the first time it requires data from it.
After that, the server runs as a daemon process, usually until the editor is closed or until the client commands it to shut down.
As it doesn't get restarted very often, it can keep the state in memory, which allows responding to client events faster.
It is quite common that the server does semantic analysis fully only once and later only runs the analysis again for files that have changed.
Caching the state and incrementally updating it is quite important, as the full analysis can take up to a considerable amount of time, which is not an acceptable latency for autocompletion nor for other operations servers provide.
Caching the abstract syntax tree is a common performance optimization strategy for servers @editing-support-for-languages-lsp.

== Machine learning based autocompletions <machine-learning>
In this chapter, we will take a look at machine-learning-based autocompletion tools.
As this is a very active field of development and we are not competing against, we will not dive into how well the models perform but rather look at what the models generally do.
The main focus is to see how they differ from the analytical approach we are taking with term search.

One of the use cases for machine learning is to order the suggestions @code-prediction-trees-transformers.
Using a model for ordering the suggestions is especially useful in dynamically typed languages as it is otherwise rather hard to order suggestions.
Although the Rust language has a strong type system, we still suffer from prioritizing different terms that have the same type.

In addition to ordering the analytically created suggestions, machine learning models can be used to generate code itself.
Such models generate code in a variety of programming languages (@pre-trained-llm-code-gen).
The general flow is that first the user writes the function signature and maybe some human-readable documentation, and then prompts the model to generate the body of the function.
This is very different from ordering suggestions, as the suggested code usually has many tokens, whereas the classical approach is usually limited to one or sometimes very few tokens.
This is also different from what we are doing with the term search: we only try to produce code that contributes towards the parent term of the correct type.
However, language models can also generate code where term search fails.
Let's look at the example for the `ripgrep`#cite-footnote("GitHub ripgrep repository", "2024-04-06", "https://github.com/BurntSushi/ripgrep/blob/6ebebb2aaa9991694aed10b944cf2e8196811e1c/crates/core/flags/hiargs.rs#L584", "https://web.archive.org/web/20240410184204/https://github.com/BurntSushi/ripgrep/blob/6ebebb2aaa9991694aed10b944cf2e8196811e1c/crates/core/flags/hiargs.rs#L584") crate shown in @rust-builder.
#figure(
sourcecode()[```rs
// Inside `printer_json` at `/crates/core/flags/hiargs.rs`

fn printer_json<W: std::io::Write>(&self, wtr: W) -> JSON<W> {
    JSONBuilder::new()                // () -> JSONBuilder
        .pretty(false)                // JSONBuilder -> JSONBuilder
        .max_matches(self.max_count)  // JSONBuilder -> JSONBuilder
        .always_begin_end(false)      // JSONBuilder -> JSONBuilder
        .build(wtr)                   // JSONBuilder -> JSON
}
```],
caption: [
    Builder pattern in Rust.
    Setter methods return a value of the receiver type.
  ],
) <rust-builder>
The type of term only changes on the first and last lines of the function body.
As the lines in the middle do not affect the type of the builder in any way, there is also no way for the term search to generate them.
Machine learning models, however, are not affected by this, as it may be possible to derive those lines from the function documentation, name, or rest of the context.

Although machine learning models are able to generate more complex code, they also have the downside of having lots of uncertainty in them.
It is very hard, if not impossible, for any human to understand what the outputs are for any given input.
In the context of code generation for autocompletion, this results in unexpected suggestions that may even not compile.
These issues are usually addressed by filtering out syntactically invalid responses or working at the level of an abstract syntax tree, as they did in @code-prediction-trees-transformers.
However, neither of those accounts for type nor borrow checking, which means that invalid programs can still be occasionally suggested.


= Term search design <design>
Before diving into the technical aspects of term search implementation, we will first explore it by giving
examples of its usages in `rust-analyzer`. 
We will first take a look at using it for filling "holes" in the program and later dive into using it for autocompletion.

== Filling holes
Filling holes is a common use case for term search, as we have found in @term-search.
Timing constraints for it are not as strict as for autocompletion, yet the user certainly doesn't want to wait for a considerable amount of time.

One example of a hole in Rust program is the ```rust todo!()``` macro.
It is a "hole", as it denotes that there should be a program in the future, but there isn't now.
These holes can be filled using a term search to search for programs that fit in the hole.
All the programs generated by term search are valid programs, meaning that they compile.

Example usages can be found in @rust-filling-todo:
#figure(
sourcecode()[```rs
fn main() {
    let a: i32 = 0;  // Suppose we have a variable a in scope
    let b: i32 = todo!();  // Term search finds `a`
    let c: Option<i32> = todo!();  // Finds `Some(a)`, `Some(b)` and `None`
}
```],
caption: [
    Filling `todo!()` holes
  ],
) <rust-filling-todo>

In addition to `todo!()` macro holes, `rust-analyzer` has a concept of typed holes, as we described in @rust-analyzer.
From a term search perspective, they work in the same way as ```rust todo!()``` macros: term search needs to come up with a term of some type to fill them.
The same example with typed holed instead of ```rust todo!()``` macros can be found in @rust-filling-typed-hole.
#figure(
sourcecode()[```rs
fn main() {
    let a: i32 = 0;  // Suppose we have a variable a in scope
    let b: i32 = _;  // Term search finds `a`
    let c: Option<i32> = _;  // Finds `Some(a)`, `Some(b)` and `None`
}
```],
caption: [
    Filling typed holes (`_`)
  ],
) <rust-filling-typed-hole>


== Term search for autocompletion
In addition to filling holes, term search can be used to give users "smarter" autocompletion suggestions as they are typing.
The general idea is the same as for filling holes.
We start by attempting to infer the expected type at the cursor.
If we manage to infer the type, then we run the term search in order to get the suggestions, which we can then show to the user.

The main difference between using term search for autocompletion and using it to fill holes is that we have decided to disable borrow checking when generating suggestions for autocompletion.
This means that not all the suggestions are valid programs and may need some modifications by the user.

The rationale for it comes from both the technical limitations of the tool and different expectations from the user.
The main technical limitation is that borrow checking happens in the MIR layer of abstraction, and `rust-analyzer` (nor `rustc`) does not support lowering partial (the user is still typing) programs to MIR.
This means that borrow checking is not really possible without big modifications to the algorithm.
That, however, is out of the scope of this thesis.

In addition to technical limitations, there is also some motivation from a user perspective for the tool to give suggestions that do not borrow check.
It is very common that the programmer has to restructure the program to satisfy the borrow checker @usability-of-ownership.
The simplest case for it is to either move some lines around in the function or to add ```rust .clone()``` to avoid moving the value.
For example, consider @rust-autocompletion with the cursor at "```rust |```":
#figure(
sourcecode(highlighted: (10,))[```rs
/// A function that takes an argument by value
fn foo(x: String) { todo!() }
/// Another function that takes an argument by value
fn bar(x: String) { todo!() }

fn main() {
  let my_string = String::new();

  foo(my_string);
  bar(my_s|); // cursor here at `|`
}
```],
caption: [
    Autocompletion of moved values
  ],
) <rust-autocompletion>
The user wants to also pass `my_string` to ```rust bar(...)```, but this does not satisfy the borrow checking rules as the value was moved to ```rust foo(...)``` on the previous line.
The simplest fix for it is to change the previous line to ```rust foo(my_string.clone())``` so that the value is not moved.
This, however, can only be done by the programmer, as there are other ways to solve it, for example, by making the functions take the reference instead of the value.
As also described in @usability-of-ownership, a common way to handle borrow checker errors is to write the code first and then fix the errors as they come up.
Inspired by this, we believe that it is better to suggest items that make the program do not borrow check than not suggest them at all.
If we only suggest items that borrow check the ```rust bar(my_string)``` function call would be ruled out, as there is no way to call it without modifying the rest of the program.


== Implementation
We have implemented term search as an addition to `rust-analyzer`, the official LSP server for the Rust language.
To have a better understanding of the context we are working in, we will first describe the main operations that happen in `rust-analyzer` in order to provide autocompletion or code actions (filling holes in our use case).

When the LSP server is started, `rust-analyzer` first indexes the whole project, including its dependencies as well as the standard library.
This is a rather time-consuming operation.
During indexing, `rust-analyzer` lexes and parses all source files and lowers most of them to High-Level Intermediate Representation (HIR).
Lowering to HIR is done to build up a symbol table, which is a table that has knowledge of all symbols (identifiers) in the project.
This includes, but is not limited to, functions, traits, modules, ADTs, etc.
Lowering to HIR is done lazily.
For example, many function bodies are usually not lowered at this stage.
One limitation of the `rust-analyzer` as of now is that it doesn't properly handle lifetimes.
Explicit lifetimes are all mapped to ```rust 'static``` lifetimes, and implicit lifetime bounds are ignored.
This also limits our possibilities to do borrow checking as there simply isn't enough data available in the `rust-analyzer` yet.
With the symbol table built up, `rust-analyzer` is ready to accept client requests.

Now an autocompletion request can be sent.
Upon receiving a request that contains the cursor location in source code, `rust-analyzer` finds the corresponding syntax node.
If it is in a function body that has not yet been lowered, the lowering is done.
Note that the lowering is always cached so that subsequent calls can be looked up from the table.
With all the lowering done, `rust-analyzer` builds up the context of the autocompletion.
The context contains location in the abstract syntax tree, all the items in scope, package configuration (e.g. is nightly enabled) etc.
If the expected type of the item under completion can be inferred, it is also available in the context.
From the context different completion providers (functions) suggest possible completions that are all accumulated to a list.
To add the term-search-based autocompletion, we introduce a new provider that takes in a context and produces a list of completion suggestions.
Once the list is complete, it is mapped to the LSP protocol and sent back to the client.

=== Term search <term-search-iters>
The main implementation of term search is done at the HIR level of abstraction, and borrow checking queries are made at the MIR level of abstraction.
The term search entry point can be found in `crates/hir/src/term_search.rs` and is named `term_search`.
The most important inputs to the term search are the scope of the program we are performing the search at and the target type.

To better understand why the main algorithm is based around bidirectional BFS, we will discuss three iterations of the algorithm.
First, we start with an algorithm that quite closely follows the algorithm we described in @agsy.
Then we will see how we managed to achieve better results by using BFS instead of DFS, as suggested in @standardml.
At last, we will see how the algorithm can benefit from bidirectional search.

=== First iteration: DFS <first-iter-dfs>
The first iteration of the algorithm follows the algorithm described in @agsy.
The implementation for it is quite short, as the DFS method seems to naturally follow the DFS, as pointed out in @standardml.
However, since our implementation does not use any caching, it is very slow.
Because of the poor performance, we had to limit the search depth to 2, as bigger depth caused the algorithm to run for a considerable amount of time.
The performance can be improved by caching some of the found terms, but doing it efficiently is rather hard.

Caching the result means that once we have managed to produce a term of type `T`, we want to store it in a lookup table so that we won't have to search for it again.
Storing the type the first time we find it is rather trivial, but it's not very efficient.
The issue arises from the fact that there are no guarantees that the first term we come up with is the simplest.
Consider the example of producing something of the type ```rust Option<i32>```.
We as humans know that the easiest way to produce a term of that type is to use the ```rust None``` constructor that takes no arguments.
The algorithm, however, might first take the branch of using the ```rust Some(...)``` constructor.
Now we have to also recurse to find something of type ```rust i32```, and potentially iterate again and again if we do not have anything suitable in scope.
Even worse, we might end up not finding anything suitable after fully traversing the tree we got from using the ```rust Some(...)``` constructor.
Now we have to also check the ```rust None``` subtree, which means that we only benefit from the cache if we want to search for ```rust Option<i32>``` again.

This is not a problem if we want to retrieve all possible terms for the target type, however, that is not always what we want to do.
We found that for bigger terms, it is better to produce a term with new holes in it, even when we have solutions for them, just to keep the number of suggestions low.
Consider the following example:

#sourcecode(numbering: none)[```rs
let var: (bool, bool) = todo!();
```]

If we give the user back all possible terms, then the user has to choose between the following options:
#sourcecode(numbering: none)[```rs
(false, false)
(false, true)
(true, false)
(true, true)
```]
However, we can simplify it by only suggesting the use of a tuple constructor with two new holes in it.
#sourcecode(numbering: none)[```rs
(todo!(), todo!())
```]
If there are only a few possibilities to come up with a solution, then showing them all isn't really a problem.
However, it is quite common for type constructors or functions to take multiple arguments.
As the number of terms is increases exponentially relative to the number of arguments a function/type constructor takes, the number of suggestions grows very fast.
As a result, quite often, all the results don't even fit on the screen.
In @second-iter-bfs, we will introduce an algorithm to handle this case.
For now, it is sufficient to acknowledge that fully traversing the search space to produce all possible terms is not the desired approach, and there is some motivation to cache the easy work to avoid the hard work, not vice versa.
Branch costs suggested in @mimer can potentially improve this, but the issue still remains as this is simply a heuristic.

Another observation from implementing the DFS algorithm is that, while most of the algorithm looked very elegant, the "struct projection" tactic described in @tactic-struct-projection was rather awkward to implement.
The issue arose with the projections having to include all the fields from the parent struct as well as from the child struct.
Including only the child "leaf" fields is very elegant with DFS, but also including the intermediate fields caused some extra boilerplate.

Similar issues arose when we wanted to speed up the algorithm by running some tactics, for example, the "impl method" only on types that we have not yet ran it on.
Doing it with DFS is definitely possible, but it doesn't fit the algorithm conveniently.
As there were many issues with optimizing the DFS approach, we decided to not improve it further and turn to a BFS-based algorithm instead.


=== Second iteration: BFS <second-iter-bfs>
The second iteration of our algorithm was based on BFS, as suggested in @algebraic-foundations-of-proof-refinement.
However, it differs from it by doing the search in the opposite direction.

To not confuse the directions, we use _forward_ when we are constructing terms from what we have (working towards the goal) and _backward_ when we work backwards from the goal.
Forward is also what we, as humans, generally use when writing programs.
For example, we usually write ```rust x.foo().bar()``` left to right (forwards from arguments to goal) instead of right to left (backwards from goal to arguments).

The algorithm in @algebraic-foundations-of-proof-refinement starts from the target type and starts working backwards from it towards what we already have.
For example, if we have a function in scope that takes us to the goal, we create new goals for all the arguments of the function, therefore we move backwards from the return type towards the arguments.
Our algorithm, however, works in the forward direction, meaning that we start from what we have in scope.
We try to apply all the functions, etc. to then build new types from what we have and hopefully, at some point, arrive at the target type.

In @graph-searching, they argue that taking the forward (bottom-up) approach will yield speedups when the active frontier is a substantial fraction of the total graph.
We believe that this might be the case for term search, as there are many ways to build new types available (functions/type constructors/methods).
Going in the forward direction, all the terms we create are well-formed and do not have holes in them.
This means that we do not need problem collections, as there are never multiple subproblems pending that have to all be solved for some term to be well-formed.
As there is a potential speedup and the implementation seems to be easier, we decided to experiment with using the forward approach.

Going in the "forward" direction also makes writing some of the tactics easier.
Consider the example of struct projections.
In the backward direction, we would start with the struct field and then later search if we had the struct available.
This works, but it is rather hard to understand, as we usually write code for projections in the forward direction.
With BFS going in the forward direction, we can just visit all the fields of struct types in every iteration, which roughly follows how we usually write code.
The issue of awkward handling of fields together with their fields also goes away, as we can consider only one level of fields in every iteration.
With multiple iterations, we manage to cover fields of nested structs without needing any boilerplate.

In this iteration, we also introduce the cache to the algorithm.
The idea of the cache is to keep track of types we have reached so that we could query for terms of that type in $O(1)$ time complexity.
Since in practice we also care about terms that unify with the type, we get the complexity of $O(n)$ where $n$ is a number of types in the cache.
This is still a lot faster than traversing the tree, as iterating the entries in the map is a quite cheap operation.
With this kind of graph, we managed to increase the search depth to 3-4, depending on the size of the project.

In the DFS approach without cache, the main limitation was time complexity, but now the limitation is memory complexity.
The issue is producing too many terms for a type.
In @first-iter-dfs, we discussed that there are often too many terms to present for the user.
However, now we find that there are also too many terms to keep in memory due to their exponential growth as the depth increases.
Luckily, the idea of suggesting user terms that have new holes in them also reduces the memory complexity a lot.

To avoid producing too many terms we cache terms using enum shown in @rust-alternative-exprs.
#figure(
sourcecode()[```rs
type Cache = Map<Type, AlternativeExprs>;

enum AlternativeExprs {
    /// There are few exprs, so we keep track of them all
    Few(Set<Expr>),
    /// There are too many exprs to keep track of
    Many,
}
```],
caption: [
    Cache data structure for term search
  ],
) <rust-alternative-exprs>
The idea is that if there are only a few terms of a given type, we keep them all so that we can provide the full term to the user.
However, if there are too many of them to keep track of, we just remember that we can come up with a term for a given type, but we won't store the terms themselves.
The cases of ```rust Many``` later become the holes in the generated term.

In addition to decreasing memory complexity, this also reduces time complexity a lot.
Now we do not have to construct the terms if we know that there are already many of them.
This can be achieved quite elegantly by using iterators in Rust.
Iterators in Rust are lazy, meaning that they only do work if we consume them.
In our case, consuming the iterator is extending the ```rust AlternativeExprs``` in the cache.
However, if we are already in many cases, we can throw away the iterator without performing any computation.
This speeds up the algorithm a lot, so now we can raise the depth of search to 10+ with it still outperforming the previous algorithms on a timescale.

The algorithm itself is quite simple.
The pseudocode for it can be seen in @rust-bfs-pseudocode.
We start by gathering all the items in scope to `defs`.
These items include local values ans constants, as well as all visible functions, type constructors, etc.
Next, we initialize the lookup table with the desired _many threshold_ for the alternative expressions shown in @rust-alternative-exprs.
The lookup table owns the cache, the state of the algorithm and some other values for optimizations.
We will discuss the exact functionalities of the lookup table in @lookup-table.

Before entering the main loop, we populate the lookup table by running a tactic called `trivial`.
Essentially, it attempts to fulfill the goal by trying the variables we have in scope.
More information about the `trivial` tactic can be found at @tactic-trivial.
All the terms it produces get added to the lookup table and can be later used in other tactics.
After that, we iteratively expand the search space by attempting different tactics until we have exceeded the preconfigured search depth.
During every iteration, we sequentially attempt different tactics.
All tactics build new types from existing types (type constructors, functions, methods, etc.) and are described in @tactics.
The search space is expanded by adding new types to the lookup table.
An example of it can be seen in @term-search-state-expansion.
We keep iterating after finding the first match, as there may be many terms of the given type.
Otherwise, we would never get suggestions for ```rust Option::Some(..)```, as ```rust Option::None``` usually comes first as it has fewer arguments.
In the end, we filter out solutions that do not take us closer to the goal.

#figure(
sourcecode()[```rs
pub fn term_search(ctx: &TermSearchCtx) -> Vec<Expr> {
    let mut defs = ctx.scope.process_all_names(...);
    let mut lookup = LookupTable::new(ctx.many_threshold);

    // Try trivial tactic first, also populates lookup table
    let mut solutions: HashSet<Expr> = 
        tactics::trivial(ctx, &defs, &mut lookup).collect();

    for _ in 0..ctx.config.depth {
        lookup.new_round();

        solutions.extend(tactics::type_constructor(ctx, &defs, &mut lookup));
        solutions.extend(tactics::free_function(ctx, &defs, &mut lookup));
        solutions.extend(tactics::impl_method(ctx, &defs, &mut lookup));
        solutions.extend(tactics::struct_projection(ctx, &defs, &mut lookup));
        solutions.extend(tactics::impl_static_method(ctx, &defs, &mut lookup));
    }

    solutions.into_iter().filter(|it| !it.is_many()).collect()
}
```],
caption: [
    Bottom up term search pseudocode
  ],
) <rust-bfs-pseudocode>

As we can see from the @rust-bfs-pseudocode, we start with what we have (locals, constants, and statics) and work towards the target type.
This is in the opposite direction compared to the tools we have looked at previously.
To better understand how the search space is expanded, let us look at @term-search-state-expansion.

#figure(
  image("fig/state_expansion.svg", width: 60%),
  caption: [
    Iterative term search state expansion.
    We start with terms of types A and B.
    With every iteration we keep the terms from previous iteration and add new terms if possible.
  ],
) <term-search-state-expansion>
We start with variables `a` of type `A` and `b` of type `B`.
In the first iteration, we are able to use the function $f: A -> C$ on `a` and get something of the type `C`.
in the iteration after that, we are able to use $g: C times B -> D$ and produce something of type `D`.

Once we have reached the maximum depth, we take all the elements that unify with the goal type and return all paths that take us to the goal type.

==== Lookup table <lookup-table>
The main task of the lookup table throughout the algorithm is to keep track of the state.
The state consists of the following components:
1. _Terms reached_ (grouped by type)
2. _New types reached_ (since last iteration)
3. _Definitions used_ and _definitions exhausted_ (for example, functions applied)
4. _Types wishlist_ (types that have been queried, but not reached)

_Terms reached_ keeps track of the search space we have already covered (visited types) and allows querying terms them in $O(1)$ complexity for exact type and $O(n)$ complexity for types that unify.
It is important to note that it also performs the transformation of taking a reference if we query for a reference type.
This is only to keep the implementation simple and the memory footprint low.
Otherwise, having a separate tactic for taking a reference of this type would be preferred.

_New types reached_ keeps track of new types added to _terms reached_ so that we can iterate only over them in some tactics to speed up the execution.

_Definitions used_ serves also only purpose for speeding up the algorithm by avoiding definitions that have already been used.

_Types wishlist_ keeps track of all the types we have tried to look up from terms reached but not found.
They are used in the static method tactic (see @tactic-static-method) to only search for static methods on types we haven't reached yet.
This is another optimization for speed described in the @tactic-static-method.

The main downside of the lookup table implementation we have is that it poorly handles types that take generics.
We only store types that are normalized, meaning that we have substituted the generic parameter with some concrete type.
In the case of generics, it often means that the lookup table starts growing exponentially.
Consider the example of using the `Option` type.
#sourcecode()[```rs
Some(T) | None
Some(Some(T)) | Some(None) | Some(T) | None
Some(Some(Some(T))) | Some(Some(None)) | Some(Some(T)) | Some(None) | Some(T) | None
```]
With every iteration, two new terms of a new type come available, even though it is unlikely one would ever use them.
However, since `Option` takes only one generic argument, the growth is linear as many of the terms cancel out due to already being in the cache.
If we have something with multiple generic parameters, it becomes exponential.
Consider the example of wrapping the types we have to pair (a tuple with two elements).
At first, we have $n$ types.
After the first iteration, we have $n^2$ new types as we are taking the Cartesian product.
In the second iteration, we can create a pair by taking one of the elements from the original set of types and the second element from the set of pairs we have.
As for every pair, there are $n$ original types to choose from and we get $n^3$ pairs and also all the pairs of pairs.
Even without considering the pairs of pairs, we see that the growth is exponential.

To keep the search space to a reasonable size, we ignore all types with generics unless they are directly related to the goal.
This means that we limit the depth for the generics to 1, which is a very severe but necessary limitation.
In @third-iter-bidirectional-bfs, we will discuss how to get around this limitation.

=== Third iteration: Bidirectional BFS <third-iter-bidirectional-bfs>
The third iteration of our algorithm is a small yet powerful improvement on the second iteration described in @second-iter-bfs.
This iteration differs from the previous one by improving the handling of generics.
We note that the handling of generics is a much smaller problem if going in the backwards direction similarly to other term search tools.
This is because we can only construct the types that actually contribute towards reaching the goal.
However, if we only go in the backwards direction, we can still end up with terms such as ```rust Some(Some(...)).is_some()``` that do contribute towards the goal but not in a very meaningful way.
BFS copes with these kinds of terms quite well, as the easiest paths are taken first.
However, with multiple iterations, many not-so-useful types get added to the lookup table nonetheless.
Note that the trick with lazy evaluation of iterators does not work here as the terms have types not yet in the lookup, meaning we cannot discard them.
Filtering them out in a backward direction is possible but not trivial.

To benefit from better handling of generics going in the backward direction and an otherwise more intuitive approach of going in forward direction, we decided to make the search bidirectional.
The forward direction starts with the locals we have and starts expanding the search space from there.
Tactics that work in the forward direction ignore all types where we need to provide generic parameters.
Other tactics start working backwards from the goal.
All the tactics that work backwards do so to better handle generics.

Going backward is achieved by using the types wishlist component of the lookup table.
We first seed the wishlist with the target type.
During every iteration, the tactics working backwards from the target type only work with the concrete types we have in our wishlist.
For example, if there is ```rust Option<Foo>``` in the wishlist and we work with the ```rust Option<T>``` type, we know to substitute the generic type parameter `T` with ```rust Foo```.
This way, we avoid polluting the lookup table with many types that likely do not contribute towards the goal.
All the tactics add types to the wishlist, so forward tactics can benefit from the backwards tactics (and vice versa) before meeting in the middle.
With some tactics, such as using methods on types only working in the forward direction, we can conveniently avoid adding complex types to the wishlist if we only need them to get something simple, such as ```rust bool``` in the ```rust Some(Some(...)).is_some()``` example.


== Tactics <tactics>
We use tactics to expand the search space for the term search algorithm.
All the tactics are applied sequentially, which causes a phase-ordering problem as tactics generally depend on the results of others.
However, the ordering of tactics problem can be fixed by running the algorithm for more iterations.
Note that some tactics also use heuristics for performance optimization that also suffer from the phase ordering problem, but they cannot be fixed by running the algorithm for more iterations.

All the tactic function signatures follow the simplified function signature shown in @rust-tactic-signature.
#figure(
sourcecode(numbering: none)[
```rs
fn tactic_name(
    ctx: &TermSearchCtx,
    defs: &HashSet<ScopeDef>,
    lookup: &mut LookupTable,
) -> impl Iterator<Item = Expr>
```],
caption: [
    Term search tactic signature.
    Arguments `ctx` and `defs` give all the available context.
    State is encapsulated in `lookup`.
    All tactics return iterator that yields terms that unify with goal.
  ],
) <rust-tactic-signature>
All the tactics take in the context of term search, definitions in scope, and a lookup table and produce an iterator that yields expressions that unify with the goal type (provided by the context).
The context encapsulates the semantics of the program, the configuration for the term search, and the goal type.
Definitions are all the definitions in scope that can be used by tactics.
Some examples of definitions are local variables, functions, constants, and macros.
The definitions in scope can also be derived from the context, but they are kept track of separately to speed up the execution by filtering out definitions that have already been used.
Keeping track of them separately also allows querying them only once, as they do not change throughout the execution of the algorithm.
The lookup table is used to keep track of the state of the term search, as described in @lookup-table.
The iterator produced by tactics is allowed to have duplicates, as filtering of them is done at the end of the algorithm.
We decided to filter at the end because it is hard to guarantee that different tactics do not produce the same elements, but without the guarantee of uniqueness, there would have to be another round of deduplication nevertheless.

==== Tactic "trivial" <tactic-trivial>
A tactic called "trivial" is one of the most trivial tactics we have.
It only attempts items we have in scope and does not consider any functions / type constructors.
The items in scope contain:
1. Constants
2. Static items
3. Generic parameters (constant generics#cite-footnote("The Rust Reference, Generic parameters", "2024-04-06", "https://doc.rust-lang.org/reference/items/generics.html", "https://web.archive.org/web/20240324062312/https://doc.rust-lang.org/reference/items/generics.html"))
4. Local items

As this tactic only depends on the values in scope, we don't have to call it every iteration.
In fact, we only call it once before any of the other tactics to populate the lookup table for forward direction tactics with the values in scope.
/*
$
(x_"constant": A in Gamma #h(0.5cm) ?: A) / (? := x_"constant") 
#h(1cm)
(x_"static": A in Gamma #h(0.5cm) ?: A) / (? := x_"static") \
\
(x_"generic": A in Gamma #h(0.5cm) ?: A) / (? := x_"generic") 
#h(1cm)
(x_"local": A in Gamma #h(0.5cm) ?: A) / (? := x_"local") 
$
*/

==== Tactic "famous types" <tactic-famous-types>
"Famous types" is another rather trivial tactic.
The idea of the tactic is to attempt values of well-known types.
Those types and values are:
1. ```rust true``` and ```rust false``` of type ```rust bool```
2. ```rust ()``` of unit type ```rust ()```
While we usually try to avoid creating values out of the blue, we make an exception here.
The rationale for making the types we generate depend on the types we have in scope is that usually the programmer writes the code that depends on inputs or previous values.
Suggesting something else can be considered distracting.
However, we find these values to be common enough to usually be a good suggestion.
Another reason is that we experienced our algorithm "cheating" around depending on values anyway.
It constructed expressions like ```rust None.is_none()``` and ```rust None.is_some()``` for ```rust true```/```rust false``` which are valid but most likely never what the user wants.
For unit types, it can use any function that has "no return type", meaning it returns a unit type.
There is usually at least one that kind of function in scope, but suggesting it is unexpected more often than suggesting `()`.
Moreover, suggesting a random function with a `()` return type can often be wrong as the functions can have side effects.
Similarly to tactic "trivial", this tactic helps to populate the lookup table for the forward pass tactics.
/*
$
(?: "bool") / (? := "true" #h(0.5cm) ? := "false")
#h(1cm)
(?: "()") / (? := "()")
$
*/

==== Tactic "type constructor"

"Type constructor" is the first of our tactics that takes us from some types to other types.
The idea is to attempt to apply the constructors of types we have in scope.
We try them by looking for terms for each of the arguments the constructor has from the lookup table.
If we have terms for all the arguments, then we have successfully applied the constructor.
If not, then we cannot apply the constructor at this iteration of the algorithm.

The tactic includes both sum and product types (`enum` and `struct` for rust).

As compound types may contain generic arguments, the tactic works in both forward and backward directions.
The forward direction is used if the ADT does not have any generic parameters.
The backward direction is used for types that have generic parameters.
In the backward direction, all the generic type arguments are taken from the types in the wishlist.
By doing that, we know that we only produce types that somehow contribute to our search.

The tactic avoids types that have unstable generic parameters that do not have default values.
Unstable generics with default values are allowed, as many of the well-known types have unstable generic parameters that have default values.
For example, the definition for ```rust Vec``` type in Rust is the following:
```rs 
struct Vec<T, #[unstable] A: Allocator = Global>
```
As the users normally avoid providing generic arguments that have default values, we also decided to avoid filling them.
This means that for the ```rust Vec``` type above, the algorithm only tries different types for `T` but never touches the `A` (allocator) generic argument.
/*
#todo("How to indicate arbitary number of fields / variants?")
#todo("Should we indicate that we actually need type constructor, arguments and type is not enough or is it implementation detail?")
$
T_"struct" = A times B times A times C #h(1cm) T_"enum" = A + B + C\
\
(a: A, b: B, c: C in Gamma #h(0.5cm) ?: T_"struct") /
(? := T_"struct" (a,b,a,c)) \
\
(a: A in Gamma #h(0.5cm) ?: T_"enum") /
(? := T_"enum" (a))
#h(1cm)
(b: B in Gamma #h(0.5cm) ?: T_"enum") /
(? := T_"enum" (b))
#h(1cm)
(c: C in Gamma #h(0.5cm) ?: T_"enum") /
(? := T_"enum" (c))
$
*/

==== Tactic "free function"
This tactic attempts to apply free functions we have in scope.
It only tries functions that are not part of any ```rust impl``` block (associated with type or trait) and therefore considered "free".

A function can be successfully applied if we have terms in the lookup table for all the arguments that the function takes.
If we are missing terms for some arguments, we cannot use the function, and we try again in the next iteration when we hopefully have more terms in the lookup table.

We have decided to filter out all the functions that have non-default generic parameters.
This is because `rust-analyzer` does not have proper checking for the function to be well-formed with a set of generic parameters.
This is an issue if the generic parameters that the function takes are not present in the return type.

As we ignore all the functions that have non-default generic parameters we can run this tactic in only forward direction.
The tactic avoids functions that return types that contain references (@tactics).
However, we do allow function arguments to take items by shared references as this is a common practice to pass by reference rather than value.
/*
$
(a: A, b: B in Gamma #h(0.5cm) f: A times B -> C in Gamma #h(0.5cm) ?: C) /
(? := f(a, b)) \
$
*/

==== Tactic "impl method"
This tactic attempts functions that take a ```rust self``` parameter.
This includes both trait methods and methods implemented directly on type.
Examples for both of these cases are shown in @rust-impl-method.
Both of the impl blocks are highlighted, and each of them has a single method that takes a ```rust self``` parameter.
These methods can be called as ```rust example.get_number()``` and ```rust example.do_thingy()```.

#figure(
sourcecode(highlighted: (5,6,7,8,9, 15,16,17,18,19))[```rs
struct Example {
    number: i32,
}

impl Example {
    fn get_number(&self) -> i32 {
        self.number
    }
}

trait Thingy {
    fn do_thingy(&self);
}

impl Thingy for Example {
    fn do_thingy(&self) {
        println!("doing a thing! also, number is {}!", self.number);
    }
}
```],
caption: [
    Examples of ```rust impl``` blocks, highlighted in yellow
  ],
) <rust-impl-method>

Similarly to the "free function" tactic, it also ignores functions that have non-default generic parameters defined on the function for the same reasons.
However, generics defined on the ```rust impl``` block pose no issues as they are associated with the target type, and we can provide concrete values for them.

A performance tweak for this tactic is to only search the ```rust impl``` blocks for types that are new to us, meaning that they were not present in the last iteration.
This implies we run this tactic only in the forward direction, i.e. we need to have a term for the receiver type before using this tactic.
This is a heuristic that speeds up the algorithm quite a bit, as searching for all ```rust impl``` blocks is a costly operation.
However, this optimization does suffer from the phase ordering problem.
For example, it may happen that we can use some method from the ```rust impl``` block later, when we have reached more types and covered a type that we need for an argument of the function.

We considered also running this tactic in the reverse direction, but it turned out to be very hard to do efficiently.
The main issue is that there are many ```rust impl``` blocks for generic `T` that do not work well with the types wishlist we have, as it pretty much says that all types belong to the wishlist.
One example of this is shown in @rust-blanket-impl.

#figure(
sourcecode(numbering: none)[```rs
impl<T: fmt::Display + ?Sized> ToString for T {
    fn to_string(&self) -> String { /* ... */ }
}
```],
caption: [
    Blanket ```rust impl``` block for ```rust ToString``` trait in the standard library.
    All the types that implement ```rust fmt::Display``` also implement ```rust ToString```.
  ],
) <rust-blanket-impl>

One interesting aspect of Rust to note here is that even though we can query the ```rust impl``` blocks for type, we still have to check that the receiver argument is of the same type.
This is because Rust allows also some other types that dereference to the type of ```rust Self``` for the receiver argument#cite-footnote("The Rust Reference, Associated Items", "2024-04-06", "https://doc.rust-lang.org/reference/items/associated-items.html#methods", "https://web.archive.org/web/20240324062328/https://doc.rust-lang.org/reference/items/associated-items.html#methods").
These types include but are not limited to ```rust Box<S>```, ```rust Rc<S>```, ```rust Arc<S>```, and ```rust Pin<S>```.
For example, there is a method signature for the ```rust Option<T>``` type in the standard library#cite-footnote("Rust standard library source code", "2024-04-06", "https://doc.rust-lang.org/src/core/option.rs.html#715", "https://web.archive.org/web/20240317121015/https://doc.rust-lang.org/src/core/option.rs.html#715") shown in @rust-receiver-type.

#figure(
sourcecode(numbering: none)[```rs
impl<T> Option<T> {
    pub fn as_pin_ref(self: Pin<&Self>) -> Option<Pin<&T>> { /* ... */ }
}
```],
caption: [
    Reciver argument with type other than ```rust Self```
  ],
) <rust-receiver-type>
As we can see from the snippet above, the type of ```rust Self``` in the ```rust impl``` block is ```rust Option<T>```.
However, the type of ```rust self``` parameter in the method is ```rust Pin<&Self>```, which means that to call the `as_pin_ref` method, we actually need to have an expression of type ```rust Pin<&Self>```.

We have also decided to ignore all the methods that return the same type as the type of ```rust self``` parameter.
This is because they do not take us any closer to goal type, and we have considered it unhelpful to show users all the possible options.
If we allowed them, then we would also receive expressions such as ```rust some_i32.reverse_bits().reverse_bits().reverse_bits()``` which is valid Rust code but unlikely something the user wished for.
Similar issues often arise when using the builder pattern, as shown in @rust-builder.
/*
#todo("same as free function as the self is not really that special")
$
(a: A, b: B in Gamma #h(0.5cm) f: A times B -> C in Gamma #h(0.5cm) ?: C) /
(? := f(a, b)) \
$
*/

==== Tactic "struct projection" <tactic-struct-projection>
"Struct projection" is a simple tactic that attempts all field accesses of struct.
The tactic runs only in the forward direction, meaning we only try to access fields of the target type rather than search for structs that have field with target type.
In a single iteration, it only goes one level deep, but with multiple iterations we cover all the fields of substructs.

This tactic greatly benefits from the use of BFS over DFS, as the implementation for accessing all the fields of the parent struct is rather trivial, and with multiple iterations, we get the full coverage, including substruct fields.
With DFS, the implementation was much more cumbersome, as simple recurring on all the fields leaves out the fields themselves.
As a result, the implementation for DFS was about two times longer than the implementation for BFS.

As a performance optimization we only run this tactic on every type once.
For this tactic, this optimization does not reduce the total search space covered, as accessing the fields doesn't depend on the rest of the search space covered.
/*
#todo("Should we show all fields and how to name them?")
$
T_"struct" = A times B times A times C\
\
(s: T_"struct" in Gamma #h(0.5cm) ?: A) /
(? := s.a) \
$
*/

==== Tactic "static method" <tactic-static-method>
"Static method" tactic attempts static methods of ```rust impl``` blocks, that is, methods that are associated with either type or trait, but do not take the ```rust self``` parameter.
Some examples of static methods are ```rust Vec::new()``` and ```rust Default::default()```.

As a performance optimization, we query the ```rust impl``` block for types we have a wishlist, meaning we only go in the backward direction.
This is because we figured that the most common use case for static methods is the factory method design pattern described in @design-patterns-elements-of-reusable-oo-software.
Querying ```rust impl``` blocks is a costly operation, so we only do it for types that are contributing towards the goal, meaning they are in wishlist.

Similarly to the "Impl method" tactic, we ignore all the methods that have generic parameters defined at the method level for the same reasoning.
/*
#todo("This is same as free function again...")
$
(a: A, b: B in Gamma #h(0.5cm) f: A times B -> C in Gamma #h(0.5cm) ?: C) /
(? := f(a, b)) \
$
*/

==== Tactic "make tuple"
The "make tuple" tactic attempts to build types by constructing a tuple of other types.
This is another tactic that runs only in the backward direction, as otherwise the search space would grow exponentially.
In Rust, the issue is even worse as there is no limit for how many items can be in a tuple, meaning that even with only one term in scope, we can create infinitely many tuples by repeating the term an infinite number of times.

Going in the backward direction, we can only construct tuples that are useful and therefore keep the search space reasonably small.
/*
$
(a: A, b: B in Gamma #h(0.5cm) ?: (A, B)) /
(? := (a, b)) \
$
*/

= Evaluation <evaluation>
In this chapter, we evaluate the performance of the three iterations of the algorithm as implemented in @term-search-iters.
The main focus is on the third and final iteration, but we compare it to previous iterations to highlight the differences.

First, we perform an empirical evaluation of the tree algorithms by performing a resynthesis on existing Rust programs.
Later, we focus on some hand-picked examples to show the strengths and weaknesses of the tool.

== Resynthesis
Resynthesis is using the tool to synthesize programs for which a reference implementation exists.
This allows us to compare the generated suggestions to known-good programs.
For resynthesis, proceed as follows:
1. Take an existing open-source project as a reference implementation.
2. Remove one expression from it, creating a hole in the program.
3. Run term search in the hole.
4. Compare the generated expressions to the reference implementation.
5. Put back the original expression and repeat on the rest of the expressions.

==== Choice of expressions
We chose to perform resynthesis only on the #emph[tail expressions] of blocks, as we consider this the most common use case for our tool.
A block expression is a sequence of statements followed by an optional tail expression, enclosed in braces (`{...}`).
For example, the body of a function is a block expression, and the function evaluates to the value of its tail expression.
Block expressions also appear as the branches of ```rust if``` expressions and ```rust match```-arms.
For some examples, see @rust-tail-expr.
#figure(
sourcecode(highlighted: (4, 10, 13, 17, 21))[
```rs
fn foo(x: Option<i32>) -> Option<bool> {
  let y = {
    /* Compute something */
    true
  }
  let res = match x {
    Some(it) => {
      if x < 0 {
        /* Do something */
        true
      } else {
        /* Do something else */
        false
      }
    }
    None => {
      true
    }
  }

  Some(res)
}
```],
caption: [
    Examples of tail expressions: in a scoping block (line 4), in branch arms (line 10, 13, 17) and the return position (line 21).
  ],
) <rust-tail-expr>

==== Choice of metrics
For resynthesis, we are interested in the following metrics:

1. #metric[Holes filled] represents the fraction of tail expressions where the algorithm finds at least one term that satisfies the type system. The term may or may not be what was there originally.
2. #metric[Holes filled (syntactic match)] represents the share of tail expressions in relation to the total number of terms that are syntactically equal to what was there before. Note that syntactical equality is a very strict metric, as programs with different syntax may have the same meaning. For example, ```rust Vec::new()``` and ```rust Vec::default()``` produce exactly the same behavior. As deciding the equality of the programs is generally undecidable according to Rice's theorem @rice-theorem, we will not attempt to consider the equality of the programs and settle for syntactic equality.
   To make the metric slightly more robust, we compare the programs ASTs, effectively removing all the formatting before comparing.
3. #metric[Average time] represents the average time for a single term search query. Note that although the cache in term search is not persisted between runs, the lowering of the program is cached. This is however also true for the average use case of `rust-analyzer` as it only wipes the cache on restart.
   To benchmark the implementation of term search rather than the rest of `rust-analyzer` we run term search on hot cache.
4. #metric[Terms per hole] - This shows the average number of options provided to the user.

These metrics are relatively easy to measure and relevant to users:
They tell us how often the tool offers assistance, how much of it is useful, and if it slows down the user's flow of development.
All experiments are conducted on a consumer-grade computer with an AMD Ryzen 7 CPU and 32GB of RAM.

==== Choice of reference implementations
For our experiments, we select a number of open-source Rust libraries.
In Rust, #emph[crate] is the name for a library.
We use _crates.io_#cite-footnote("The Rust community’s crate registry", "2024-04-06", "https://crates.io/", "https://web.archive.org/web/20240409223247/https://crates.io/"), the Rust community’s crate registry as a source of information of the most popular crates.
_Crates.io_ is the _de facto_ standard crate registry, so we believe that it reflects the popularity of the crates in the Rust ecosystem very well.

We select representative examples of different kinds of Rust programs by picking crates from popular categories on _crates.io_. 
For each category containing at least 1000 crates, we select its top 5 crates, sorted by all-time downloads.
This leaves us with 31 categories and a total of 155 crates.
The full list of crates can be seen in #ref(<appendix-crates>, supplement: "Appendix").

==== Results
First, we are going to take a look at how the hyperparameter of search depth affects the chosen metrics.

We measured #metric[holes filled] and the number of #metric[terms per hole] for search depths up to 5 (@term-search-depth-accuracy, @tbl-depth-hyper-param).
For search depth 0, only trivial tactics (@tactic-trivial and @tactic-famous-types) are run.
This results in 18.9% of the holes being filled, with only 2.5% of the holes having syntactic matches.
Beyond the search depth of 2, we noticed barely any improvements in the portion of holes filled.
At depth 2, the algorithm fills 74.9% of holes.
By doubling the depth, the number of holes filled increases only by 1.5%pt to 76.4%.
More interestingly, we can see from @tbl-depth-hyper-param that syntactic matches starts to decrease after a depth of 3.
This is because we get more results for subterms and squash them into ```rust Many```, i.e. replace them with a new hole.
Terms that would result in syntactic matches get squashed, resulting in a decrease in syntactic matches.

The number of terms per hole follows a similar pattern to holes filled, but the curve is flatter.
At depth 0, we have, on average, 15.1 terms per hole.
At depths above 4, this number plateaus at around 23 terms per hole.
Note that a larger number of terms per hole is not always better.
Too many terms might be overwhelming to the user.

Over 15 terms per hole at depth 0 is more than we expected, so we will more closely investigate the number of terms per hole in @c-style-stuff.

#figure(
  placement: auto,
  grid(
  image("fig/accuracy.png", width: 100%),
  image("fig/nr_suggestions.png", width: 100%),

  ),
  caption: [
    The effect of search depth on the fraction of holes filled, and the average number of terms per hole.
    For depth >2, the number of holes filled plateaus.
    Syntactic matches do not improve at depth above 1.
    Number of terms per hole starts at high number of 15 and increases until depth of 4 reaching 22.
  ],
) <term-search-depth-accuracy>


To more closely investigate the time complexity of the algorithm, we run the experiment up to a depth of 20.
We estimate that running the experiment on all 155 crates would take about half a month.
In order to speed up the process, we select only the most popular crate for each category.
This results in 31 crates in total (#ref(<appendix-reduced-crates>, supplement: "Appendix")).

We observe that in the average case, the execution time of the algorithm is in linear relation to the search depth (@term-search-depth-time).
Increasing depth by one adds about 8ms of execution time on average.

#figure(
  placement: auto,
  image("fig/time.png", width: 90%),
  caption: [
    Execution time of the algorithm is linear in the search depth.
    $"Slope" = 7.6"ms"/"depth"$, standard deviation = 6.7ms
  ],
) <term-search-depth-time>
We can see that increasing the search depth over two can actually have somewhat negative effects.
The search will take longer, and there will be more terms.
More terms often mean more irrelevant suggestions.
By examining the fraction of holes filled and holes filled with syntactic matches, we see that both have reached a plateau at depth 2.
From that, we conclude that we are mostly increasing the number of irrelevant suggestions.
This can also be seen in @term-search-depth-accuracy, where the fraction of holes filled has stalled after the second iteration, but execution time keeps increasing linearly in @term-search-depth-time.

#figure(
  placement: auto,
  table(
    columns: 5,
    inset: 5pt,
    align: horizon,
    table.header[*Depth*][*Holes filled*][*Syntactic matches*][*Terms per hole*][*Average time*],
[0], [18.9%], [2.5%], [15.1], [0.5ms], 
[1], [68.6%], [11.0%], [18.1], [7.1ms], 
[2], [74.9%], [11.3%], [20.0], [49.5ms], 
[3], [76.1%], [11.4%], [21.5], [79.5ms], 
[4], [76.4%], [11.3%], [22.1], [93.9ms], 
[5], [76.5%], [11.3%], [22.3], [110.1ms],
  ),
  caption: [
    Depth hyperparameter effect on metrics.
    Holes filled plateaus at 76% on depth 2.
    Syntactic matches reaches 11.4% at depth 3 and starts decreasing.
    Terms per hole starts at high number of 15 per hole, plateaus at depth 4 around 22 terms per hole.
    Average time increases about linearly.
  ]
) <tbl-depth-hyper-param>

With a depth of 2, the program manages to generate a term that satisfies the type for 74.9% of all holes.
In 11.0% of searches, the generated term syntactically matches the original term.
The average number of terms per hole is 20, and they are found in 49ms.
However, the numbers vary a lot depending on the style of the program.
The standard deviation between categories for the average number of terms is about 56 terms, and the standard deviation of the average time is 135ms.
Both of these are greater than the average numbers themselves, indicating large differences between categories.
We discuss the categories that push the standard deviation so high in @c-style-stuff.

#let ver(x) = raw("v" + str(x))

To give some context to the results, we decided to compare them to results from previous iterations of the algorithm.
However, both of the previous algorithms were so slow with some particular crates that we couldn't run them on the whole set of benchmarks.
As some of the worst cases are eliminated for iterations #ver(1) and #ver(2), the results in @tbl-versions-comparison are more optimistic for #ver(1) and #ver(2) than for the final iteration of the algorithm.
Nevertheless, the final iteration manages to outperform both of the previous iterations.

The first iteration performs significantly worse than others, running almost two orders of magnitude slower than other iterations and filling about only a third of the holes compared to the final iteration of the algorithm.
As the performance of the first iteration is much worse than the later iterations, we will not dive into the details of it.

Instead, we compare the last two iterations more closely.
The final iteration manages to fill 1.6 times more holes than the second iteration of the algorithm at depth 3.
It also fills 1.8 times more holes with syntactic matches.
These results were achieved in 12% less time than the second iteration.

#figure(
  // placement: auto,
  table(
    columns: 5,
    align: (x, _) => if x == 4 { right } else { horizon },
    inset: 5pt,
    table.header[*Algorithm*][*Holes filled*][*Syntactic matches*][*Terms per hole*][*Avg time*],
[#ver(1), $"depth"=1$], [26%], [4%], [5.8], [4900ms], 
[#ver(2), $"depth"=3$], [46%], [6%], [17.2], [90ms], 
//[v3, $"depth"=2$], [75%], [11%], [20.0], [49ms], 
[#ver(3), $"depth"=3$], [76%], [11%], [21.5], [79ms],
  ),
  caption: [
    Comparison of algorithm iterations.
    #ver(1) performs the worst in every metric, especially execution time.
    #ver(2) runs slightly slower than #ver(3), and fills significantly fewer holes.
    // V3 with depth 2 outperforms V2 with depth 3 by filling more holes in half the time.
  ]
) <tbl-versions-comparison>

In addition to average execution time, we care about the low latency of suggestions.
We chose 100ms as a latency threshold, which we believe is low enough for responsive autocompletion.
This is a recommended latency threshold for web applications (@usability-engineering), and the mean latency of writing digraphs while programming is around 170ms (@typing-latency).
We will use our algorithm with a depth of 2, as this seems to be the optimal depth for autocompletion.

We found that 87% of holes can be filled within 100ms.
In 8 of the categories, all holes could be filled in 100ms.
The main issues arose in the categories "hardware-support" and "external-ffi-bindings", in which only 6% and 16% of the holes could be filled within 100ms threshold.
These categories were also problematic from the other aspects, and we will discuss the issues in them in detail in @c-style-stuff.


== Usability <usability>
In this section, we study cases where our algorithm either performs very well or very poorly.
We discuss the performance of our algorithm for different styles of programs as well as in different contexts in which to perform term searches. 

==== Generics
Although we managed to make the algorithm work decently with a low amount of generics, extensive use of generics slows it down.
Crates in the category "mathematics" are highly generic, and as a result, the average search time in this category is about 15 times longer than the average over all categories (767ms vs 50ms, @tbl-per-category-results).
One example is `nalgebra`#cite-footnote("Crates.io, nalgebra library", "2024-04-06", "https://crates.io/crates/nalgebra", "https://web.archive.org/web/20230928073209/https://crates.io/crates/nalgebra") crate,
which uses generic parameters in almost all of its functions.
The slowdown occurs because the wishlist of types grows very large since there are many generic types with different trait bounds.

==== Tail expressions
We find that tail expressions are one of the best contexts to perform term search in.
They are a good fit for both filling holes and also for providing autocompletion suggestions, for the following reasons:
1. Tail expressions usually have a known type.
  The type is either written explicitly (e.g. a function return type) or can be inferred from context (e.g. all match arms need to have the same type).
2. Once the user starts writing the tail expression, they usually have enough terms available in context to fill the hole.
  For example, it is common to store `struct` fields in local variables and then combine them into a `struct` only in the tail expression.

Accurate type information is essential for term search to provide good suggestions.
When filling holes, the user has often already put in some extra effort by narrowing down the type of hole.
Non-tail expressions, however, often lack enough type information, and thus autocompletion produces no suggestions at all.

==== Function arguments
We found that letting the algorithm search for parameters of a function call yields good results.
This is especially true when the user is working in "exploration mode" and is looking to find different ways of calling the function.
Similarly to tail expressions, function calls usually have accurate type information available for the arguments, with some exceptions for generic types.
Often, there are also arguments of the right type available in context, so the term search can easily fill them in.

==== Local variables
In practice, term search is not very useful for generating terms for local variables.
Usually, a local variable is bound in a `let`-statement, and it is common to omit its type and let the compiler infer it instead.
This, however, means that there is no type information available for the term search.
Adding the type explicitly fixes the issue, but this results in non-idiomatic Rust code.
In this regard, type inference and term search have opposite goals:
One finds types for programs, and the other finds programs for types.

==== Builder pattern
As discussed in @machine-learning, term search struggles to suggest terms of types using the builder pattern.
Suggestions like `Foo::builder().build()` are incomplete but valid suggestions.
However, we found that in some cases, such suggestions provide value when the user is writing code in "exploration mode".
Such suggestions indicate a way of getting something of the desired type.
Now the user has to evaluate if they want to manually call the relevant methods on the builder or if they do not wish to use the builder at all.
Without these suggestions, the user may even not know that a builder exists for the type.

==== Procedural Macros
An interesting observation was that filling holes in the implementation of procedural macros is less useful than usual and can even cause compile errors.
The decrease in usability is caused by procedural macros mapping ```rust TokenStream``` to ```rust TokenStream``` (Rust syntax to Rust syntax), meaning we do not have useful type information available.
This is very similar to the builder pattern, so the decrease in usefulness originates from the same reasons.
However, procedural macros are somewhat special in Rust, and they can also rise compile-time errors.
For example, one can assert that the input ```rust TokenStream``` contains a non-empty `struct` definition.
As the term search has no way of knowing that the ```rust TokenStream``` has to contain certain tokens, it also suggests other options that clearly validate the rule, causing the error to be thrown.

==== Formatting
We found that the formatting of the expressions can have a significant impact on the usability of the term search in cases of autocompletion.
This is because it is common for LSP clients to filter out suggestions that do not look similar to what the user is typing.
Similarity is measured at the level of text with no semantic information available.
This means that even though ```rust x.foo()``` (method syntax) and ```rust Foo::foo(x)``` (universal function call syntax) are the same, the second option is filtered out if the user has typed ```rust x.f``` as text wise they do not look similar.
This causes some problems for our algorithm, as we decided to use universal function call syntax whenever possible, as this avoids ambiguity.
However, users usually prefer method syntax as it is less verbose and easier to understand for humans.

However, this is not a fundamental limitation of the algorithm.
One option to solve this would be to produce suggestions using both of the options.
That, however, has its own issues, as it might overwhelm the user with the number of suggestions if the suggestions are text-wise similar.
There can always be options when the user wishes to mix both of the syntaxes, which causes the number of suggestions to increase exponentially as every method call would double the number of suggestions if we would suggest both options.

==== Foreign function interface crates <c-style-stuff>
We found that for some types of crates, the performance of the term search was significantly worse than for others.
It offers a lot more terms per hole by suggesting 303 terms per hole, which is about 15 times more than the average of 20.
Such a large number of suggestions is overwhelming to the user, as 300 suggestions do not even fit on the screen.
Interestingly, almost all of the terms are found at depth 0, and only a very few are added at later iterations.

A high number of suggestions are caused by those crates using only a few primitive types, mostly integers.
For example, in C, it is common to return errors, indexes, and sometimes even pointers as integers.
Yet C's application binary interface (ABI) is the only stable ABI Rust has.
Foreign function interface (FFI) crates are wrappers around C ABI and therefore often use integer types for many operations.

Searching for an integer, however, is not very useful as many functions in C return integers, which all fit into the hole based on type.
For example, the number of terms found per hole reaches 300 already at depth 0, as there are many integer constants that all fit most holes.
This means that there is a fundamental limitation of our algorithm when writing C-like code in Rust and working with FFI crates.
As the point of FFI crates is to serve as a wrapper around C code so that other crates wouldn't have to, we are not very concerned with the poor performance of term search in FFI crates.

To see how the results for crates with idiomatic Rust code would look, we filtered out all crates from the categories "external-ffi-bindings", "os", and "no-std" (@tbl-depth-hyper-param-median).
We can see that _terms per hole_ is the only metric that suffers from C-like code.

#figure(
  //placement: auto,
  table(
    columns: 5,
    inset: 5pt,
    align: horizon,
    table.header[*Depth*][*Holes filled*][*Syntactic matches*][*Terms per hole*][*Average time*],
[0], [19.0%], [2.6%], [1.3], [0.4ms], 
[1], [69.1%], [11.1%], [3.9], [6.5ms], 
[2], [75.5%], [11.4%], [5.8], [52.1ms], 
[3], [76.7%], [11.5%], [7.4], [84.1ms], 
[4], [77.0%], [11.4%], [8.0], [99.1ms], 
[5], [77.1%], [11.4%], [8.2], [116.0ms], 
 
  ),
  caption: [
    Results without crates from categories _external-ffi-bindings_, _os_ and _no-std_.
    _Holes filled_, _syntatic matches_ and _average time_ have similar results to overall average.
    There are about 14 terms less per hole at all depths.
  ]
) <tbl-depth-hyper-param-median>

== Limitations of the methods
In this section, we highlight some limitations of our evaluation.
We point out that "holes filled" is a too permissive metric, and "syntactic matches" is too strict.
Ideally, we want something in between, but we don't have a way to measure it.

==== Resynthesis
Metric "holes filled" does not reflect the usability of the tool very well.
This would be a useful metric if we used it as a proof search.
When searching for proofs, we often care that the proposition can be proved rather than which of the possible proofs it generates.
This is not the case for regular programs with side effects.
For them, we only care about terms that are semantically correct, e.g. do what the program is supposed to do.
Other terms can be considered noise, as they are programs that no one asked for.

Syntactic matches (equality) is a too strict metric as we actually care about the semantic equality of programs.
The metric may depend more on the style of the program and the formatting than on the real capabilities of the tool.
Syntactic matches also suffer from squashing multiple terms to the ```rust Many``` option, as the new holes produced by _Many_ are obviously not what was written by the user.

Average time and number of terms per hole are significantly affected by a few categories that some may consider outliers.
We have decided not to filter them out to also show that our tool is a poor fit for some types of programs.

Average execution can also be criticized for being irrelevant.
Having the IDE freeze for a second once in a while is not acceptable, even if at other times the algorithm is very fast.
To also consider the worst-case performance, we have decided to also measure latency.
However, we must note that we only measure the latency of our algorithm.
While using the tool in the IDE, the latency is higher due to LSP communication and the IDE also taking some time.
We only measure the latency of our algorithm, as other sources of latency are outside of our control and highly dependent on the environment.

==== Usability
This section is based on the personal experience of the author and may therefore not reflect the average user very well.
Modeling the average user is a hard task on its own and would require us to conduct a study on it.
As studying the usage of IDE tools is outside the scope of this thesis, we only attempt to give a general overview of the strengths and weaknesses of the tool.
Different issues may arise when using the tool in different contexts.

= Future work <future-work>
In this section, we will discuss some of the work that could be done to improve term search in `rust-analyzer`.
Some of these topics consist of features that were not in the scope of this thesis.
Other focus on improving the `rust-analyzer` functionality overall.

==== More permissive borrow checking
The current borrow checking algorithm we implemented for `rust-analyzer` is rather conservative and also forbids many of the correct programs.
This decreases the usefulness of term search whenever reference types are involved.
The goal would be to make the borrow checking algorithm in `rust-analyzer` use parts of the algorithm that is in the official compiler but somehow allow borrow checking also on incomplete programs.
Lowering incomplete programs (the user is still typing) to MIR and performing borrow checking incrementally is a complex problem, however, we believe that many other parts of the `rust-analyzer` could benefit from it.

==== Smarter handling of generics
In projects with hundreds of functions that take generic parameters our algorithm effectiveness decreases.
One of the main reasons for it is that we fully normalize all types before working with them.
In case of types and functions that have generic parameters this means substituting in the generic parameters.
However, that is always not required.
Some methods on types with generic parameters do not require knowing exact generic parameters and therefore can be used without substituting in the generic types.
Some examples of it are ```rust Option::is_some``` and ```rust Option::is_none```.
Others only use some of the generic parameters of the type.
If not all generic parameters are used, we could avoid substituting in the generic types that are not needed, as long as we know that we have some options available for them.

==== Development of more tactics
A fairly obvious improvement that we believe still should be touched on is the addition of new tactics.
The addition of new tactics would allow usage in a new context.
Some ideas for new tactics:
- Tuple projection - very similar to struct projection. Very easy to add.
- Macro call - similarly to function calls, macros can be used to produce terms of unexplored types.
  As macros allow more custom syntax and work at the level of metaprogramming, adding them can be more complex.
- Higher-order functions - generating terms for function types is more complex than working with simple types.
  On the other hand, higher-order functions would allow the usage of term search in iterators and therefore increase its usefulness by a considerable margin.
- Case analysis - Perform a case split and find a term of suitable type for all the match arms.
  May require changing the algorithm slightly as each of the match arms has a different context.

==== Machine learning based techniques
We find that machine-learning-based techniques could be used to prioritize generated suggestions.
All the terms would still be generated by term search and would be valid programs by construction, which is a guarantee that LLMs cannot have.
On the other hand, ordering suggestions is very hard to do analytically, and therefore we believe that it makes sense to train a model for it.
With better ordering of suggestions, we can be more permissive and allow suggestions that do not affect the type of the term (endofunctions).
For example, suggestions for builder patterns could be made more useful by also suggesting some setter methods.

==== LSP response streaming
Adding LSP response streaming is an addition to `rust-analyzer` that would also benefit term search.
Response streaming would be especially helpful in the context of autocompletion.
It would allow us to incrementally present the user autocompletion suggestions, meaning that latency would become less of an issue.
With the latency issue solved, we believe that term-search-based autocompletion suggestions could be turned on by default.
Currently, the main reason for making them opt-in was that the autocompletion is already slow in `rust-analyzer` and term search makes it even slower.

= Conclusion <conclusion>
In this thesis, our main objective was to implement term search for the Rust programming language.
We achieved it by implementing it as an addition to `rust-analyzer`, the official LSP server for Rust.

First, we gave an overview of the Rust programming language to understand the context we were working in.
We are focusing on the type system and the borrow checking, as they are two fundamental concepts in Rust.

After that, we gave an overview of term search and the tools for it.
We focused on the tools used in Agda, Idris, Haskell, and StandardML.
We analyzed both their functionality and the algorithms they use.
By comparing them to one another, we laid the groundwork for our own implementation.

After that, we covered the LSP protocol and some of the autocompletion tools to gain some understanding of the constraints we have when trying to use the term search for autocompletion.

The term search algorithm we implemented is based on the tools used in Agda, Idris, Haskell, and StandardML.
We took a different approach from the previous implementations by using a bidirectional search.
The bidirectional approach allowed us to implement each tactic in the direction that was the most natural fit for it.
This resulted in a rather simple implementation of tactics that achieved relatively high performance.

To evaluate the performance of the algorithm, we ran it on existing open-source projects.
For measuring the performance, we chose the top 5 projects from the most popular categories on crates.io, the Rust community’s crate registry.
This resulted in 155 crates.

We added term-search-based autocompletion suggestions to evaluate the usability of term search for autocompletion.
With its small depth, the algorithm proved to be fast enough and resulted in more advanced autocompletion suggestions compared to the usual ones.
As the autocompletion in `rust-analyzer` is already rather slow, the feature is disabled by default, yet all the users of it can opt into it.
