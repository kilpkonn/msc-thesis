#import "template.typ": *

// Take a look at the file `template.typ` in the file panel
// to customize this template and discover how it works.
#show: project.with(
  title: "Term Search in Rust",
  title_estonian: "Avaldise otsing programmeerimiskeeles Rust",
  thesis_type: "Master thesis",
  authors: (
    (
      name: "Tavo Annus",
      student_code: "211564IAPM"
    ),
  ),
  supervisors: (
    "Philipp Joram",
  ),
  // Insert your abstract after the colon, wrapped in brackets.
  // Example: `abstract: [This is my abstract...]`
  abstract: lorem(59),
  location: "Tallinn",
  date: "January 17, 2024",
)

// We generated the example code below so you can see how
// your document will look. Go ahead and replace it with
// your own content!

= Introduction
Rust#footnote(link("https://www.rust-lang.org/")) is a new programming language for developing reliable and efficient systems.
The language was originally created by Mozilla for Firefox but is now gaining popularity and has found its way to the Linux kernel#footnote(link("https://lkml.org/lkml/2022/10/16/359")).
Rust has expressive type system that guarantees no undefined behaviour even though it has reference types.
This is done by rejecting all programs that may contain undefined behavior during the compilation.
We will call the set of programs that can be compiled valid, as they are guaranteed to not cause undefined behavior.
Many programming languages with type systems that guarantee the progam to be valid have tools that help the programmer with term search i.e. by searching for valid programs (also called expressions in Rust) that satisfy the type system.
Rust, however, does not have tools for term search, although the type system makes it a perfect candidate for one.
Consider the following Rust program:
```rs
enum Option<T> { None, Some(T) }

fn wrap(arg: i32) -> Option<i32> {
    todo!();
}
```

From the types of values in scope and constructors of `Option`, we can produce the expected result of wrapping the argument in `Option` and returning it.
By combining multiple type constructors as well as functions in scope or methods on types, it is possible to produce more complex valid programs.

== Motivation
Due to Rust having an expressive type system, the programmer might find themselves quite often wrapping the result of some function behind multiple layers of type constructors. For example, in the web backend framework `actix-web`#footnote(link("https://actix.rs/")), a typical JSON endpoint function might look something like this:
```rs
struct FooResponse { /* Struct fields */ }

#[get("/foo")]
async fn foo() -> Option<Json<FooResponse>> {
    let service_res = service.foo(); // Get a response from some service
    Some(Json(FooResponse {
        /* Fill struct fields from `service_res` */
    }))
}
```
We can see that converting the result from the service to `FooResponse` and wrapping it in `Some(Json(...))` can be automatically generated just by making the types match.
This means that term search can be used to reduce the amount of code the programmer has to write.
In @how-programmers-interact-with-code-generation-models[p. 19] they suggest that Large Language Model (LLM) based code generation tools are used to reduce the amount of code the programmer has to write therefore making them faster (_acceleration mode_).
In @how-programmers-interact-with-code-generation-models[p. 19] they say that in addition to _acceleration mode_, LLMs are also be used in so-called _exploration mode_ where the programmer is unsure of how to proceed and uses the term search to explore possible paths to go forward.
They state that both modes are common usage patters among programmers @how-programmers-interact-with-code-generation-models[p. 2].

In acceleration mode, term search is not as powerful as language models, but it can be more predictable as it has well-defined tactics that it uses rather than deep neural networks.
There is not so much "wow" effect - it just produces code that one could write by trying different programs that type-check.

However, there seems to be a bigger advantage for term search in _exploration mode_.
In @how-programmers-interact-with-code-generation-models[p. 10], they also stated that programmers tend to explore only if they have confidence in the tool.
As term search only produces valid programs based on well-defined tactics, it is a lot easier to trust it than code generation based on language models that have some uncertainty in them.

== Research Objectives
The main objective of this thesis is to implement tactics-based term search for a programming language Rust.
Other objectives include:
- Evaluating the fitness of tactics on existing large codebases
- Investigating term search usability for autocompletion

== Research Questions
The research questions for this thesis are:
- How to implement tactic based term search for programming language Rust?
- How to evealuate the fitness of the term search?
- How can term serch be used for autocompletion?
#todo("This and previous subsection seeb kind of same. Should I delete one or...? On the other hand people keep telling we should have both but I've yet to see an example where both exist without duplication.")

= Background / State of the art (week 1)
#todo("Is State of the art legit title?")

== Term search
The Curry-Howard correspondence is a direct correspondence between computer programs and mathematical proofs.
It is the basic idea in proof assistants such as Coq and Isabelle and also in dependently typed languages such as Agda and Idris.
The idea is to state a proposition as a type and then to prove it by producing a value of the given type as explained in @propositions-as-types.

For example, if we have addition on natural numbers defined as following Idris code:
// Todo rename add, say idris
```hs
add : Nat -> Nat -> Nat
add Z     m = m
add (S k) m = S (add k m)
```
We can prove that adding any natural number `m` to 0 is equal to the natural number `m`.
For that, we create a declaration `plus_reduces_Z` with the type of the proposition and prove it by defining a program that satisfies the type.
```hs
plus_reduces_Z : (m : Nat) -> plus Z m = m  -- Proposition
plus_reduces_Z m = Refl                     -- Proof
```
The example above is quite trivial, as the compiler can figure out from the definition of `plus` that `plus Z m` is defined to be `m` according to first definition of `add`
Based on that we can prove `plus_reduces_Z` by reflexivity.
However, if there are more steps required, writing proofs manually gets cumbersome, so we use tools to automatically search for terms that inhabit a type ie proposition.
For example, Agda has a tool called Agsy that is used for term search, and Idris has this built into its compiler.

=== Term search in Agda
Agda is one of the "more famous" languages that has that has tools leveraging term search.
In @dependently-typed-programming-in-agda they describe Agda as a dependently typed functional programming language and also a proof assistant.
We'll be more interested in the proof assistants as they are the ones leveraging the term search to help the programmer with coming up with proofs. 
As there are many alternatives we've picked two that seem the most popular or relavant for our use case.
We chose Agsy as this is the well known tool that comes with Agda and Mimer that atemptes to improve on Agsy.

==== Agsy <agsy>
Agsy is the term search based proof assistant that comes with Agda.
It was first published in 2006 in @tool-for-automated-theorem-proving-in-agda and integrated into Agda in 2009#footnote(link("https://agda.readthedocs.io/en/v2.6.4.1/tools/auto.html")).

We will be looking at the high level implementation of the algorithm used by Agsy for term search desvribed in @tool-for-automated-theorem-proving-in-agda.
In @tool-for-automated-theorem-proving-in-agda they say that in Agsy search space is explored using iterated deepening.
This is necessary since a problem may in general be refined to infinite depth.
The proof search can have multiple branches with subproblems.
In some cases we need to solve one subproblem to solve the "top level" problem.
This is the case when we try different approaches to come up with a term.
For example we can either use some local variable, function or type constructor to solve the problem as shown in @agsy_transformation_branches.

#figure(
  image("fig/agsy_transformation_branches.svg", width: 60%),
  caption: [
    Agsy transformation branches
  ],
) <agsy_transformation_branches>

In other cases we need to solve all the subproblems to solve the "top level" problem.
This is the case when we use type constructors that take multiple members or functions with multiple arguments.
In case of case splitting we also have to solve all the subproblems produced.
For example shown in @agsy_all_branches we see that function `foo(a: A, b: B, c: C)` can only be used if we manage to solve the subproblems of finding terms of correct type for all the arguments.

#figure(
  image("fig/agsy_all_branches.svg", width: 60%),
  caption: [
    Agsy branches for function call
  ],
) <agsy_all_branches>

Agsy uses problem collections (`PrbColl`) to model the subproblems that need to be all solved for the problem to be solved.
Solution collections (`SolColl`) are used to keep track of solutions for particular problem collection.

The intuition for the tool is following:
1. Given a problem we create set of possible subproblem collections out of which we need to solve one as show in @agsy_transformation_branches.
2. We attempt to solve all the subproblem collections by recursevely solving all the problems in collection
3. If we manage to solve all the problems in collection we use it as a possible solution, otherwise we discard it as a dead end.

The algorithm itself is based around DFS and consists of two subfunctions.
Function $"search": "problem" -> ["solution"]$ is the main entry point that attempts to find a set of solutuions for a problem.
The function internally makes use of another function $"searchColl": "PrbColl" -> ["SolColl"]$ that attempts to find set of solution collections for a problem collection.
The pseudocode for the `search` and `searchColl` functions can be seen in the snippets below.

#algo(
  title: [search],
  parameters: ("problem",),
  row-gutter: 5pt,
)[
  refs, sol := createRefs(problem) #comment[Create refinements, extract solution]\
  sols := []\
  for each ref in refs #i\
    prbcoll := apply(ref, problem) #comment[Apply refinement to problem]\
    solcolls := searchColl(prbcoll) #comment[Search for solutions for problems]\
    for each solcol in solcolls #i \
      newsol := compose(solcol, sol) #comment[Compose to get new solution] \
      addSoluion(sol, sols) #d #comment[Add solution to set of solutions]\
    end for #d \
  end for \
  return sols #comment[Return all solutions]
]
The `search` algorithm starts by creating all possible refinements for the problem and extracting the solution so far.
Refinements are generated by tactics and consist of atomic steps of refining a problem to construct the corresponding proof term.
The example in the @agsy_transformation_branches contains three possible refinements for the goal: 1) Replace it with local, 2) Replace it with function and create new subproblems for every argument, 3) Replace goal with a type constructor and create subgoals for all fields required by constructor.
In addition to 
Then we attempt to apply each refinement to the problem to transform the problem to a problem collection.
After that we attempt to solve the problem collection via the `searchColl` function.
We compose all the solution collections with current solution to get a new solution and add it to the set of possible solutions.
In the end we return the set of all possible solutions.

#algo(
  title: [searchColl],
  parameters: ("prbcoll",),
  row-gutter: 5pt,
)[
  solcolls := []\
  for each prb in prbcoll #i #comment[Iterate over all problems in collection]\
    sols := search(prb) #comment[Search solution for the problem]\
    if empty(sols) #i #comment[Check if there is a solution]\
      return [] #d #comment[Return empty for no solution]\
    end if\
    addSolutions(sols, solcolls) #d #comment[Add solutions to collection]\
  end for \
  return solcollss #comment[Return all solution collections]
]
With `searchColl` we attempt to solve problem collection by finding .
To do that we iterate over all the problems and attempt to solve them by calling `search` function.
If we cannot find solution for a problem in problem colloection we discard the whole problem collection by returning empty solution immideately.
This is because problems in the problem collection need to be solved for the solution to hold.
In case we find solutions to the problem we add them to solutions collection.
In the end we return solutions collection.

As described above the algorithm is built around DFS.
However the authors of @tool-for-automated-theorem-proving-in-agda note that while the performace of the tool is good enough to be useful it performs poorly on larger problems.
They suggest that more advanced search space reduction techniques can be used as well as writing it in a language that does not suffer from automatic memory management.
It is also noted that there seems to be many false subproblems that can never be solved so they suggest a parallel algorithm that could potentially prove the uselessness of those subproblems potentially faster to reduce the search space.

==== Mimer
Mimer is another proof assistant tool for Agda that attempts to adresss some of the shortcomings in Agsy.
In @mimer they say that Mimer is designed to handle many small synthesis problems rather than complex ones as compared to Agsy.
Mimer also doesn't perform case splits to reduce the search space.
Otherwise the main algorithm closely follows the one used in Agsy and described in @agsy.

The main differences to original Agsy implementation are:
1. Mimer uses memoization to avoid searching for same term multiple times.
2. Mimer guides the search with branch costs

Branch costs is a heuristic to hopefully guide the search to an answer faster that randomly picking branches.
In @mimer they gave lower cost to branches that contain more local variables and less external definitions.
The rationale for that is that it is more likely that user wishes to use variables from local scope than from outside of it.
However they noted in @mimer that the costs for the tactics need to be tweaked in future work as this was not their focus.
#todo("Read about paper")

=== Term search in Idris2 (week 3)
I think there is one and the only term serach implementation in Idris2.

=== Term search in Standard ML <standardml>
In @algebraic-foundations-of-proof-refinement they implemented term search for Standard ML as a part of RedPRL#footnote(link("https://redprl.org/")) project.

The algorithm suggested in @algebraic-foundations-of-proof-refinement keeps track of subgoals in an ordered sequence in which each induces a variable of the appropriate sort which the rest of the sequence may depend on.
This sequence is also called a telescope @telescopic-mappings-typed-lamda-calc.
The telescope is required to work on typesystems with dependent types.
For typesystems without dependent types ordinary `List` data structure can be used as there are no relations between subgoals.

In @algebraic-foundations-of-proof-refinement they suggest to use BFS instead of DFS to more effectively propagete substitutions to subgoals in telescope.
The idea is to run all the tactics once on each subgoal, repeatedly.
This way substitutions propagate along the subgoals telescope after every iteration.
In the case of DFS we would propagate the constraints only after exhausting the search on the first subgoal in the sequence.

In practice the Refinery uses interleaving of subgoals generated by tactics to acieve something similar.
Consider the example where we are searching for a pair of list of some type and a function of that type to `Integer` (`?goal :: ([a], a -> Integer)`).
We have `bar` of type `Bar` in scope as well as functions `mk_foo` (creates `Foo` from `Bar`) `mk_list` (create list for type) and `bar_to_int` that takes us from type `Bar` to `Integer`.
```hs
bar : Bar
mk_foo : Bar -> Foo
mk_list_foo : Foo -> [Foo]
mk_list_bar : Bar -> [Bar]
bar_to_int  : Bar -> Integer
```

First we can split the goal of finding a pair to two subgoals `[?subgoal1 : [a], ?subgoal2 : a -> Integer]`.
This is the same step for BFS and DFS as there is not much else to do with `?goal`.

Now we are at where the differences between DFS and BFS start playing out.
First lets look at how the DFS would handle the goals.
First we focus on the `?subgoal1`.
We can use `mk_list_foo` to transform the goal to finding of something of type `Foo`.
Now we have following goals `[?subgoal3 : Foo, ?subgoal2 : a -> Integer]`.
Note that although the `a` in the `?subgoal2` has to be of type `Foo` we do not propagate this knowledge there yet as we are focusing on `?subgoal3`.
We use `mk_foo` to create new goal `?subgoal4 : Bar` which we solve by providing `bar`.
Now we propagate the constraints to the remaining subgoals, `?subgoal2` in this example.
This means that the second subgoal becomes `?subgoal2 : Foo -> Integer`.
However we cannot find anything of type `Foo -> Integer` so we have to revert all the way to `?subgoal1`.
This time we use `mk_list_bar` to fill `?subgoal1` meaning that the remaining subgoal becomes `?subgoal2 : Bar -> Integer`.
We can fill it by providing `bar_to_int`.
As there are no more subgoals remaining the problem is solved.

An overview of the steps we took can be seen in the snippet below.
```hs
?goal : ([a], a -> Integer)
(?subgoal1 : [a], ?subgoal2 : a -> Integer)
(mk_list_foo(?subgoal3 : Foo), ?subgoal2 : a -> Integer)
(mk_list_foo(mk_foo(?subgoal4 : Bar), ?subgoal2 : a -> Integer)
(mk_list_foo(mk_foo(bar)), ?subgoal2 : Foo -> Integer) -- Revert to ?subgoal1
(mk_list_bar(?subgoal3 : Bar), ?subgoal2 : a -> Integer)
(mk_list_bar(bar), ?subgoal2 : Bar -> Integer)
(mk_list_bar(bar), bar_to_int)
```

Now lets take a look at the algorithm that uses BFS for to handle the goals.
The first iteration is the same as described above after which we have two subgoals `[?subgoal1, ?subgoal2]` to fill.
Once again we use `mk_list_foo` to transform the first subgoal to `?subgoal3 : Foo`.
But this time we also propagate the information to other subgoals so that we constrain the `?subgoal2` to `Foo -> Integer`.
In the next iteration we search for `Bar` in the first goal and also for a function of type `Foo -> Integer` in the second goal.
We find `bar` for the first goal, but not anything for the second goal.
This means we have to revert to `?subgoal1`.
Note that at this point we still have `?subgoal4` pending, meaning we have not yet exhausted the search in current "branch".
Reverting now means that we save some work that was guaranteed to have no effect on the overall outcome.
Having reverted back to `?subgoal1` we replace it with `mk_list_bar` transforming the goal to `?subgoal5 : Bar` and constraining the other subgoal to 
`?subgoal2 : Bar -> Integer`.
In the next iteration we can find solutions for both of the goals.
```hs
?goal : ([a], a -> Integer)
(?subgoal1 : [a], ?subgoal2 : a -> Integer)
(mk_list_foo(?subgoal3 : Foo), ?subgoal2 : Foo -> Integer)
(mk_list_foo(mk_foo(?subgoal4 : Bar)), ?subgoal2 : <impossible>) -- Revert to ?subgoal1
(mk_list_bar(?subgoal5 : Bar), ?subgoal2 : Bar -> Integer)
(mk_list_bar(bar), bar_to_int)
```

In the example above we see that BFS and propagating constraints to other subgoals can help us cut some search branches to speed up the search.
However this is not always the case.
BFS is faster only if we manage to cut the proof before exhausting the search at the current goal.
In case the first goal we focus at cannot be filled DFS is faster as it doesn't do any work on filling other goals.

=== Term search in Haskell
Wingman#footnote(link("https://hackage.haskell.org/package/hls-tactics-plugin-1.6.2.0")) is a plugin for Haskell Language Server that provides term search.
For term search Wingman uses library called Refinery#footnote(link("https://github.com/TOTBWF/refinery")) that is also based on @algebraic-foundations-of-proof-refinement similarly to the Standar ML tool we described in @standardml.

As we described the core ideas in @standardml we won't cover them here.
However we will take a look at some implementation details.

The most interesting implementation detail for us is how BFS is acieved.
Refinery uses interleaving of subgoal generated by each tactic to get the desired effect.
Let's look at the example to get a better idea what is going on.
Suppose that at some point of the term search we have three pending subgoals: `[?sg1, ?sg2, ?sg3]` and we have some thactic that prduces two new subgoals when refining `?sg1`.
The DFS way of handling it would be
```
[?sg1, ?sg2, ?sg3] -> tactic -> [?sg4, ?sg5, ?sg2, ?sg3]
```
However with interleaving the goals are ordered in the following way
```
[?sg1, ?sg2, ?sg3] -> tactic -> [?sg2, ?sg4, ?sg3, ?sg5]
```
Note that there is also a way to insert the new goals to back of the goals list which is the BFS way.
```
[?sg1, ?sg2, ?sg3] -> tactic -> [?sg2, ?sg3, ?sg4, ?sg5]
```
However in Refinery they have decided to go with interleaving as it works well with tactics that produce infinite amounts of new holes due to not making any new process.
Note that this works especially well because of the lazy evaluation in Haskell.
In case of eager evealuation the execution would still halt on producing all the subgoals so interliving would have now effect.



=== Term search in Elm with Smyth
Smyth#footnote(link("https://uchicago-pl.github.io/smyth/")) is a systen for program sketching in a typed functional language, approximately Elm.
In @smyth they describe that it uses evaluation of ordinary assertions that give rise to input-output examples, which are then used to guide the search to complete the holes.
Symth uses type and example directed synthesis as opposed to other tools in Agda only using type guided search for terms.
The general idea is to search for terms that satisfy the goal type as well as example outputs for the term given in assertions.
It is also based on a DFS, but is optimized for maximal use memoization.
The idea is to maximize the amount of terms that have same typing environment and can therefore be reused.
This is done by factorizing the terms into smaller terms that carry less context with them.
Smyth has many other opimizations but they focus on using the information from examples and are therefore not interesting for us as they focus on optimizing the handling of data provided by examples.

#todo("Rust synthesis")

== Autocomplete (week 1)
No deep dive, but some brief overview.

=== Language Server Protocol (week 1)
Again some high level overview to show some technological limitations / standard solutions.

=== TODO
#todo("Anything else? Everything else feels like legacy now as we have  LSP.
Perhaps Jetbrains built in stuff is relavant, but why that and not anything else.
Also very language dependent so hard to say anything meaningful about that.")

== LLM based autocompletions? (week 4)
#todo("Should I talk about them?
They are legit alternative.
On the other hand I do not really want to go into neural nets and LLMs and not sure if talking about them only on the high level is a good idea.
Feels like if I point out shortcomings etc someone is like but there is another model that fixes it...")

= Methods (week 5)
#todo("Should this be somewhere before?")

#todo("Should I list the implemention here as well? or is this kind of obvious?")

== Usability (week 5)
I guess this is explanation and justification what it does not do and why?
Latency, incorrect stuff, etc

== Resynthesis (week 5)

=== Chosen metrics (week 5)

=== Chosen crates (week 5)
#todo("Should I just say top5 or also list them out here?
I guess other option would be to list them in the validation paragraph")

== Limitations of the methods (week 5)
#todo("Or should it be under either of them")

= Term search design (week 6)
Before diving into the technical aspects of term search implementation, we will first explore it by giving
examples of its usages in `rust-analyzer`. 
We will first take a look at using it for filling "holes" in the program and later dive into using it for autocompletion.

== Filling holes
One of the most known examples of holes in Rust programs is the `todo!()` macro.
It is a "hole" as it denotes that there should be a program in the future but there isn't now.
These holes can be filled using term search to search for programs that fit in the hole.
All the programs generated by term search are valid programs meaning that they compile.

Example usages can be found in the snippet below:
```rs

fn main() {
    let a: i32 = 0;  // Suppose we have a variable a in scope
    let b: i32 = todo!();  // Term search finds `a`
    let c: Option<i32> = todo!();  // Finds `Some(a)`, `Some(b)` and `None`
}
```

In addition to `todo!()` holes `rust-analyzer` has concept of typed holes.
They are underscore characters at illegal positions, for example in rvalues.
From term search perspective they work similarly to `todo!()` macros - term search needs to come up with a term of some type to fill them.
#todo("what ra has before")

The same example with typed holed instead of `todo!()` macros can be found in the snippet below:
```rs

fn main() {
    let a: i32 = 0;  // Suppose we have a variable a in scope
    let b: i32 = _;  // Term search finds `a`
    let c: Option<i32> = _;  // Finds `Some(a)`, `Some(b)` and `None`
}
```

== Autocomplete
Term search can also be used to give user "smarter" autocomplete suggestions as they are typing.
#todo("he -> they")
The general idea is the same as in filling holes.
We attempt to infer the expected type at the cursor.
If we manage to infer the type then we run the term search in order to get the suggestions.

The main difference between using term search for autocomplete and using it to fill holes is that we've decided to disable borrowchecking when generating suggestions for autocompletion.
This means that not all the suggestions are valid programs and may need some modifications by user.

The rationale for it comes from both technical limitations of the tool as well as different expectations from the user.
The main techincal limitation is that borrow checking happens in the MIR layer of abstraction and `rust-analyzer` (nor `rustc`) does not support lowering partial (user is still typing) programs to MIR.

However there is also some motivation from user perspective for the tool to give also suggestions that do not borrow check.
We found that it is quite often that when writing the code the user jumps back and forward to fix borrow checking issues.
#todo("would be good to have reference to something here")
For example consider the snippet below:
```rs
/// A function that takes an argument by value
fn foo(x: String) { todo!() }
/// Another function that takes an argument by value
fn bar(x: String) { todo!() }

fn main() {
  let my_string = String::new();

  foo(my_string);
  bar(my_string); // error[E0382]: use of moved value: `my_string`
}
```
#todo("Indicate cursor position somehow")
#todo("Explain the error, sepparate section")
The most logical fix for it is to go back to where the function `foo` is called and change the call to `foo(my_string.clone())` so that the variable of `my_string` doesnt get moved.
However if we only suggest items that borrow check the `bar(my_string)` function call would be ruled out as there is no way to call it without modifying the rest of the program.


== Implementation (week 6)
#todo("What happens in ra outside term search, what are hir, mir etc. how the term search is triggered")
We've implemented term search as an addition to `rust-analyzer`, the official LSP client for the Rust language.
The main implementation is done in the High-Level Intermediate Representation (HIR) level of abstraction and borrow checking queries are made in MIR level of abstraction.

Term search entry point can be found in `crates/hir/src/term_search/mod.rs` and is named as `term_search`.
The most important inputs to term search are scope of the program we are performing the search at and target type.

The main algorithm for the term search is based on Breadth-first search (BFS).
We consider types of all values in scope as starting nodes of the BFS graph.
Then we use transitions such as type constructors and functions to get from one node of the graph to others.
The transitions are grouped into tactics to have more clear overview of the algorithm.

The high level overview of the main loop can be seen in the @term-search-main-loop.
#figure(
  image("fig/term_search_loop.svg", width: 60%),
  caption: [
    Term search main loop
  ],
) <term-search-main-loop>

#todo("DFS stuff")
We start by initializing the lookup table which keeps track of the state.
It has information of types we have reached, transitions we've taken and types we've searched for but didn't find and transitions we've used.
Before entering the main loop we populate the lookup table by running a tactic called `trivial`.
Essentially it attempts to fulfill the goal by trying variables we have in scope.
More information about the `trivial` tactic can be found in @tactic-trivial.
All the types get added to lookup table and can be later used in other tactics.
After we iteratively expand the search space by attempting different tactics untill we've exceeded the preconfigured search depth.
We keep iterating after finding the first match as there may be many possible options.
For example otherwise ve would never get suggestions for `Option::Some(..)` as `Option::None` usually comes first as it has less arguments.
During every iteration we sequentally attempt different tactics.
More on the tactics can be found in @tactics, but all of them attempt to expand the search space by trying different type transformations (type constructors, functions, methods).
The search space is expanded by adding new types to lookup table.
Example for it can be seen in @term-search-state-expansion.

#figure(
  image("fig/state_expansion.svg", width: 60%),
  caption: [
    Term search state expansion
  ],
) <term-search-state-expansion>
We start with variables `a` of type `A` and `b` of type `B`.
In the first iteration we are able to use function $f: A -> C$ on `a` and get something of type `C`.
The iteration after that we are able to use $g: C times B -> D$ and produce something of type `D`.

Once we've reached the maximum depth we take all the elements that unify with the goal type and filter out the duplicates returning all the unique paths that take us to goal type.

==== Lookup table <lookup-table>
The main task for lookup table throughout the algorithm is to keep track of the state.
The state consists of following components:
1. Terms reached (grouped by types)
2. New types reached (since last iteration)
3. Definitions used / exhausted (for example functions applied)
4. Types queried, but not reached

Terms reached serves the most obvious purpose of them.
It keeps track of the search space we have already covered (visited types) and allows quering terms for time in `O(1)` complexity.
Important thing to note here that it also performs transformation of taking a reference if we query for reference type.
This is only to keep the implementation simple and memory footprint low.
Otherwise having separate tactic for taking a reference of the type would be preferred.

New types reached keeps track of new types added to terms reached so that we can iterate only over them in some tactics to speed up the execution.

Definitions used serves also only purpose for speeding up the algorithm by avoiding definitions that have already been used.
#todo("What to do with type transformations that take generics. I guess ignore now, but throwing them away decreases available search place")

Types queried keeps track of all the types we have tried to look up from terms reached but not found.
They are used in static method tactic (see @tactic-static-method) to only search for static methods on types we haven't reached yet.
This is another optimization for speed described in @tactic-static-method.

=== Tactics (week 6) <tactics>
Tactics are used to expand the search space for the term serch algorithm.
All the tactics are applied sequentially which causes a phase ordering problem.
Some tactics may depend on results of others.
However for the order of tactics it can be fixed by running the algorithm for more iterations.
Note that some tactics also use heuristics for performace optimization and these optimizations also suffer from the phase ordering problem but they can not be fixed by running the algorithm for more iterations.

All the tactic function signatures follow the simplified function signature shown in the snippet below
```rs
fn tactic_name(
    ctx: &TermSearchCtx,
    defs: &HashSet<ScopeDef>,
    lookup: &mut LookupTable,
) -> impl Iterator<Item = Expr>
```
All the tactics take in the context of term search, definitions in scope and a lookup table and the tactics produce an iterator that yields expressions that unify with the goal type (provided by the context).
The context encampsulates semantics of the program, configuration for the term search and the goal type.
Definitions are all the definitions in scope that can be used by tactics.
Some of the examples of definitions are local variables, functions, constants and macros.
The definitions in scope can also be derived from the context, but they are kept track of sepparately to speed up the execution by filtering out definitions that have already been used.
Keeping track of them separately also allows quering them only once as the do not change throughout the execution of the algorithm.
Lookup table is used to keep track of the state of the term search as described in @lookup-table.
The iterator produced by tactics is allowed to have duplicates as filtering of them is done at the end of the algorithm.
We decided to filter at the end because it is hard to guarantee that different tactics do not produce same elements, but without the guarantee of uniqueness there would have to be another round of deduplication nevertheless.



#todo("Should I measure something per tactic?
Like how much does it help? There are many combinations so maybe not so good idea.")

==== Tactic "trivial" <tactic-trivial>
Tactic called "trivial" is one of the most trivial tactics we have.
It only attempts items we have in scope and does not perform any type transitions. #todo("what are type transitions")
The items in scope contains:
1. Constants
2. Static items
3. Generic parameters (constant generics#footnote(link("https://doc.rust-lang.org/reference/items/generics.html")))
4. Local items

As this tactic only depends on the values in scope we don't have to call it every iteration.
In fact we only call it once before any of the other tactics to populate the lookup table with the values in scope.

==== Tactic "famous types"
"Famous types" is another rather trivial tactic.
The idea of the tactic is to attempt values of well known types.
Types and values are:
1. `true` and `false` of type bool
2. `()` of type unit
Whilst we usually try to avoid creating values out of the blue we make an exception here.
The rationale of making types we generate depend on types we have in scope is that usually the programmer writes the code that depends on inputs or previous values.
Suggesting something else can be considered distracting.
However we find these values to be common enough to also suggest them.
Another reson is that we experienced our algorithm "cheating" around depending on values anyway.
It constructed expressions like `None.is_none()`, `None.is_some()` for `true`/`false` which are valid but all most never what the user wants.
For unit types it uses any function that has "no return type" meaning it returns unit type.
There is all most always at least one that cind of function in scope but suggesting it is wrong more often than suggesting `()`.


==== Tactic "type constructor"
"Type constructor" is first of our tactics that takes us from some types to another types.
The idea is to try type constructors for types we have in scope.
This includes both sum and product types (`enum` and `struct` for rust).
The tactic ignores all types that contain constant generics as we couldn't find a way to efficiently come up with constant values to try.
Trying anything doesn't work as the search space grows so big that it doesn't fit into memory.
Another performance optimization for this tactic is that it only attempts types with generics if they directly unify with goal type.
This mean that `Some(inner)` is possible but `Some(Some(inner))` is not possible outcome of our algorithm.
This decision was made to disallow exponential growth of search space.

The tactic also avoids types that have unstable generic parameters that do not have default values.
Unstable generics with default values are allowed as many of the well known types have unstable generic parameters that have default values.
For example the definition for `Vec` type in Rust is following:
```rs 
struct Vec<T, #[unstable] A: Allocator = Global>
```
As the users normally avoid providing generics arguments that have default values we also decided to avoid filling them.
This means that for the `Vec` type above the algorithm only tries different types for `T`, but never touches the `A` (allocator) generic argument.

==== Tactic "free function"
"Free function" is a tactic that tries different functions in scope.
It only tries functions that are not part of any `impl` block (associated with type or trait) and therefore considered "free".
To speed up the tactic we've decided to filter out all of the functions that have non-default generic parameters.
By trial and error we've found that functions that have generic parameters seem to be not that common.
#todo("Get some numbers here")

However attempting the function with every type we've reached slows the algorithm down quite a bit.
At the worst case the slowdown is exponential again.
As described in @tactics the tactic avoids functions that return types that contain references.
However we do allow function arguments to take items by shared references.

==== Tactic "impl method"
"Impl method" is a tactic that attempts functions that have `self` parameter.
This includes both trait methods as well as methods implemented directly on type.
Similarly to "free function" tactic it also ignores functions that have non-default generic parameters for the same reasons.
Only difference is that now both the function and the `impl` block may contain generics.
We treat them the same, meaning we ignore the function if there are any generic parameters present.

Another performace tweak for this tactic is to only search the `impl` blocks for types that are new to us meaning that they were not
present in the last iteration.
This is a heuristic that speeds up the algorithm quite a bit as searching for all `impl` blocks is a costy operation.
However this optimization does suffer from the phase ordering problem.
For example it may happen that we can use some method from the `impl` block later when we have reached more types and covered a type that we need for an argument of the function.

One interesting aspect of Rust to note here is that even though we can query the `impl` blocks for type we still have to check that the receiver argument is of the same type.
This is because Rust allows also some other types that dereference to type of `Self` for the receiver argument#footnote(link("https://doc.rust-lang.org/reference/items/associated-items.html#methods")).
These types include but are not limited to `Box<S>`, `Rc<S>`, `Arc<S>`, `Pin<S>`.
For example there is a following method signatures for `Option<T>` type in standard library#footnote(link("https://doc.rust-lang.org/src/core/option.rs.html#715")).
```rs
impl<T> Option<T> {
    pub fn as_pin_ref(self: Pin<&Self>) -> Option<Pin<&T>> { /* ... */ }
}
```
As we can see from the snippet above the Type of `Self` in `impl` block is `Option<T>`.
However the type of `self` parameter in the method is `Pin<&Self>` which means that to call the `as_pin_ref` method we actually need to have expression of type `Pin<&Self>`.

We've also decided to ignore all the methods that return the same type as the type of `self` paremeter.
This is because they do not take us any closer to goal type and we've considered it unhelpful to show user all the possible options.
I've we'd allow them then we'd also receive expressions such as `some_i32.reverse_bits().reverse_bits().reverse_bits()` which is valid Rust code but unlikely something the user wished for. #todo("builder won't work, but here re good arguments for not to work anyway, order, lack of info")

==== Tactic "struct projection"
"Struct projection" is a simple tactic that attempts all field accesses of struct.
In a single iteration it only goes one level deep, but with multiple iterations we cover also all the fields of substructs.

This tactic highly benefitted from the use of BFS over DFS as the implementation for accessing all the fields of parent struct is rather trivial and with multiple iterations we get the full coverage including substruct fields.
With DFS the implementation was much more cumbersome as simple recurring on all the fields leaves out the the fields themselves.
As a result the implementation for DFS was about 2 times longer than the implementation for BFS.

As a performace optimization we only run this tactic on every type once.
For this tactic this optimization does not reduce the total search space covered as accessing the fields doesn't depend on rest of the search space covered.

==== Tactic "static method" <tactic-static-method>
"Static method" tactic attempts static methods of `impl` blocks, that is methods that are associated with either type or trait, but do not take `self` parameter.
One of the most common examples of static methods are `Vec::new()` and `Default::default()`.

As a performance optimization we qurey the `impl` block for types that we have previously queried from the lookup table but not found.
This is because we figured that the most common usecase for static methods is the factory method design pattern described in @design-patterns-elements-of-reusable-oo-software.
Similarly to "Impl method" tactic we ignore all the methods that have more than 1 generic parameter either at the `impl` or the method level.
The motivation is the same as for the "Impl method" tactic but as the static methods are more rare and we wanthed the tactic to also work on container types such as `Vec<T>` we decided to raise the thresold to 1.

= Results (week 7-8)

== Usability (week 8)

== Resynthesis (week 8)

= Future work (week 9)
#todo("Or after related work?")


= Related Work (week 9)
#todo("What here?
Kind of similar to what is in Background section.")
Maybe subsection to state of the art.

