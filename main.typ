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
#todo("More overview of rust, borrow checker model of types, what makes it safe. Not sure what to add tbh...")
Rust#footnote(link("https://www.rust-lang.org/")) is a new programming language for developing reliable and efficient systems.
The language was originally created by Mozilla for Firefox but is now gaining popularity and has found its way to the Linux kernel#footnote(link("https://lkml.org/lkml/2022/10/16/359")).
Rust has an expressive type system that guarantees no undefined behavior even though it has reference types.
This is done by rejecting all programs that may contain undefined behavior during the compilation.
We will call the set of programs that can be compiled valid, as they are guaranteed to not cause undefined behavior.
Many programming languages with type systems that guarantee the program to be valid have tools that help the programmer with term search i.e. by searching for valid programs (also called expressions in Rust) that satisfy the type system.
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


From the types of values in scope and constructors of `Option`, we can produce the expected result of wrapping the argument in `Option` and returning it.
By combining multiple type constructors as well as functions in scope or methods on types, it is possible to produce more complex valid programs.

== Motivation
Due to Rust having an expressive type system, the programmer might find themselves quite often wrapping the result of some function behind multiple layers of type constructors. For example, in the web backend framework `actix-web`#footnote(link("https://actix.rs/")), a typical JSON endpoint function might look something like shown in @motivation-example-1.
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

We can see that converting the result from the service to `FooResponse` and wrapping it in `Some(Json(...))` can be automatically generated just by making the types match.
This means that term search can be used to reduce the amount of code the programmer has to write.

In @how-programmers-interact-with-code-generation-models[p. 19] they suggest that code generation tools are used in two different modes.
1. They are used to reduce the amount of code the programmer has to write therefore making them faster.
  They call it the _acceleration mode_.
2. They are used to explore possible ways to complete incomplete programs.
  This is mostly used when the programmer is new to the libraries they are touching and is unsure how to continue.
  They call this usage pattern as _exploration mode_.
  
They found that both modes are common usage patters among programmers using large language model based code generation tools.
We argue that the same patterns can be found among programmer using term search.

In acceleration mode, term search is not as powerful as language models, but it can be more predictable as it has well-defined tactics that it uses rather than deep neural networks.
There is not so much "wow" effect - it just produces code that one could write by trying different programs that type-check.

However, we hope there is a bigger advantage for term search in _exploration mode_.
@how-programmers-interact-with-code-generation-models[p. 10] finds that programmers tend to explore only if they have confidence in the tool.
As term search only produces valid programs based on well-defined tactics, it is a lot easier to trust it than code generation based on language models that have some uncertainty in them.

== Research Objectives
The main objective of this thesis is to implement tactics-based term search for a programming language Rust.
Other objectives include:
- Evaluating the fitness of tactics on existing large codebases
- Investigating term search usability for autocompletion

== Contributions of the thesis
In this thesis we make following contributions:
1. In @background we give overview of term search algorithms used in other languages and autocompletion tools used in Rust and mainstream programming languages. We also introduce some aspects of Rust programming language that are relavant for the term search.
2. In @design we introduce term search to Rust by implementing it to the official language server of the Rust programming language. We discuss different usecases for it as well as the implementation details. In @tactics we describe the capabilities of our tool.
3. In @evaluation we evaluate the performance of the tool. We compare it to mainstream tools, some machine learning based methods and term search tools in other programming languages.
4. In @future-work we describe future work that would improve our implementation. This includes technical challenges, but also describes possible extensions to the algorithm.

= Background <background>
In this chapter we are taking a look at what the term search is, how is it used and how are the algorithms for it implemented in some of the tools we've chosen.
We will also take a look at the type system of the Rust programming language to see how it relates to type systems of other languages that have tools for term search.
In the end we'll briefly cover how autocomplete is implemented in modern tools to give some context of the framefork we are working in and tools what we are improving on.

== Term search <term-search>
Term search (often known as proof search) is generating programs (searching terms) that satisfy some type in given context.
It is often used in automated theorem proving.

The Curry-Howard correspondence is a direct correspondence between computer programs and mathematical proofs.
It is the basic idea in proof assistants such as Coq and Isabelle and also in dependently typed languages such as Agda and Idris.
The idea is to state a proposition as a type and then to prove it by producing a value of the given type as explained in @propositions-as-types.

For example, if we have addition on natural numbers defined in Idris as shown in @idirs-add-nat.
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
For that, we create a declaration `plus_reduces_Z` with the type of the proposition and prove it by defining a program that satisfies the type.
#figure(
sourcecode()[
```hs
plus_reduces_Z : (m : Nat) -> plus Z m = m  -- Proposition
plus_reduces_Z m = Refl                     -- Proof
```],
caption: [
    Prove $0 + n = n$ in Idris
  ],
) <idirs-plus-reduces-z>
The example above is quite trivial, as the compiler can figure out from the definition of `plus` that `plus Z m` is defined to be `m` according to first definition of `add`
Based on that we can prove `plus_reduces_Z` by reflexivity.
However, if there are more steps required, writing proofs manually gets cumbersome, so we use tools to automatically search for terms that inhabit a type ie proposition.
For example, Agda has a tool called Agsy that is used for term search, and Idris has this built into its compiler.

=== Term search in Agda
Agda @dependently-typed-programming-in-agda is a dependently typed functional programming language and also a proof assistant.
It is one of the first languages that has tools leveraging term search.
We'll be more interested in the proof assistant part of Agda as it is the one leveraging the term search to help the programmer with coming up with proofs. 
As there are many alternatives we've picked two that seem the most popular or relevant for our use case.
We chose Agsy as this is the well known tool that comes with Agda and Mimer that attempts to improve on Agsy.

==== Agsy <agsy>
Agsy is the term search based proof assistant that comes with Agda.
It was first published in 2006 in @tool-for-automated-theorem-proving-in-agda and integrated into Agda in 2009#footnote(link("https://agda.readthedocs.io/en/v2.6.4.1/tools/auto.html")).

We will be looking at the high level implementation of the algorithm used by Agsy for term search.

Agsy explores it's search space by using iterated deepening.
This is necessary since a problem may in general be refined to infinite depth.
The refinment of a problem can produce multiple branches with subproblems.
In some cases we need to solve all the subproblems but in other cases it is sufficent to solve just one to solve the "top-level" problem.

An example where we need to solve just one of the subproblems is when we try different approaches to come up with a term.
For example, we can either use some local variable, function or type constructor to solve the problem as shown in @agsy_transformation_branches.

#figure(
  image("fig/agsy_transformation_branches.svg", width: 60%),
  caption: [
    Agsy transformation branches
  ],
) <agsy_transformation_branches>

Some examples where we need to solve all the subproblems are using a type constructors that take multiple members or functions with multiple arguments.
In case of case splitting we also have to solve all the subproblems produced.
For example shown in @agsy_all_branches we see that function `foo(a: A, b: B, c: C)` can only be used if we manage to solve the subproblems of finding terms of correct type for all the arguments.

#figure(
  image("fig/agsy_all_branches.svg", width: 60%),
  caption: [
    Agsy branches for function call
  ],
) <agsy_all_branches>

Agsy uses problem collections (`PrbColl`) to model the subproblems that need to be all solved individually for the "top-level" problem to be solved.
Solution collections (`SolColl`) are used to keep track of solutions for particular problem collection.
Solution collection has a solution for each of the problems in a corresponding problem collection.

The intuition for the tool is following:
1. Given a problem we create set of possible subproblem collections out of which we need to solve one as show in @agsy_transformation_branches.
2. We attempt to solve all the subproblem collections by recursively solving all the problems in collection
3. If we manage to solve all the problems in collection we use it as a possible solution, otherwise we discard it as a dead end.

The algorithm itself is based around DFS and consists of two subfunctions.
Function $"search": "problem" -> ["solution"]$ is the main entry point that attempts to find a set of solutuions for a problem.
The function internally makes use of another function $"searchColl": "PrbColl" -> ["SolColl"]$ that attempts to find set of solution collections for a problem collection.
The pseudocode for the `search` and `searchColl` functions can be seen in @agsy-snippet.

We model Problem collection as a list of subproblems together with a _refinment_ that produces those problems.
Refinment is a recipe to transform the problem so that we get zero or more subproblems out for the input problem.
For example problem of finding a pair `(Bool, Int)` can be refined to two subproblems of finding `Bool` and finding `Int`.
In case we refine the problem without creating any new subproblems then we can call the problem solved.
Otherwise all the subproblems need to be solved for the solution to hold.
Refinment is stored so that on a successful solution we would know how to construct the solution term from the solution collection.

The `search` algorithm starts by refining the problem into new problem collections.
Refining is done by tactics that are essentially just a way of organising possible refinements.
An example tactic that attempts to solve the problem by filling it with locals in scope can be seen in @agsy-example-tactic.
// The example in the @agsy_transformation_branches contains three possible kinds if refinements for the problem: 1) Replace it with local (no new subproblems), 2) Replace it with function and create new subproblems for every argument, 3) Replace problem with a type constructor and create subproblem for all fields required by constructor.
Once we have the solution collections we attempt to solve them via the `searchColl` function.
Problem collections where we can't solve all the problems cannot be turned into solution collections as there is way to build well formed term with problems remaining in it.
As we only care about cases where we can fully solve the problem we discard them.
For the successful solution collections we substitute the refinments we took into the problem to get back solution.
As the solution is a well formed term with no remaining subproblems we return it.
In case there are no problem collections to solve we can call the problem to be trivially solved.
This acts as a "base case" for the algorithm.
In case there are problem collections but we cannot solve any of them then we cannot solve the problem so we return nothing instead of solution.

#figure(
sourcecode()[```hs
newtype ProbColl = (Refinment, [Problem])
newtype SolColl  = (Refinment, [Solution])

-- Find solutions to problem
search :: Problem -> Maybe [Solution]
search p = 
  let
    probColls: [ProbColl] = createRefs p
    solColls: [SolColl] = flatten [sc | Just sc <- map searchColl probColls]
    sols: [Solution] = map (\sc -> substitute sc p) solColls 
  in 
    case (probColls, sols) of
      ([],    _) -> Just TrivialSolution  -- No holes, trivially solved
      ( _,   []) -> Nothing
      ( _, sols) -> Just sols

-- Find solution to every problem in problem collection
searchColl :: ProbColl -> Maybe [SolColl]
searchColl = sequence $ fmap search

-- Create refinements for problem
createRefs :: Problem -> [ProbColl]
createRefs p = flatten [tactic1 p, tactic2 p, tacticN p]
```],
caption: [
    Agsy high level algorithm
  ],
) <agsy-snippet>

An example of tactic can be seen in @agsy-example-tactic.
#figure(
sourcecode()[```hs
-- Suggest locals for solving any problem
tacticLocal :: Problem -> [ProbColl]
tacticLocal p = 
  let locals = localsInScope p
  in
    map (\l -> (Refinment::SubstituteLocal p l, [])) $
    filter (\l -> couldUnify p l) locals
```
],
caption: [
    Agsy example tactic
  ],
) <agsy-example-tactic>

As described above the algorithm is built around DFS.
However, the authors of @tool-for-automated-theorem-proving-in-agda note that while the performance of the tool is good enough to be useful it performs poorly on larger problems.
They suggest that more advanced search space reduction techniques can be used as well as writing it in a language that does not suffer from automatic memory management.
It is also noted that there seems to be many false subproblems that can never be solved so they suggest a parallel algorithm that could potentially prove the uselessness of those subproblems potentially faster to reduce the search space.

==== Mimer
Mimer @mimer is another proof assistant tool for Agda that attempts to adresss some of the shortcomings in Agsy.
As of February 2024, Mimer has become part of Agda#footnote(link("https://github.com/agda/agda/pull/6410")) and will be released as a replacement for Agsy.
#todo("see if direct quote")
"Mimer is designed to handle many small synthesis problems rather than complex ones" @mimer.
Mimer is less powerful than Agsy as it doesn't perform case splits but on the other hand it is designed to be more rubust.
Other than not using case splits and the main algorithm follows the one used in Agsy and described in @agsy.

The main differences to original Agsy implementation are:
1. Mimer uses memoization to avoid searching for same term multiple times.
2. Mimer guides the search with branch costs

Branch costs is a heuristic to hopefully guide the search to an answer faster that randomly picking branches.
Mimer gives lower cost to branches that contain more local variables and less external definitions.
The rationale for that is that it is more likely that user wishes to use variables from local scope than from outside of it.
However, they noted that the costs for the tactics need to be tweaked in future work as this was not their focus.

=== Term search in Standard ML <standardml>
As a part of the RedPRL#footnote(link("https://redprl.org/")) @redprl project, @algebraic-foundations-of-proof-refinement implements term search for Standard ML.

The algorithm suggested in @algebraic-foundations-of-proof-refinement keeps track of subproblems in an ordered sequence in which each induces a variable of the appropriate sort which the rest of the sequence may depend on.
This sequence is also called a telescope @telescopic-mappings-typed-lamda-calc.
The telescope is required to work on type systems with dependent types.
In contrast, typesystems without dependent types can use ordinary `List` data structure as there are no relations between subproblems.

To more effectively propagete substitutions to subproblems in telescope @algebraic-foundations-of-proof-refinement suggests to use BFS instead of DFS.
The idea is to run all the tactics once on each subproblem, repeatedly.
This way substitutions propagate along the telescope of subproblems after every iteration.
In the case of DFS we would propagate the constraints only after exhausting the search on the first subproblem in the sequence.
To better understand the difference between the BFS approach suggested and DFS approach lets see how each of them work.

First let's consider the DFS approach as a baseline.
The high level algorithm for DFS is to first generate possible ways of how to refine the problem into new subproblems and then solving each of the subproblems fully before contiuing to next subproblem. 
In the snippet below tactics create problem collections that are options we can take to refine the problem into new subproblems.
After that we attempt to solve each set of subproblems to find the first problem collection where we manage to solve all the subproblems.
That problem collection effectively becomes our solution.
In @standardml-dfs-code we can see that the DFS fits functional style very well as for all the subproblems we can just recursively call the same `solve` function again.
Note that in the listing the constraints are propagated to remaining problemss only after problem is fully solved.
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

Now lets look at how the BFS algorithm suggested in @algebraic-foundations-of-proof-refinement works.
The high level algorithm for BFS is to generate possible ways to refine the problem into new subproblems and then incrementally solve all the subproblems in parallel.
The pseudocode for it can be seen in @standardml-bfs-code.

The algorithm starts by converting the given problem to singelton problem collection.
Now the produced collection is fed into `solveBFS` function that starts incrementally solving the problem collections.
In the example we are using queue to keep track of the problem collections we are solving.
Internally the `solveBFS` function loops over the elements of the queue until either a solution is found or the queue becomes empty.
In the snippet we check the status of the problem collection with a `status` function that tells us the status of the problem collection.
The status is either
 - *AllSolved* for problem collections that do not have any unresolved subproblems in them and are ready to be converted into solutions.
 - *NoSolution* for problem collections that have remaining unresolved subproblems that we are unable to make any progress on.
 - *RemainingProblems* for all the problem collections that we can make progress on by incrementally stepping the problem further.
 In case of `AllSolved` we return the solution as we are done with the search.
 In case of `NoSolution` we discard the problem from the queue.
 Otherwise (in case of `RemainingProblems`) we step the problem collection at the head of the queue and push the results back to the back of the queue.
 Now we are ready to keep iterate the loop again with the new problem collection at the head of the queue.

 Stepping the problem collection steps (or adds atomic refinements) to all problems in the problem collection and propagates the constrainst to rest of the subproblems if refinements produce any new constraints.
 As the problem can generally refined in multiple ways the function returns a list of problem collections that are all possible successors of the input problem collection.
 Propagating the constrains is done in `propagateConstraints` function.
 The function adds new constraints arising form the head element refinements to all subproblems in the problem collection.

#figure(
sourcecode()[```hs
solve :: Problem -> Maybe Solution
solve problem = 
  let 
    pcs: [ProblemCollection] = toSingeltonCollection problem
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

Consider the example where we are searching for a goal `?goal :: ([a], a -> Integer)` that is a pair of a list of some type and a function of that type to `Integer`.
Similar goals in real word could arrise from finding a list together with a function that can map the elements to integer to sum them.
Another example where dependent goals arise would be a list together with a finction to print all the elements.

Note that in this example we want the first member of pair to be list but we do not care of the types inside the list.
The only requirement is that the second member of pair can map the same type to integer.
We have following items in scope:
#todo("maybe int to string, aka show")
```hs
bar : Bar
mk_foo : Bar -> Foo
mk_list_foo : Foo -> [Foo]
mk_list_bar : Bar -> [Bar]
bar_to_int  : Bar -> Integer
```

To simplify the notation we will name the goals as `?<number>`, for example `?1` for goal 1.

First we can split the goal of finding a pair to two subgoals `[?1 : [a], ?2 : a -> Integer]`.
This is the same step for BFS and DFS as there is not much else to do with `?goal` as there are now functions
that take us to pair of any types exept using pair constructor.
At this point we have two subgoals to solve
```hs
(?1 : [a], ?2 : a -> Integer)
```

Now we are at where the differences between DFS and BFS start playing out.
First let's look at how the DFS would handle the goals.
First we focus on `?1`.
We can use `mk_list_foo` to transform the goal to finding of something of type `Foo`.
Now we have the following solution and goals.

```hs
(mk_list_foo(?3 : Foo), ?2 : a -> Integer)
```

Note that although the `a` in `?s2` has to be of type `Foo` we do not propagate this knowledge there yet as we are focusing on `?3`.
We only propagate the constrains when we discard the hole as filled.
We use `mk_foo` to create new goal `?4 : Bar` which we solve by providing `bar`.
Now we propagate the constraints to the remaining subgoals, `?2` in this example.
This means that the second subgoal becomes `?2 : Foo -> Integer` as shown below.

```hs
(mk_list_foo(mk_foo(?4 : Bar), ?2 : a -> Integer)
(mk_list_foo(mk_foo(bar)), ?2 : Foo -> Integer)
```
However, we cannot find anything of type `Foo -> Integer` so we have to revert all the way to `?1`.
This time we use `mk_list_bar` to fill `?1` meaning that the remaining subgoal becomes `?2 : Bar -> Integer`.
We can fill it by providing `bar_to_int`.
As there are no more subgoals remaining the problem is solved with the steps shown below.

```hs
(mk_list_bar(?3 : Bar), ?2 : a -> Integer)
(mk_list_bar(bar), ?2 : Bar -> Integer)
(mk_list_bar(bar), bar_to_int)
```

An overview of all the steps we took can be seen in the @standardml-dfs-steps.
#figure(
sourcecode()[```hs
?goal : ([a], a -> Integer)
(?1 : [a], ?2 : a -> Integer)
(mk_list_foo(?3 : Foo), ?2 : a -> Integer)
(mk_list_foo(mk_foo(?4 : Bar), ?2 : a -> Integer)
(mk_list_foo(mk_foo(bar)), ?2 : Foo -> Integer) -- Revert to ?1
(mk_list_bar(?3 : Bar), ?2 : a -> Integer)
(mk_list_bar(bar), ?2 : Bar -> Integer)
(mk_list_bar(bar), bar_to_int)
```],
caption: [
    DFS algorithm steps
  ],
) <standardml-dfs-steps>

Now let's take a look at the algorithm that uses BFS for to handle the goals.
The first iteration is the same as described above after which we have two subgoals to fill.
```hs
(?1 : [a], ?2 : a -> Integer)
queue = [[?1, ?2]]
```

As we are always working on the head element of the queue we are still working on `?1`.
Once again we use `mk_list_foo` to transform the first subgoal to `?3 : Foo` but this time we also insert another problem collection to the queue where we use `mk_list_bar` instead.
We also propagate the information to other subgoals so that we constrain `?2` to either `Foo -> Integer` or `Bar -> Integer`.
```hs
(mk_list_foo(?3 : Foo), ?2 : Foo -> Integer)
(mk_list_bar(?4 : Bar), ?2 : Bar -> Integer)

queue = [[?3, ?2], [?4, ?2]]
```

In the next step we search for something of type `Foo` for `?3` and a function of type `Foo -> Integer` in `?2`.
We find `bar` for the first goal, but not anything for the second goal.
This means we discard the branch as we are not able to solve the problem collection.
Note that at this point we still have `?4` pending, meaning we have not yet exhausted the search in current "branch".
Reverting now means that we save some work that was guaranteed to have no effect on the overall outcome.
The search space becomes
```hs
(mk_list_foo(mk_foo(?4 : Bar)), ?2 : <impossible>) -- discarded
(mk_list_bar(?4 : Bar), ?2 : Bar -> Integer)

queue = [[?4, ?2]]
```
Now we focus on the other problem collection.
In this iteration we find solutions for both of the goals as following.
As all the problems in the problem collection get get solved we can turn it into solution and return it.
```hs
(mk_list_bar(?5 : Bar), ?2 : Bar -> Integer)
(mk_list_bar(bar), bar_to_int)
```

An overview of all the steps we took can be seen in @standardml-bfs-steps. #todo("this is confusing for parallel stuff tho")
#figure(
sourcecode()[```hs
?goal : ([a], a -> Integer)
(?1 : [a], ?2 : a -> Integer)
(mk_list_foo(?3 : Foo), ?2 : Foo -> Integer)
(mk_list_foo(mk_foo(?4 : Bar)), ?2 : <impossible>) -- Discard branch
(mk_list_bar(?5 : Bar), ?2 : Bar -> Integer)
(mk_list_bar(bar), bar_to_int)
```],
caption: [
    DFS algorithm steps
  ],
) <standardml-bfs-steps>

In the example above we see that BFS and propagating constraints to other subgoals can help us cut some search branches to speed up the search.
However, this is not always the case.
BFS is faster only if we manage to cut the proof before exhausting the search at the current goal.
In case the first goal we focus at cannot be filled DFS is faster as it doesn't do any work on filling other goals.

=== Term search in Haskell
Wingman#footnote(link("https://hackage.haskell.org/package/hls-tactics-plugin-1.6.2.0")) is a plugin for Haskell Language Server that provides term search.
For term search Wingman uses library called Refinery#footnote(link("https://github.com/TOTBWF/refinery")) that is also based on @algebraic-foundations-of-proof-refinement similarly to the Standard ML tool we described in @standardml.

As we described the core ideas in @standardml we won't cover them here.
However, we will take a look at some implementation details.

The most interesting implementation detail for us is how BFS is achieved.
Refinery uses interleaving of subgoal generated by each tactic to get the desired effect.
Let's look at the example to get a better idea what is going on.
Suppose that at some point of the term search we have three pending subgoals: `[`#text(red)[`?1`]`, ?2, ?3]` and we have some thactic that prduces two new subgoals `[`#text(blue)[`?4`]`, `#text(blue)[`?5`]`]` when refining #text(red)[`?1`].
The DFS way of handling it would be
#block()[
`[`#text(red)[`?1`]`, ?2, ?3] -> tactic -> [`#text(blue)[`?4`]`, `#text(blue)[`?5`]`, ?2, ?3]`
]
However with interleaving the goals are ordered in the following way
#block()[
`[`#text(red)[`?1`]`, ?2, ?3] -> tactic -> [?2, `#text(blue)[`?4`]`, ?3, `#text(blue)[`?5`]`]`
]
Note that there is also a way to insert the new goals to back of the goals list which is the BFS way.
#block()[
`[`#text(red)[`?1`]`, ?2, ?3] -> tactic -> [?2, ?3, `#text(blue)[`?4`]`, `#text(blue)[`?5`]`]`
]
However in Refinery they have decided to go with interleaving as it works well with tactics that produce infinite amounts of new holes due to not making any new process.
Note that this works especially well because of the lazy evaluation in Haskell.
In case of eager evaluation the execution would still halt on producing all the subgoals, so interlining would have now effect.


=== Term search in Idris2
Idris2 is a dependently typed programming language that has term search built into it's compiler.
Internally the compiler makes use of a small language they call TT.
In @idris2-design-and-implementation they say that TT is a dependently-typed λ -calculus with inductive families and pattern matching definitions.
The language is kept as small as reasonably possible to make working with it easier.

As the term search algorithm also works on TT we'll take a closer look at it.
More precise we'll look at they call $"TT"_"dev"$ that is TT, but extended with hole and guess bindings.
The guess binding is similar to a let binding, but without any reduction rules for guess bindings.
In @idris2-design-and-implementation they note that using binders to represent holes is useful in a dependently-typed setting since one value may determine another.
Attaching a guess (generated term) to a binder ensures that instantiating one such variable also instantiates all of its dependencies

$"TT"_"dev"$ consists of terms, bindings and constants as shown in @idris-tt-syntax.
#todo("reference idris paper for the figure")
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
    $"TT"_"dev"$ syntax
  ],
) <idris-tt-syntax>

Idris2 makes use of priority queue of hole and guess binders to keep track of subgoals to fill.
The goal is considered filled once the queue becomes empty.

In the implementation, the proof state is captured in an elaboration monad, which is a state monad with exceptions.
The general flow of the algorithm is following:
1. Create a new proof state
2. Run series of tactics to build up the term
3. Recheck the generated term

Proof state contains the context of the problem (local and global bindings), the proof term, unsolved unification problems and the holes queue.
The main parts of the state that change during the proof search are the holes queue and sometimes the unsolved unification problems.
Holes queue changes as we try empty it by filling all the holes.
Unsolved unification problems only changes if new information about unification comes available when instanciating terms in the proof search.
For example we may have unification problem `Unify(f x, Int)` that cannot be solved without further without new information.
Only when we provide some concrete `f` or `x` the problem can be solved further.

Tactics in Idris2 operate on the sub-goal given by the hole at the head of the hole queue in the proof state.
All tactics run relative to context which contains all the bindings in scope.
They take a term (that is hole or guess binding) and produce new term that is of suitable type.
Tactics are also allowed to have side effects that modify proof state.

Next let's take a look at the primitive building blocks that are used by tactics to create and fill holes.

Operation `claim` is used to create new holes in the context of current hole.
The operation creates new hole binding to the head of the holes queue.
Note that the binding is what associates the generated hole with the current hole.

Operation `fill` is used to fill a goal with value. 
Given value `v` the operation attempts to solve the hole by creating a guess binder with `v`.
It also tries to fill other goals by attempting to unifying `v` with the types of holes.
Note that the `fill` operation does not destroy the hole yet as the guess binding it created is allowed to have more holes in it.

To destroy holes, operation `solve` is used.
It operates on guess bindings and checks if they contain any more holes.
If they don't, then the hole is destroyed and substituted with the value from guess binder.

The two step process, with `fill` followed by `solve`, allows the elaborator to work safely with incomplete terms.
This way incomplete terms do not affect other holes (by adding extra constraints) until we know we can solve them.
Once a term is complete in a guess binding, it may be substituted into the scope of the binding safely.
In each of these tactics, if any step fails, or the term in focus does not solve the entire tactic fails.
This means that it roughly follows the DFS approach described in @standardml.


=== Term search in Elm with Smyth
Smyth#footnote(link("https://uchicago-pl.github.io/smyth/")) is a system for program sketching in a typed functional language, approximately Elm.
In @smyth, they describe that it uses evaluation of ordinary assertions that give rise to input-output examples, which are then used to guide the search to complete the holes.
Symth uses type and example directed synthesis as opposed to other tools in Agda only using type guided search for terms.
The general idea is to search for terms that satisfy the goal type as well as example outputs for the term given in assertions.
It is also based on a DFS, but is optimized for maximal use memoization.
The idea is to maximize the amount of terms that have same typing environment and can therefore be reused.
This is done by factorizing the terms into smaller terms that carry less context with them.
Smyth has many other optimizations, but they focus on using the information from examples and are therefore not interesting for us as they focus on optimizing the handling of data provided by examples.

== Program synthesis in Rust
RusSol is a proof of concept tool to synthesize Rust programs from both functiond declarations and pre- and postconditions.
It is based on separation logic as described in @rust-program-synthesis, and it is the first synthesizer for Rust code from functional correctness specifications.
Internally it uses SuSLik’s general-purpose proof search framework. #footnote(link("https://github.com/JonasAlaif/suslik")).
RusSol itself is implemented as a extension to rustc, the official rust compiler.
It has separate command line tool, but internally it reuses many parts of the compiler.
Although the main use case for RusSol is quite different from our use case it shared a lot of common ground.

The idea of the tool is to specify function declaration as following and then run the tool on it to synthesize the program to replace the `todo!()` macro on line 5 in @russol-input.

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
From the preconditions (`requires` macro) and postconditions (`ensures` macro) it is able to synthesize the body of the function.
For the example in @russol-input the output is shown in @russol-output.
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
It can also insert `unreachable!()` macros to places that are never reached during the program execution.

RusSol works on the HIR level of abstraction.
It translates the information from HIR to separation logic rules that SuSLik can understand and feeds them into it.
After getting back successful response it turns the response back into Rust code as shown in @russol-workflow.
#figure(
  image("fig/russol-suslik.png", width: 100%),
  caption: [
    "RusSol workflow" by @rust-program-synthesis / #link("https://creativecommons.org/licenses/by/4.0/ ")[CC BY 4.0]
  ],
) <russol-workflow>

All the programs synthesized by RusSol are guaranteed to be correct by construction.
This is achieved by extracting the programs from separation logic derivations.
However, in @rust-program-synthesis they noted that they cannot prove the correctness of separation logic rules for Rust as at this point rust lacks formal specification.
Nevertheless, the tool was tested on 100 different crates and managed to always produce valid code.

As the tool uses external engine to synthesize the programs we will not dive into its inner workings.
However, we will take a look at the notes by the authors of @rust-program-synthesis as they are very relevant also for us.

The authors found that quite often the types are descriptive enough to produce useful programs and the pre- and postconditions are not required.
This aligns with our intuition of synthesizing terms from types can be useful in practice.

The authors of RusSol pointed out the main limitations of the tool are:
1. It does not support traits
2. It does not support conditionals as it lacks branch abduction
3. It does not synthesize arithmetic expressions
4. It does not support `unsafe` code

They also noted that first three of them can be solved with some extra engineering effort, but the last one requires more fundamental changes to the tool.

From the benchmarks on top 100 crates on crates.io it was measured that it takes about 0.5s on average to synthesize non-primitive expressions.
Quite often the synthesis time was 2-3s and sometimes reached as high as 18.3s.
This is fast enough to use for filling holes, but too slow to use for autocompletion.

== The Rust language
Rust is a general-purpose systems programming language first released in 2015#footnote(link("https://blog.rust-lang.org/2015/05/15/Rust-1.0.html")).
It takes lots of inspiration from functional programming languages, namely, it supports algebraic data types, higher-order functions, and immutability.

=== Type unification in Rust
Rust has multiple different kinds of types.
There are primitives, references, abstract data types, generics, lifetimes, alias types, and more.
It is possible to check for either syntactic or semantic equality between two types.
Syntactic equality is very conservative compared to sematic equality as it requires to items to be exactly the same.
This can sometimes be a problem as in Rust high-level intermediate representation (HIR), there are multiple ways to define a type.
For example, in `let x: i32 = 0;` the type of `x` and the type of literal `0` are not syntactically equal.
However their types are semantically the same as `0` is inferred to have the type `i32`.

To check for semantic equality of types we see if two types can be unified.
Rust's type system is based on a Hindley-Milner type system @affine-type-system-with-hindley-milner, therefore the types are compared in a typing environment.
In rust traint solver is responisble for checking unification of types#footnote(link("https://rustc-dev-guide.rust-lang.org/ty.html")).
The trit solver works at the HIR level of abstraction and it is heavily inspired by Prolog engines.
The trait solver uses "first-order hereditary harrop" (FOHH) clauses, which are horn clauses that are allowed to have quantifiers in the body @proof-procedure-for-the-logic-of-hereditary-harrop-formulas.
To check for unification of types, we first have to normalize to handle type projections #footnote(link("https://rust-lang.github.io/chalk/book/clauses/type_equality.html")).
In @rust-type-projections, all `Foo`, `Bar` and `Baz` are different projections to the type `u8`.
#figure(
sourcecode()[
```rs
type Foo = u8; // Type alias

impl SomeTrait for u8 {
  type Bar = u8;   // Associated type
  type Baz = Self; // Associated type with extra level of indirection
}
```],
caption: [
    Type projections in Rust
  ],
) <rust-type-projections>
Normalization is done in the context of typing environment.
First we register clasuses provided by the typing environment to the trait solver.
After that we register a new inference variable in and then we solve for it.
A small example of normalizing the `Foo` type alias from the program above can be seen in @rust-normalizing.
#figure(
sourcecode(numbering: none)[```txt
AliasEq(Foo = u8)
Projection(Foo, ?normalized_var)  <- normalized_var is constrained to u8 after solving
```],
caption: [
    Normalizing types in Rust
  ],
) <rust-normalizing>
Not all types can be fully normalized.
For example, consider the function below.
```rs
fn foo<T: IntoIterator>(...) { ... }
```
In this example, there is now a way to know the exact type of `T`.
In that case, we use placeholder types, and later there will be an extra obligation to solve that the placeholder type is equal to some actual type.
This is also known as lazy normalization, as the normalization is only done on demand.

To check if types `X` and `Y` unify, we register a new obligation `Eq(X = Y)`.
To continue the example above and check if `Foo` unifies with `u8`, we register `Eq(Foo = u8)`.
Now we try to solve for it.
Solving is done by the prolog like engine, that tries to find solution based on the the clauses we've registred.
If contradiction is found between the goal and clauses registered from the typing environment then there is no solution.
In other words this means that the types do not unify.
On successful solution we are given a new set of subgoals that still need to be proven.
If we manage to recursively prove all the subgoals, then we know that the unify.
If some goals remain unsolved but there is also no contradiction, then simply more information is needed to guarantee unification.
How we treat the last case depends on the use case, but in this thesis, for simplicity, we assume that the types do not unify.

=== Borrow checking
Another crucial step for the Rust compiler is borrow checking#footnote(link("https://rustc-dev-guide.rust-lang.org/borrow_check.html")).
The main responisbilities for the borrow checker are to make sure that:
- All variables are initialized before being used
- No value is moved twice or used after being dropped
- No value is moved while borrowed
- No immutable variable can be mutated
- There can be only one mutable borrow

The borrow checker works at the Middle Intermediate Representation (MIR) level of abstraction.
The currently used model for borrows is Non-Lexical Lifetimes (NLL).
The borrow cheker first builds up a control flow graph to find all possible data accesses and moves.
Then it builds up constraints between lifetimes.
After that, regions for every lifetime are built up.
A region for a lifetime is a set of program points at which the region is valid.
The regions are built up from constraints:
- A liveness constraint arises when some variable whose type includes a region R is live at some point P. This simply means that the region R must include the point P.
- Outlives constraint `'a: 'b` means that the region of `'a` has to also be a superset of the region of `'b`.
From the regions, the borrow checker can calculate all the borrows at every program point.
An extra pass is made over all the variables, and errors are reported whenever aliasing rules are violated.

Rust also has a concept of two-phased borrows that splits the borrow into two phases: reservation and activation.
These are used to allow nested function calls like `vec.push(vec.len())`.
These programs would otherwise be invalid, as in the example above `vec.len()` is immutably borrowed while `vec.push(...)` takes the mutable borrow.
The two-stage borrows are treated as follows:
- It is checked that no mutable borrow is in conflict with the two-phase borrow at the reservation point (`vec.len()` for the example above).
- Between the reservation and the activation point, the two-phase borrow acts as a shared borrow.
- After the activation point, the two-phase borrow acts as a mutable borrow.

There is also an option to escape the restrictions of borrow checker by using `unsafe` code blocks.
In an `unsafe` code block, the programmer has the sole responsibility to guarantee the validity of aliasing rules with no help from the borrow cheker.


== Autocompletion
Autocompletion is predicting of what the user is typing and then suggesting the predictions to user.
In case of programming the suggestions are usually derived form context and may be just a words from current buffer or maybe functions reachabele in the current context.
It is nowadys cosidered one of the basic features that any integrated development environment (IDE) has built in.

We will explore the LSP protocol in @lsp-protocol to have the basic understanding of the constraints and features of the framework we are working in.
This is essensial to later undersand some of our design choises for implementation later described in @design.

Lets take a look at some of the poplular autocompletion tools and their autocompletion related features to give some ituition of what is the common approach for implementing them.
We'll be mostly looking at what kind of sematic information the tools use to provide suggestions.

==== Clangd
Clangd#footnote(link("https://clangd.llvm.org/")) is one of the most used autocompletion tools for C/C++.
It is a LSP server extension to clang compiler and therefore can be used in many editors.
It suggests functions, methods, variables, etc are available in the context and it can handle some mistypings and abbreviations of some words.
For example using snake case instead of camel case still yields suggestions.

For method calls it does understand the receiver type and only suggests methods/fields that exist on the type.
However it does not try to infer the expected type of the expression that is being completed and therefore is unable to prioritize methods based on that.
All in all it serves as a great example of autocompletion tool that has semantic understanding of the program, but does not provide any functionality beyond basics.

==== Pyright
Pyright#footnote(link("https://github.com/microsoft/pyright")) is one of the most used autocompletion tools for Python.
It is another LSP server to provide the functionality for muliple IDEs.
It suggests all the item that are available in scope for autocompletion and it also suggests the methods/fields that are on the receiver type.

Whilst it tries to provide more advanced features than clangd it does not get much further due to python being dynamically typed language.
There simply isn't that much information available before running the program.
This seems to be a general limitation to all python autocompletion tools.

==== Intellij
Intellij#footnote(link("https://www.jetbrains.com/idea/")) is a IDE by JetBrains for Java.
Similarly to all other JetBrains products it does not use LSP but rather has all the tooling built into the product.
It provides the completion of all the items in scope as well the methods/fields of receiver type.
They call it the "basic completion﻿".
The tool has also understanding of expected type so it attempts to order the suggestions based on their types.
This means that suggestions with expected type appear first in the list.

In addition to "basic completion" they provide "type-matching completion﻿" that is very similar to basic completion but filter out all the results that do not have matching type.
There is also what they call "chain completion" that expands the list to also suggest chained method calls.
Together with filtering out only matching types it gives similar results to what term search provides.
However as this is implemented in a different way it's depth is limited to two which makes it less useful.
It also doesnt' attempt to automatically fill all the arguments so it works the best with functions that take no arguments.
For Java it is quite useful nontheless as there are a lot of getter functions.

In some sense the depth limit to two (or three together with the receiver type) is mainly a technical limitation but it is also caused by Java using interfaces a in different way that what Rust does with traits.
Interfaces in Java are meant to hide internal representation of classes which in some cases limits what we can provide just based on types.
For example if we are expected to give something theat implements `List` we cannot really prefer `ArrayList` to `LinkedList` just based on types.
More common usage of satic dispatch in Rust means that we more often know the concrete type and therefore can also provide more accurate suggestions based on it.
In Java there is often not enough information to suggest longer chains as there are likely too many irrelavant suggestions.

==== Rust-analyzer <rust-analyzer>
Rust-analyzer#footnote(link("https://rust-analyzer.github.io/")) s an implementation of Language Server Protocol for the Rust programming language. 
It provides features like completion and goto definition/references, smart refactorings etc.
This is also the tool we are extending with term search functionality.

Rust-analyzer provides all the "basic completions" that IntelliJ provides and also supports ordering suggestions by type.
However it does not support method chains so in that regard it is less powerful than IntelliJ for Java.
Filtering by type is also not part of it but as it gathers all the information to do it so it can be implemented rather trivially.

Other than autocompletion it does have interesting concept of typed holes.
They are `_` (underscore) characters at expression positions that cause the program to be rejected by the compiler.
Rust-analyzer treats them as holes in the program that are supposed to become terms of correct type to make the program valid.
Based on that concept it suggest filling them with variables in scope which is very similar to what term search does.
However, it only suggest trivial ways of filling holes so we are looking to improve on it a lot.

=== Language Server Protocol <lsp-protocol>
Implementing autocompletion for every language and for every IDE results in a $O(N * M)$ complexity where N is the number of languages supported and M is the number of IDEs supported.
In other words one would have to write a tool for every language-IDE pair.
This problem is very similar to problem in compilers design with N languages and M target archidectures.
As they describe in @compiler-design the $O(N*M)$ can be reduced to $O(N+M)$ by sepparating the compiler to front and back end.
The idea is that there is a unique front end for every language that lowers the language specific constructs to intermediate representation that is a common interface for all of them.
To get machine code out of the intermediate representation there is also a unique back end for every target archidecture.

Similar ideas can be also used in building language tooling.
Language server protocol (LSP) has been invented to do exactly that.
The Language Server Protocol#footnote(link("https://microsoft.github.io/language-server-protocol/")) (LSP) is an open, JSON-RPC-based#footnote(link("https://www.jsonrpc.org/specification")) protocol for use between editors and servers that provide language specific tools for a programming language.
The protocol takes the position of intermediate representation, front ends are the LSP clients in IDEs and backends are LSP servers.
We will refer to LSP client as just client and LSP server as just server.
As the protocol is standardised every client knows how to work with any server.
LSP was first introduced to public in 2016 and now now most#footnote(link("https://microsoft.github.io/language-server-protocol/implementors/tools/")) modern IDEs support it.

Some of the most common functionalities LSP servers provide according to @editing-support-for-languages-lsp:
- Go to definition / references
- Hover
- Diagnostics (warnings / errors)
- Autocompletion
- Formatting
- Refactoring routines (extract function, etc.)
- Semantic syntax highlighting

The the high level communication of client and server is show in @lsp-data-flow.
The idea is that when the programmer works in the IDE the client sends all text edits to server.
The server can then process the updates and send new autocompletion suggestion / syntax highlighting / diagnostics back to client so that it can update the  information in IDE.
#figure(
  image("fig/lsp_data_flow.svg", width: 100%),
  caption: [
    LSP communication
  ],
) <lsp-data-flow>
Important thing to note here is that the  client starts the server the first time it requires data from it.
After that the server runs as daemon process usually until the editor is closed or until the client commands it to shut down.
As it doesn't get restarted very often it can keep the state in memory which allows responding to client events faster.
It is quite common that the server does semantic analysis fully only once and later only runs the analysis again for files that have changed.
Cacheing the state and incrementally updating it is quite important as the full analysis can take up to considerable amount of time which is not an acceptable latency for autocompltion nor for other operations servers provide.
In @editing-support-for-languages-lsp they describe that caching the abstract syntax tree is the most common performance optimization strategy for servers.

== Machine learning based autocompletions <machine-learning>
In this chapther we will take a look at machine learning based autocompletion tools.
As this is a very active field of development we are not competing against we will not dive into how good this or other models perform but rather look at what the models generally do.
The main focus is to see how do they differ from the analytical approach we are taking with term search.

In @code-prediction-trees-transformers they state that one of the most obvious usecases for machine learning is to order the suggestions.
They state that the using a model for ordering the suggestions is escpecially useful in dynamically typed languages as it is otherwise rather hard to order suggestions.
Although the Rust language has strong type system we still suffer from prioritizing differenent terms that have the same type.

In addition to ordering the analytically created suggestions macine learning models can be used to generate code itself.
For example in @pre-trained-llm-code-gen they introduce a model that can generate code for up to 23 different programming languages.
The general flow is that when the user has written the function signature and maybe some human readable documentation for the function they can prompt the model to generate the body for the function.
This is very different from ordering suggestions as the suggested code usually has many tokens in in whilst the classical approach is usually limited to on or sometimes very few tokens.
This is also different from what we are doing with the term search.
In the case of term search we only try to produce code that some contributes towards the parent term of correct type.
However language models can also generate code that do not contribute towards finding the goal type.
Lets look at the example for the `ripgrep`#footnote(link("https://github.com/BurntSushi/ripgrep/blob/6ebebb2aaa9991694aed10b944cf2e8196811e1c/crates/core/flags/hiargs.rs#L584")) crate shown in @rust-builder.
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
    Builder pattern in Rust
  ],
) <rust-builder>
As we can see from the changes of type added in comments the type of the term only changes on the first and last line of the function body.
As the lines in the middle do not affect the type of the builder in any way there is also no way for the term search to generate them.
Machine learning models however are not affected by this as it may be possible to derive those lines from the function docstring, name or rest of the context.

Although the machine learning models are able to generate more complex code they have also downside of having lots of uncertanity in them.
It is vary hard to impossible for any human to understand what are the outputs for any given input.
In the context of code generation for autocompletion this results in unexpected suggestions that may even not compile.
These issues are usually adressed by filtering out syntactically invalid responses or working at the level of abstract syntax tree as they did it in @code-prediction-trees-transformers.
However neither of those accounts for type nor borrow checking which means that invalid programs can still be occasionally suggested.


= Term search design <design>
Before diving into the technical aspects of term search implementation, we will first explore it by giving
examples of its usages in `rust-analyzer`. 
We will first take a look at using it for filling "holes" in the program and later dive into using it for autocompletion.

== Filling holes
Filling holes is a common use case for term search as we've found in @term-search.
Timing constrains for it are not as strict as for autocompletion, yet the user certainly doesn't want to wait for a considerable amount of time.

One of the most known examples of holes in Rust programs is the `todo!()` macro.
It is a "hole" as it denotes that there should be a program in the future, but there isn't now.
These holes can be filled using term search to search for programs that fit in the hole.
All the programs generated by term search are valid programs meaning that they compile.

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

In addition to `todo!()` macro holes `rust-analyzer` has a concept of typed holes as we described in @rust-analyzer.
From term search perspective they work in the same way as `todo!()` macros - term search needs to come up with a term of some type to fill them.
The same example with typed holed instead of `todo!()` macros can be found in @rust-filling-typed-hole.
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


== Autocompletion
In addition to filling holes, term search can be used to give user "smarter" autocompletion suggestions as they are typing.
The general idea is the same as for filling holes.
We start by attempting to infer the expected type at the cursor.
If we manage to infer the type then we run the term search in order to get the suggestions which we can then show to the user.

The main difference between using term search for autocompletion and using it to fill holes is that we've decided to disable borrow checking when generating suggestions for autocompletion.
This means that not all the suggestions are valid programs and may need some modifications by user.

The rationale for it comes from both technical limitations of the tool as well as different expectations from the user.
The main techincal limitation is that borrow checking happens in the MIR layer of abstraction and `rust-analyzer` (nor `rustc`) does not support lowering partial (user is still typing) programs to MIR.
This means that borrow checking is not really possible without big modifications to the algorithm.
That however is out of scope of this thesis.

In addition to technical limitations, there is also some motivation from user perspective for the tool to give also suggestions that do not borrow check.
In @usability-of-ownership they found that it is very common that the programmer has to restructure the program to satisfy the borrow checker.
The simplest case for it is to either move some lines around in function or to add `.clone()` to avoind moving the value.
For example consider @rust-autocompletion with the cursor at `|`:
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
The user want's to also pass `my_string` to `bar(...)` but this does not satisfy the borrow checking rules as the value was moved to `foo(...)` on the previous line.
The simplest fix for it is to change the previous line to `foo(my_string.clone())` so that the value is not moved.
This however can only be done by the programmer as there are also other ways to solve it, for example making the functions take the reference istead of value.
As also described in @usability-of-ownership the most common way to handle borrow checker errors is to write the code first and then fix the errors as they come up.
Inspired by this we believe that is better to suggest items that make the program do not borrowcheck than not suggest them at all.
If we only suggest items that borrow check the `bar(my_string)` function call would be ruled out as there is no way to call it without modifying the rest of the program.


== Implementation
We've implemented term search as an addition to `rust-analyzer`, the official LSP client for the Rust language.
To have better understanding of the context we are working in we will first diescribe the main operations that happen in `rust-analyzer` in order to provide autocompletion or code actions (filling holes in our use case).

When the LSP server is started, `rust-analyzer` first indexes whole project, including it's dependencies as well as standard library.
This is rather time consuming operation.
During indexing `rust-analyzer` lexes and parses all source files and lowers most of it to High-Level Intermediate Representation (HIR).
Lowering to HIR is done to build up symbol table, that is a table that has knowledge of all symbols (idendtifiers) in the project.
This includes but is not limited to functions, traits, modules, ADTs, etc.
Lowering to HIR is done lazily.
For example most function bodies are usually not lowered at this stage.
One limitation of the `rust-analyzer` as of now is that it doesn't properly handle lifetimes.
Explicit lifetimes are all mapped to `'static` lifetimes and implicit lifetime bounds are ignored.
This also limits our possibilities to do borrow checking as there simply isn't enough data available in the `rust-analyzer` yet.
With the symbols table built up, `rust-analyzer` is ready to accept client requests.

Now autocompletion request can be sent.
Upon receiving a request that contains the cursor location in source code `rust-analyzer` finds the corresponding syntax node.
In case it is in function body that has not yet been lowered the lowering is done now.
Note that the lowering is always cached so that subsequent calls can be looked up from the table.
With all the lowering done, `rust-analyzer` builds up context of the autocompletion.
The context contains location in abstract syntax tree, all the items in scope, package configuration (is nightly enabled) etc.
If expected type of the item under completion can be inferred it is also available in the context.
From the context different completion providers (functions) suggest possible completions that are all accumulated to a list.
To add the term search based autocompletion we introduct a new provider that takes in a context and produces a list of completion suggestions.
Once the list is complete it is mapped to LSP protocol and sent back to client.

=== Term search <term-search-iters>
The main implementation of term search is done in the HIR level of abstraction and borrow checking queries are made in MIR level of abstraction.
Term search entry point can be found in `crates/hir/src/term_search.rs` and is named as `term_search`.
The most important inputs to term search are scope of the program we are performing the search at and the target type.

To better understand why the main algorithm is based around bidirectional BFS we will discuss three iterations of the algorithm.
First we start with algorithm that quite closely follows the algorithm we described in @agsy.
Then we will see how we managed to achieve better results with using BFS instead of DFS as suggested in @standardml.
At last we will see how the algorithm can benefit from bidirectional search.

=== First iteration: DFS <first-iter-dfs>
The first iteration of the algorithm follows the algorithm described in @agsy.
The implementation for it is quite short as the DFS method seems to naturally follow the DFS as pointed out in @standardml.
However since our implementation does not use any cacheing it is very slow.
Bacause of the poor performance we had to limit the search depth to 2 as bigger depth caused the algorithm to run for a considerable amount of time.
The performace can be improved by cacheing some of the found terms but doing it efficiently is rather hard.

Cacheing the result means that once we have managed to produce a term of type `T` we want to store it in a lookup tabel so that we wouldn't have to search for it again.
Storing the type first time we find it is rather trivial, but it's not very efficient.
The issue arises from that there are no guarantees that the first term we come up with is the simplest.
Consider the example of prducing something of type `Option<i32>`.
We as humen know that easiest way to produce a term of that type is to use the `None` constructor that takes no arguments.
The algorithm however might first take the branch of using `Some(...)` constructor.
Now we have to also recurse to find something of type `i32`, and potentially iterate again and again if we do not have anything suitable in scope.
Even worse, we might end up not finding anything suitable after fully traversing the tree we got from using the `Some(...)` constructor.
Now we have to also check the `None` subtree which means that we only benefit from the cache if we want to search for `Option<i32>` again.

This is not a problem if we want to retreive all possible term for the target type, however that is not always what we want to do.
We found that for bigger terms it is better to produce a term with new holes in it, even when we have solutions for them, just to keep amount of suggestions low.
Consider the following example.

#sourcecode(numbering: none)[```rs
let var: (bool, bool) = todo!();
```]

If we give user back all possible terms then the user has to choose between following options:
#sourcecode(numbering: none)[```rs
(false, false)
(false, true)
(true, false)
(true, true)
```]
However, we can simplify it to only suggesting the use of tuple constructor with two new holes in it.
#sourcecode(numbering: none)[```rs
(todo!(), todo!())
```]
If there are only few possiblilities to come up with a solution then showing them all isn't really a problem.
However it is quite common for the type constructors or functions to take multiple arguments.
This as the amount of terms is exponential relative to amount of arguments to function/type constructor takes the amount of suggestions grows very fast.
As result quite often all the results don't even fit onto screen.
In @second-iter-bfs we will introduce a algorithm to handle this case.
For now it is sufficient to aknowledge that fully traversing the search space to produce all possible terms is not the desired approach and there is some motivativation to cache the easy work to avoid the hard work, not vice versa.
Branch costs suggested in @mimer can potentially improve this but the issue still remains as this is simply a heuristic.

Another observation from implementing the DFS algorithm is that whilst most of the algorithm looked very elegant the "struct projection" tactic described in @tactic-struct-projection was rather awkward to implement.
The issue arose the projections having to include all the fields from the parent struct as well as from the child struct.
Including only the child "leaf" fields is very elegant with DFS but also including the intermediate fields caused some extra boilerplate.

Similar issues arose when we wanted to speed up the algorithm by running some tactics, for example "impl method" only on types that we have not yet ran it on.
Doing it with DFS is definitely possible but it doesn't fit the algorithm conveniently.
As there were were many issues with optimizing the DFS approach we decided to not improve it further and turn to BFS based algorithm instead.


=== Second iteration: BFS <second-iter-bfs>
The second iteration of our algorithm was based on BFS as suggested in @algebraic-foundations-of-proof-refinement.
However it differs from it by doing the search in the opposite direction.
The algorithm in @algebraic-foundations-of-proof-refinement starts from the target type and starts working backwards from it towards what we already have.
For example if we have function in scope that takes us to the goal we create new goals for all the arguments of the function, therefore move backwards from the return type towards the arguments.
Our algorithm however works in the forward direction, meaning that we start from what we have in scope.
We try to apply all the functions etc. to then build new types from what we have and hopefully at some point arrive at the target type.

In @graph-searching they argue that taking the forward (bottom-up) approach will yield speedups when the active frontier is a substantial fraction of the total graph.
We believe that this might be the case for term search as there are many ways to build new types available (functions/type constructors/methods).
Going in the forward direction all the terms we create are well formed and do not have holes in them.
This means that we do not need problem collections as there are never multiple subproblems pending that have to all be solved for some term to be well formed.
As there is a potential speedup as well as the implementation seems to be easier we decided to experiment with using the forward approach.

Going in the "forward" direction also makes writing some of the tactics easier.
Consider the example of struct projections.
In the backwards direction we would start with the struct field and then later search if we have the struct available.
This works, but it is rather hard to understand as we usually write code for projections in the forward direction.
With BFS going in the forward direction we can just visit all the fields of struct types in every iteration which roughly follows how we usually write code.
The issue of awkward handling of fields together with their fields also goes away as we can consider only one level of fields in every iteration.
With multiple iterations we manage to cover fields of nested structs without needing any boilerplate.

In this iteration we also introduce the cache to the algorithm.
The idea of the cache is to keep track of types we have reached so that we could query for terms of that type in $O(1)$ time complexity.
Since in practice we also care about terms that unify with the type we get the complexity of $O(n)$ where the $n$ is number of types in cache.
This is still a lot faster than taversing the tree as iterating the entries in the map is quite cheap opertion.
With this kind of graph we managed to increase the search depth to 3-4 depending on the size of the project.

In the DFS approach without chache the main limitation was time complexity, but now the limitation is the memory complexity.
The issue is producing too many terms for a type.
In @first-iter-dfs we dicussed that there are often too many terms to present for the user.
However now we find that there are also too many terms to keep in memory due to exponential growth of them as the depth increases.
Luckily the idea of suggesting users the terms that have new holes in them also reduces the memory complexity a lot.

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
The idea is that if there a only a few terms of given type we keep them all so that we can provide the full term to the user.
However if there are too many of them to keep track of we just remember that we can come up with a term for given type, but we won't strore the terms themselves.
The cases of `Many` later become the holes in the generated term.

In addition to decreasing memory complexity this reduces also time complexity a lot.
Now we do not have to construct the terms if we know that there are already many of the type.
This can be acieved quite elegantly by using iterators in Rust.
Iterators in Rust are lazy meaning that they only do work if we consume them.
In our case consumin the iterator is extending the `AlternativeExprs` in the Cache.
However if we are already in the many case we can throw away the iterator without performing any computation.
This speeds up the algorithm a lot so now we can rise the depth of search to 10+ with it still outperforming the previous algorithms on time scale.

The algoritm itself is quite simple, the pseudocode for it can be seen in @rust-bfs-pseudocode.
We start by gathering all the items in scope to `defs`.
These items include local values, constants as well as all visible functions/type constructors etc.
Next we initialize the lookup table with desired many threshold for the alternative expressions shown in @rust-alternative-exprs.
The lookup table owns the cache, the state of the algorithm and some other values for optimizations.
We will discuss the exact functionalities of the lookup table in @lookup-table.

Before entering the main loop we populate the lookup table by running a tactic called `trivial`.
Essentially it attempts to fulfill the goal by trying variables we have in scope.
More information about the `trivial` tactic can be found in @tactic-trivial.
All the terms it produces get added to lookup table and can be later used in other tactics.
After that we iteratively expand the search space by attempting different tactics until we've exceeded the preconfigured search depth.
We keep iterating after finding the first match as there may be many possible options.
For example otherwise we would never get suggestions for `Option::Some(..)` as `Option::None` usually comes first as it has fewer arguments.
During every iteration we sequentially attempt different tactics.
More on the tactics can be found in @tactics, but all of them attempt to expand the search space by trying different ways to build new types from existing types (type constructors, functions, methods, etc.).
The search space is expanded by adding new types to lookup table.
Example for it can be seen in @term-search-state-expansion.
In the end we filter out duplicates and solutions that do not take us closer to the goal.

#figure(
sourcecode()[```rs
pub fn term_search(ctx: &TermSearchCtx) -> Vec<Expr> {
    let mut defs = ctx.scope.process_all_names(...);
    let mut lookup = LookupTable::new(ctx.many_threshold);

    // Try trivial tactic first, also populates lookup table
    let mut solutions: Vec<Expr> = 
        tactics::trivial(ctx, &defs, &mut lookup).collect();

    for _ in 0..ctx.config.depth {
        lookup.new_round();

        solutions.extend(tactics::type_constructor(ctx, &defs, &mut lookup));
        solutions.extend(tactics::free_function(ctx, &defs, &mut lookup));
        solutions.extend(tactics::impl_method(ctx, &defs, &mut lookup));
        solutions.extend(tactics::struct_projection(ctx, &defs, &mut lookup));
        solutions.extend(tactics::impl_static_method(ctx, &defs, &mut lookup));
    }

    solutions.into_iter().filter(|it| !it.is_many()).unique().collect()
}
```],
caption: [
    Bottom up term search pseudocode
  ],
) <rust-bfs-pseudocode>

As we can see from the @rust-bfs-pseudocode we start from what we have (locals, constants, statics) and work towards the target type.
This is opposite direction comparaed to what is used in all the other tools we have looked at.
To better understand how the search space is expanded let's look at @term-search-state-expansion.

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
4. Types wishlist (Types that have been queried, but not reached)

Terms reached serves the most obvious purpose of them.
It keeps track of the search space we have already covered (visited types) and allows quering terms them in $O(1)$ complexity for exact type and $O(n)$ complexity for types that unify.
Important thing to note here that it also performs transformation of taking a reference if we query for reference type.
This is only to keep the implementation simple and memory footprint low.
Otherwise, having separate tactic for taking a reference of the type would be preferred.

New types reached keeps track of new types added to terms reached so that we can iterate only over them in some tactics to speed up the execution.

Definitions used serves also only purpose for speeding up the algorithm by avoiding definitions that have already been used.

Types wishlist keeps track of all the types we have tried to look up from terms reached but not found.
They are used in static method tactic (see @tactic-static-method) to only search for static methods on types we haven't reached yet.
This is another optimization for speed described in @tactic-static-method.

The main downside of the lookup table implementation we have is that it poorly handles types that take generics.
We only store types that are normalize meaning that we have substitued the generic parameter with some concrete type.
In case of generics, if often means that the lookup table starts growing exponentially.
Consider the example of using `Option` type.
#sourcecode()[```rs
Some(T) | None
Some(Some(T)) | Some(None) | Some(T) | None
Some(Some(Some(T))) | Some(Some(None)) | Some(Some(T)) | Some(None) | Some(T) | None
```]
With every iteration two new terms of new type come available, even though it is unlikely one would ever use them.
However since `Option` takes only one generic argument the grown is linear as many of the term cancel out due to already being in the cache.
If we have something with multiple generic parameters becomes exponential.
Consider the example of wrapping the types we have to pair (tuple with two elements).
At first we have $n$ types. After first iteration we have $n^2$ new types as we are taking the Cartesian product.
In the second iteration ve can crate a pair by taking one of the elements from the original set of types and the second element from the set of pairs we have.
As for every pair there are $n$ original types to choose from we get $n^3$ pairs and also all the pairs of pairs.
Even without considering the pairs of pairs we see that tho growth is exponential.

To keep the search space to a reasonable size we ignore all types with generics unless if they take as directly to the goal.
This means that we limit the depth for the generics to 1 which is a very severe however necessary limitation.
In @third-iter-bidirectional-bfs we will discuss how to get around this limitation.

=== Third iteration: Bidirectional BFS <third-iter-bidirectional-bfs>
#todo("paragraph for terminology, directions, why, example. this should be before 2nd iter")
The third iteration of our algorithm is a small yet powerful improvement on the second iteration described in @second-iter-bfs.
This iteration differs from the previous one by improving the handling of generics.
We note that the handling of generics is a lot smaller problem if going in the backwards direction as other term search tools do.
This is because we can only construct the types that actually contribute towards reaching the goal.
However if we only go in the backwards direction we can still end up with terms such as `Some(Some(...)).is_some()` that do contribute towards the goal but not in a very meaningful way.
BFS copes with these kind of terms quite well as the easiest paths are taken first.
However with multiple iteration many not so useful types get added to the lookup table nontheless.
Note that the trick with lazy evaluation of iterators does not work here as the terms have types not yet in the lookup meaning we cannot discard them.
Filtering them out in backwards direction is possible but not trivial.

To benefit from better handling of generics going in the backwards direction and otherwise more intuitive approach of going forwards we decided to make the search bidirectional.
The forward direction starts from the locals we have and starts expanding the search space from there.
Tactics that work in the forward direction ignore all types where we need to provide generic paramiters.
Other tactics start working backwards from the goal.
All the tactics that work backwards do so to better handle generics.

Going backwards is achieved by using the types wishlist component of the lookup table.
We first seed the wishlist with the target type.
During every iteration the tactics working backwards from the target type only work with concrete types we have in wishlist.
For example if there is `Option<Foo>` in the wishlist and we work with the `Option<T>` type we know to substitute the generic type parameter `T` with `Foo`.
This way we avoid polluting the lookup tabel with a large number of types that mostlikely do not contribute towards the goal.
All the tactics add types to the wishlist so forward tactics can benefit from the backwards tactics (and vice versa) before meeting in the middle.
With some tactics such as using methods on type only working in the forward direction we can conveniently avoid adding complex types to wishlist if we only need them to get something simple such as `bool` in the `Some(Some(...)).is_some()` example.


== Tactics <tactics>
We use tactics to expand the search space for the term search algorithm.
All the tactics are applied sequentially which causes a phase ordering problem as tactics genrally depend on results of others.
However, the ordering of tactics problem can be fixed by running the algorithm for more iterations.
Note that some tactics also use heuristics for performance optimization that also suffer from the phase ordering problem, but they can not be fixed by running the algorithm for more iterations.

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
    Term search tactic signature
  ],
) <rust-tactic-signature>
All the tactics take in the context of term search, definitions in scope and a lookup table and produce an iterator that yields expressions that unify with the goal type (provided by the context).
The context encapsulates semantics of the program, configuration for the term search and the goal type.
Definitions are all the definitions in scope that can be used by tactics.
Some of the examples of definitions are local variables, functions, constants and macros.
The definitions in scope can also be derived from the context, but they are kept track of separately to speed up the execution by filtering out definitions that have already been used.
Keeping track of them separately also allows querying them only once as they do not change throughout the execution of the algorithm.
Lookup table is used to keep track of the state of the term search as described in @lookup-table.
The iterator produced by tactics is allowed to have duplicates as filtering of them is done at the end of the algorithm.
We decided to filter at the end because it is hard to guarantee that different tactics do not produce same elements, but without the guarantee of uniqueness there would have to be another round of deduplication nevertheless.

==== Tactic "trivial" <tactic-trivial>
Tactic called "trivial" is one of the most trivial tactics we have.
It only attempts items we have in scope and does not consider any functions / type constructors.
The items in scope contains:
1. Constants
2. Static items
3. Generic parameters (constant generics#footnote(link("https://doc.rust-lang.org/reference/items/generics.html")))
4. Local items

As this tactic only depends on the values in scope we don't have to call it every iteration.
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

==== Tactic "famous types"
"Famous types" is another rather trivial tactic.
The idea of the tactic is to attempt values of well known types.
Those types and values are:
1. `true` and `false` of type `bool`
2. `()` of unit type `()`
Whilst we usually try to avoid creating values out of the blue we make an exception here.
The rationale of making types we generate depend on types we have in scope is that usually the programmer writes the code that depends on inputs or previous values.
Suggesting something else can be considered distracting.
However, we find these values to be common enough to be usually a good suggestions.
Another reason is that we experienced our algorithm "cheating" around depending on values anyway.
It constructed expressions like `None.is_none()`, `None.is_some()` for `true`/`false` which are valid but all most never what the user wants.
For unit types it can use any function that has "no return type" meaning it returns unit type.
There is all most always at least one that kind of function in scope but suggesting it is unexpected more often than suggesting `()`.
Moreover suggesting a random function with `()` return type can often be wrong as the functions can have side effects.
Similarly to tactic "trivial" this tactic helps populating the lookup table for the forward pass tactics.
/*
$
(?: "bool") / (? := "true" #h(0.5cm) ? := "false")
#h(1cm)
(?: "()") / (? := "()")
$
*/

==== Tactic "type constructor"
"Type constructor" is first of our tactics that takes us from some types to another types.
The idea is to try type constructors for types we have in scope.
This includes both sum and product types (`enum` and `struct` for rust).

As the ADT types may or may not contain generic arguments the tactic work in both forward and backward direction.
Forward direction is used if the ADT does not have any generic parameters.
Backward direction is used for types that have generic parameters.
In the backward direction all the generic type arguments are taken from the types in wishlist so we know that we only produce types that somehow contribute towards our search.

The tactic avoids types that have unstable generic parameters that do not have default values.
Unstable generics with default values are allowed as many of the well known types have unstable generic parameters that have default values.
For example the definition for `Vec` type in Rust is following:
```rs 
struct Vec<T, #[unstable] A: Allocator = Global>
```
As the users normally avoid providing generics arguments that have default values we also decided to avoid filling them.
This means that for the `Vec` type above the algorithm only tries different types for `T`, but never touches the `A` (allocator) generic argument.
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
"Free function" is a tactic that tries different functions in scope.
It only tries functions that are not part of any `impl` block (associated with type or trait) and therefore considered "free".
We've decided to filter out all the functions that have non-default generic parameters.
This is because `rust-analyzer` does not have proper checking for the function to be well formed with a set of generic parameters.
This is an issue if the generic parameters that the function takes are not present in the return type.

As we ignore all the functions that have non-default generic parametrs we can run this tactic in only forward direction.
As described in @tactics the tactic avoids functions that return types that contain references.
However, we do allow function arguments to take items by shared references as this is a common practice to pass by reference rather than value.
/*
$
(a: A, b: B in Gamma #h(0.5cm) f: A times B -> C in Gamma #h(0.5cm) ?: C) /
(? := f(a, b)) \
$
*/

==== Tactic "impl method"
"Impl method" is a tactic that attempts functions that have `self` parameter.
This includes both trait methods and methods implemented directly on type.
Similarly to "free function" tactic it also ignores functions that have non-default generic parameters defined on the function for the same reasons.
However generics defined on the impl block possess no issues as they are associated with the target type and we can provide concrete values for them.

A performace tweak for this tactic is to only search the `impl` blocks for types that are new to us meaning that they were not present in the last iteration.
This implies we run this tactic only in the forward direction ie we need to have term for the receiver type before using this tactic.
This is a heuristic that speeds up the algorithm quite a bit as searching for all `impl` blocks is a costly operation.
However, this optimization does suffer from the phase ordering problem.
For example, it may happen that we can use some method from the `impl` block later when we have reached more types and covered a type that we need for an argument of the function.

We considered also running this tactic in the reverse direction but it turned out to be very hard to do efficiently.
The main issue is that there are many `impl` blocks for generic `T` which do not work well with the types wishlist we have as it pretty much says that all types belong to the wishlist.

One interesting aspect of Rust to note here is that even though we can query the `impl` blocks for type we still have to check that the receiver argument is of the same type.
This is because Rust allows also some other types that dereference to type of `Self` for the receiver argument#footnote(link("https://doc.rust-lang.org/reference/items/associated-items.html#methods")).
These types include but are not limited to `Box<S>`, `Rc<S>`, `Arc<S>`, `Pin<S>`.
For example there is a method signatures for `Option<T>` type in standard library#footnote(link("https://doc.rust-lang.org/src/core/option.rs.html#715")) shown in @rust-receiver-type.

#figure(
sourcecode(numbering: none)[```rs
impl<T> Option<T> {
    pub fn as_pin_ref(self: Pin<&Self>) -> Option<Pin<&T>> { /* ... */ }
}
```],
caption: [
    Receiver argument example in Rust
  ],
) <rust-receiver-type>
As we can see from the snippet above the Type of `Self` in `impl` block is `Option<T>`.
However, the type of `self` parameter in the method is `Pin<&Self>` which means that to call the `as_pin_ref` method we actually need to have expression of type `Pin<&Self>`.

We've also decided to ignore all the methods that return the same type as the type of `self` parameter.
This is because they do not take us any closer to goal type, and we've considered it unhelpful to show user all the possible options.
I've we'd allow them then we'd also receive expressions such as `some_i32.reverse_bits().reverse_bits().reverse_bits()` which is valid Rust code but unlikely something the user wished for.
Similar issues arise often when using the builder pattern as shown in @rust-builder
/*
#todo("same as free function as the self is not really that special")
$
(a: A, b: B in Gamma #h(0.5cm) f: A times B -> C in Gamma #h(0.5cm) ?: C) /
(? := f(a, b)) \
$
*/

==== Tactic "struct projection" <tactic-struct-projection>
"Struct projection" is a simple tactic that attempts all field accesses of struct.
The tactic runs only in the forward direction meaning we only try to access fields of target type rather than search for structs that have field with target type.
In a single iteration it only goes one level deep, but with multiple iterations we cover also all the fields of substructs.

This tactic highly benefitted from the use of BFS over DFS as the implementation for accessing all the fields of parent struct is rather trivial and with multiple iterations we get the full coverage including substruct fields.
With DFS the implementation was much more cumbersome as simple recurring on all the fields leaves out the the fields themselves.
As a result the implementation for DFS was about 2 times longer than the implementation for BFS.

As a performance optimization we only run this tactic on every type once.
For this tactic this optimization does not reduce the total search space covered as accessing the fields doesn't depend on rest of the search space covered.
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
"Static method" tactic attempts static methods of `impl` blocks, that is methods that are associated with either type or trait, but do not take `self` parameter.
One of the most common examples of static methods are `Vec::new()` and `Default::default()`.

As a performance optimization we qurey the `impl` block for types that we have i wishlist meaning we only go in the backwards direction.
This is because we figured that the most common use case for static methods is the factory method design pattern described in @design-patterns-elements-of-reusable-oo-software.
Quering `impl` blocks is a costy operation so we only do it for types that are contributiong towards the goal meaing they are in wishlist.

Similarly to "Impl method" tactic we ignore all the methods that have generic parameters defined on the method level for the same reasoning.
/*
#todo("This is same as free function again...")
$
(a: A, b: B in Gamma #h(0.5cm) f: A times B -> C in Gamma #h(0.5cm) ?: C) /
(? := f(a, b)) \
$
*/

==== Tactic "make tuple"
"Make tuple" tactic attempts to build types by constructing a tuple of other types.
This is another tactic that runs only in the backwards direction as otherwise the search space would grow exponentially.
In Rust the issue is even workse as there is no limit for how many items can be in a tuple meaning that even with only one term in scope we can create infinitely many tuples by repeating the term infinite amount of times.

Going in the backwards direction we can only construct tuples that are useful and therefore keep the search space in reasonably small.
/*
$
(a: A, b: B in Gamma #h(0.5cm) ?: (A, B)) /
(? := (a, b)) \
$
*/

= Evaluation <evaluation>
In this chapter we evaluate the performace of the three iterations of algorithms we implemented in @term-search-iters.
The main focus is on the third and final iteration but we compare it to previous iterations to highlight the differences.

First we are perform empirical evaluation of the tree algorithms by performing a resynthesis on existing Rust programs.
Later we focus on some hand picked examples to show the strengts and weaknesses of the tool.

== Resynthesis
Resynthesis is using the tool to synthesise programs we already have.
This allows comparinon of the generated suggestions to what humen have written.
For resynthesis we do the following:
1. Take exisiting open source project as a baseline
2. Remove one expression from it, thus create a hole in the program
3. Run term search on the hole
4. Compare generated results with what was there before
5. Put back the original expression and repeat on rest of the expressions

==== Chosen expressions
We chose to perform the the resynthesis only on the tail expressions of every block.
Other options that we considered are let assignments and arguments of function calls.
We chose tail expressions as we consider this the most common usecase for our tool.
Tail expression are the last expression in a block expression which value is returned as a value of the block.
The most well known place for them is the tail expression in the function body.
However since we consider all the block expressions the tail expressions in each of the branches of `if condition { ... } else { ... }` expression are also considered as well as the expressions in `match` arms or the plain block expressions used for scoping.
To better understand what is considered the tail expression we have constructed hypothetical example of code in @rust-tail-expr and highlighted all the lines that have tail expressions on them.
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
    Tail expression examples
  ],
) <rust-tail-expr>
Intuitively we can thing of them as the all the expressions that are on the last line of the block expression (`{ .. }`) and that do not end with a semicolon.

==== Chosen metrics
Here is a list of metrics we are interested in for resynthesis
1. Tail expressions found - This represents the precentage of tail expressions where the algorithm managed to find some term that satisfies the type system. The term may or may not be what was there before.
2. Syntactic hits - This represents the precentage of tail expressions in relation to total amount of terms that are syntactically exactly what was there before. Note that syntactical equality is a very strict metric as programs with different syntax may have the same meaning. For example `Vec::new()` and `Vec::default()` produce exactly the same behavior. As deciding of the equality of the programs is generally undecidable according to Rice's theorem @rice-theorem we will not attempt to consider the equality of the programs and settle with the syntactic equality.
   To make the metric slightly more robust we remove all the whitespace from the programs before comapring them.
3. Average time - This represents average time for a single term search query. Note that although the cache in term search is not persisted between runs the lowering of the program is cached. This is however also true for the average usecase as `rust-analyzer` as it only wipes the cache on restart.
   To benchmark the implementation of term search rather than the rest of `rust-analyzer` we run term search on hot cache.
4. Average options per hole - This shows the average amount of options provided to the user.

==== Chosen crates
Crate is a name for a Rust library.
We use crates.io#footnote(link("https://crates.io/")), the Rust community’s crate registry as a source of information of the most popular crates.
Crates.io is _de facto_ standard crate registry so we believe that it reflects the popularity of the crates in the Rust ecosystem very well.

To choose crates that are representative also to what average rust code looks like we decided to pick top 5 crates by all time downloads of the most popular categories on crates.io.
To filter reduce the sample size we decided to filter out categories that have fewer than 1000 crates in them.
That left us with 31 categories with 155 crates in them.
Full list of chosen crates can be seen in #ref(<appendix-crates>, supplement: "Appendix").

==== Results
First we are going to take a look at how the hyperparameter of search depth affects the chosen metrics.
The relation between depth and all the metrics.
From @term-search-depth-accuracy we can see that after the second iteration we are barely finding any new terms and very few of them are also the syntactic matches.
From @tbl-depth-hyper-param we can see that the curve for terms found is not entirely flat, but the improvements are very minor.

#figure(
  image("fig/accuracy.png", width: 90%),
  caption: [
    Term search depth effect on metrics
  ],
) <term-search-depth-accuracy>

The amount of suggestions follows similar pattern to terms found but the curve is flatter.
The search time of the algortihm seems to be in linear realtion with the search depth with a root mean square error of 8.1ms.

#figure(
  image("fig/time.png", width: 90%),
  caption: [
    Term search depth effect on time and amount of suggestions
  ],
) <term-search-depth-time>

From the mesurments shown in @term-search-depth-accuracy and @term-search-depth-time we see that increasing the search depth over two can actually have somewhat negative effects.
The search will take longer and there will be more suggestions which can often mean more irrelavant suggestions as the syntactic hits is growing really slowly.

#figure(
  table(
    columns: 5,
    inset: 5pt,
    align: horizon,
    table.header[*Depth*][*Syntax hits*][*Found*][*Suggestions per expr*][*Avg time (ms)*],
[0], [0.02], [0.188], [15.058], [23.419], 
[1], [0.093], [0.68], [18.137], [33.032], 
[2], [0.095], [0.745], [20.003], [72.419], 
[3], [0.098], [0.761], [21.514], [111.813], 
[4], [0.096], [0.76], [22.101], [137.065], 
[5], [0.095], [0.762], [22.257], [151.103], 
  ),
  caption: [Depth hyperparameter effect on metrics]
) <tbl-depth-hyper-param>

More interestingly we can see from the table that syntax hits starts to decrease after depth of 2.
This is because we get more results for subterms and squash them to _Many_ option, or in other words replace with new hole.
Terms that would result in syntactic hits get also squased into _Many_ resulting in a decrease in syntactic hits.

With the depth limit of 2 the program managed to generate a term with syntactic match in 10.7% of searches and find some term that satisfies the type in 74.0% of the searches.
Average number of suggestions per hole is 18.6 and they are found in 35ms.
However the numbers vary alot depending on the style of the program.
Standard deviation for average number of suggestions is about 56 and 167ms for average time.
Standard deviation is pushed so high by some outliers which we discuss in @c-style-stuff.

#todo("First two iterations of the algorithm")

== Usability <usability>
In this section we study cases where our algorithm works either very well or very poorly.
We discuss some styles of programming, and places in program for that.
In addition of highlighting the programs we discuss why the algorithm behaves the way it does.

==== Generics
Although we managed to make the algorithm work decently with low amount of generics some libraries make extensive use of generics which is problematic for our algorithm.

Extensive usage of generics is very common among math related crates.
As a result the average search time for category "mathematics" is abount 10 times longer than the average over all categories. (784ms vs 72ms).

One example of such library is `nalgebra`#footnote(link("https://crates.io/crates/nalgebra")).
It uses generic parameters in all most all of it's functions.
A typical function from `nalgebra` can be seen in @eval-nalgebra.

Use of many generic parameters which result in a slower performance of our tool.
This is because the amount of types in wishlist can grow very large as there will be many generic types with different trait bounds.

==== Tail expressions
We find that tail expressions to be one of the best suited places for term search.
They are a good fit for both filling the holes but also for providing autocompletion suggestions.
This is for the following reasons:
1. Tail expressions usually have the expected type known.
  The type is either explicitly written (for example function return type) or can be inferred from the context (for example all the match arms need to have the same return type).
2. Once the user starts writing the tail expression they usually have enough terms available in the context to fill the hole.
  For example it is common to store struct fields in local variable and then combine them into struct only in the tail expression.
The effect is the bigger in the case of using term search for autocompletion than in case of using it to fill the holes.
In case of filling holes the user has often already done some extra effort such as specifing the type of the hole.
Ihe accurate type information is essential for the term search to provide good suggestions and non-tail expressions often do not have it availabel when typing.

==== Function arguments
We found that another very useful place for the term search alogrithm is to find parameters for the function call.
This is especially true when the user is working in the "exploration mode" and is looking to find different options how to call the function.
Similarly to tail expressions function calls usually have accurate type information available for the arguments with some expetions for generic types that are too general to provide accurate suggestions.
Often there are also arguments available in the context so the term search can easily fill them in.

==== Local variables
We found that in practice the terms search is not very useful for genereating the terms for local variables.
The main reason for that is that it is common to omit the type of the variable explicitly and let the compiler infer the type.
This however means that there is not type information available for the term search.
Adding the type explicitly fixes the issue but this is extra work for the user.

==== Builder pattern
As we previously discussed in @machine-learning the term search is not very effective in case the functions do not have the actions they do encoded into types.
One of the most common examples for it is the builder pattern in Rust.
There are usually only two methods on builder that change the return type which means the algorithm can only suggest them.
This results in suggestions like `Foo::builder().build()` which is a incomplete but valid suggestion.
However from personal experience with using the tool we found that in some cases also such suggestions provide value when the user is writing code in "exploration mode".
Such suggestions indicate an option of getting something of desired type and now the user has to evaluate if they want to manually call relavant methods on the builder or they do not wish to use the builder at all.
Without the term search suggestions the user may even not know that there exists a builder for the type.

==== Procedural Macros
An interesting observation was that filling holes in the implementation of procedural macros is less useful than usually and can even cause compile errors.
The decrease in usability is caused by procedural macros mapping `TokenStream` to `TokenStream` (Rust syntax to Rust syntax) meaning we do not have useful type information available.
This is very similar to builder pattern so the decrease in usefulness originates from the same reasons.
However procedural macros are somewhat special in Rust and they can also rise compile time errors.
For example one can assert that the input `TokenStream` contains a non-empty `struct` definition.
As the term search has no way of knowing that the `TokenStream` has to contain certain tokens also suggest other options that clearly validate the rule causing the error to be thrown.

==== Formatting
We found that formatting of the expressions can cause significat impact on the usability of the term search in case of autocompletion.
This is because is is common for the LSP Clients to filter out suggestions that do not look similar to what the user is typing.
Similarity is measured at the level of text with no semantinc information available.
This means that even though `x.foo()` (method syntax) and `Foo::foo(x)` (universal function call syntax) are the same the second option is filtered out if the user has typed `x.f` as text wise they do not look similar.
This causes some problems for our algorithm as we decided to use universal function call syntax whenever possible as this avoids ambuigity.
However users usually prefer method syntax as it is less verbose and easier to understand for humans.

However this is not a fundamental limitation of the algorithm.
One option to solve this would be to produce suggestions with using both of the options.
That however has it's own issues as it might overwhelm the user with the amount of suggestions in case the suggestions are text wise similar.
There can always be options when the user wishes to mix both of the syntaxes which causes the amount of suggestions to increase exponentially as every method call would double the amount of suggestions if we'd suggest both options.

==== Foreign function interface crates <c-style-stuff>
We found that for some types of crates the performace of the term search was significantly worse than for others.
Category "external-ffi-bindings" has an average search time of 571ms that is a lot slower than average of 72ms.
It also affers a lot more suggestions per term by suggesting 303 terms per hole which is about 15 times more than average of 20.
Such a big number of suggestions is overwhelming to user as 300 suggestions do not even fit onto screen.

Slow search times and high number of suggestions are caused by those crates not using many different types.
The only foreign function interface Rust supports is C, and C does not have such an expressive type system as Rust.
Foreign function interface (FFI) crates are wrappers around C functions and therefore often use integer types for most operations.
Searching for an integer however is not very useful as most functions in C return integers which all fit to the hole based on type.
As the point of FFI crates is to serve as a wrapper around C code so that other crates wouldn't have to we are not very concerned with the poor performace of term search in FFI crates.


== Limitations of the methods (week 5)
==== Resynthesis
The precentage of terms that the term search managed to fill does not reflect the usability of the tool very well.
This would be useful metric if we would use it as a proof search.
In case of regular programs that also have side effects we only care about suggestions that are semantically correct.
Other suggestions are noise as they produce programs that noone asked for.

Syntactic hits (equality) is a misleading metric as we really care about semantic equality of programs.
The metric may depend more on the style of the program than the formatting than on the real capabilities of the tool.
Syntactic hits also suffers from squashing multiple terms to `Many` option as the new holes produced by _Many_ are obviously not what was written by user.

Instead of average time and amount of suggestions per term search we should measure the worst case performace.
Having the IDE freeze for for a second once in a while is not acceptable even if at other times the algorithm is very fast.

==== Usability
This sections is really based on very small amount of personal experience and may therefore not reflect the average user very well.



= Future work (week 9) <future-work>
In this section we will discuss some of the work that could be done to improve term search in `rust-analyzer`.
Some of these topics consist of features for which there was not enough time to complete them in the timeframe of the thesis.
Other focus on improving the `rust-analyzer` functionality overall.

==== More permissive borrow checking
The current borrow checking algorithm we implemented for `rust-analyzer` is rather conservative and also forbids many of the correct programs.
This decreases the usefulness of term search usefulnesss whenever reference types are involved.
The goal would be to make the borrow checking algorithm in `rust-analyzer` use parts of the algorithm that is in the official compiler, but somehow allow borrow checking also on incomplete programs.
Lowering incomplete programs (user is still typing) to MIR and performing borrow checking incrementally is a complex problem however we believe that also many other parts of the `rust-analyzer` could benfeit from it.

==== Smarter handling of generics
In projects with hundreds of functions that take generic parameters our algorithm effectiveness decreases.
One of the main reasons for it is that we fully normalize all types before working with them.
In case of types and functions that have generic parameters this means substituting in the generic parameters.
However that is always not required.
Some methods in `impl` block do not require knowing exact generic parameters and therefore can be used without substituting in the generic types.
Some examples of it are `Option::is_some` and `Option::is_none`.
Others only use some of the generic parameters of the type.
In case not all generic parameters are used we could avoid substituting in the generic types that are not needed as long as we know that we have some options available for them.

==== Development of more tactics
A fairly obvious improvement that we believe still should be touched on is the addition of new tactics.
Addition of new tactics would allow usage in new context.
Some ideas for new tactics:
- Tuple projection - very similar to struct projection. Very easy to add.
- Macro call - similarly to function calls macros can be used to to produce terms of new types.
  As macros allow more custom syntax and work at the level of metaprogramming adding them can be more complex.
- Higher order functions - generating terms for function types is more complex than working with simple types.
  On the other hand higher order functions would allow usage of term search in iterators and therefore increase it's usefulness by a considerable margin.

==== Machine learning based techniques
We find that machine learning based techniques could be used to prioritize generated suggestions.
This could allow also suggestions that do not affect the type of the term.
For example suggestions for builder pattern could be made more useful by also suggesting some setter methods.
This would have some benefits over using LLMs as the code generation tools.
All the terms would be still generated by term search and would be valid programs by construction which is a guarantee that LLMs cannot have.
The ordering of suggestions is something that is very hard to do analytically and therefore we believe that it makes sense to train a model for it.

= Conclusion
In this thesis our main objective was to implement term search for the Rust programming language.
We achieved it by implementing it as a addition to `rust-analyzer`, the official LSP server for Rust.

We started by giving overview of similar tools used in Agda, Idris, Haskell and StandardML.
We analyzed both their functionality and algorithms they use and compared them to one another.

After that we dove into Rust programming language to give context of the langauge we are working in.
We also covered the LSP protocol and some of the autocompletion tools to have some uderstanding of the constrainsts we have when trying to use the term search for autocompletion.

The term search search algorithm we implemented is based on the term search tools used in Agda, Idris, Haskell and StandardML.
We took the different approach from the previos implementations by using the bidirectional search.
The bidirectional approach allowed us to implement each tactic for the direction that is the most natural fit for it.
This yielded in a rather simple implementations of tactics that achieve realtively high performace.

To evaluate the performace of the algorithm we ran the algortithm on existing open source projects.
For measuring the performace we chose top 5 projects of the most popular categories on crates.io, the Rust community’s crate registry.
This resulted in 155 crates.

We added term search based autocompletion suggestions to evaluate the usability of term search for autocompletion.
With small depth the algorithm proved to be fast enough and resulted in more advanced autocompletion suggestions compared to usual ones.
As the autocompletion in `rust-analyzer` is already rather slow the feature is disabled by default, yet all the users of it can opt into it.
