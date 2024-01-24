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

== Term search (week 2)
I guess I can take the base from the document I have...

=== Term search in Agda (week 2)
#todo("Should it have subsections or merge?")

==== Agsy (week 2)

==== Some alternatives (week 2)
I've found some papers on improved versions of Agsy or alternatives to it.
I imagine I should compare them and see what is different.

=== Term search in Idris2 (week 3)
I think there is one and the only term serach implementation in Idris2.

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

The same example with typed holed instead of `todo!()` macros can be found in the snippet below:
```rs

fn main() {
    let a: i32 = 0;  // Suppose we have a variable a in scope
    let b: i32 = _;  // Term search finds `a`
    let c: Option<i32> = _;  // Finds `Some(a)`, `Some(b)` and `None`
}
```

== Autocomplete
Term search can also be used to give user "smarter" autocomplete suggestions as he is typing.
The general idea is the same as in filling holes.
We attempt to infer the expected type at the cursor.
If we manage to infer the type then we run the term search in order to get the suggestions.

The main difference between using term search for autocomplete and using it to fill holes is that we've decided to disable borrowchecking when generating
suggestions for autocompletion.
This means that not all the suggestions are valid programs and may need some modifications by user.

The rationale for it comes from both technical limitations of the tool as well as different expectations from the user.
The main techincal limitation is that borrow checking happens in the MIR layer of abstraction and `rust-analyzer` (nor `rustc`) does not support lowering
partial (user is still typing) programs to MIR.

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
The most logical fix for it is to go back to where the function `foo` is called and change the call to `foo(my_string.clone())` so that the variable of `my_string` doesnt get moved.
However if we only suggest items that borrow check the `bar(my_string)` function call would be ruled out as there is no way to call it without modifying the rest of the program.


=== Implementation (week 6)
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
We start by initializing the lookup table which keeps track of the state.
It has information of types we have reached, types we've searched for but didn't find and transitions we've used.
Before entering the main loop we populate the lookup table by running a tactic called `trivial`.
More information about the `trivial` tactic can be found in @tactic-trivial, but essentially it attempts to fulfill the goal by trying
variables we have in scope.
All the types get added to lookup table and can be later used in other tactics.
After we iteratively expand the search space by attempting different tactics untill we've exceeded the preconfigured search depth.
We keep iterating after finding the first match as there may be many possible options.
For example otherwise ve would never get suggestions for `Option::Some(..)` as `Option::None` usually comes first as it has less arguments.
During every iteration we sequentally attempt different tactics.
More on the tactics can be found in @tactics, but all of them attempt to expand the search space by trying different type transformations (type constructors, functions, methods).
The search space is expanded by adding new types to lookup table.
Once we've reached the maximum depth we filter out the duplicates and return all the paths that take us to goal type.



=== Tactics (week 6) <tactics>
#todo("Should I measure something per tactic?
Like how much does it help? There are many combinations so maybe not so good idea.")

==== Tactic trivial <tactic-trivial>
Describe every tactic, what it does, what it does not do and why.

= Results (week 7-8)

== Usability (week 8)

== Resynthesis (week 8)

= Future work (week 9)
#todo("Or after related work?")


= Related Work (week 9)
#todo("What here?
Kind of similar to what is in Backgeround section.")
Maybe subsection to state of the art.

