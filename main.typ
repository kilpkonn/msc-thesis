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

= Research Objectives
The main objective of this thesis is to implement tactics-based term search for a programming language Rust.
Other objectives include:
- Evaluating the fittness of tactics on existing large codebases
- Investigating term search usability for autocompletion

#todo("Where should I compare to existing?")

= Background / State of the art
#todo("Is State of the art legit title?")"

== Autocomplete
Should I describe what it is or is it obvious.
All the very high level items should be well known and specifics depend on implementation.

=== Language Server Protocol
Or is it irrelavant as this is not something I change?
On the other hand I guess this should give reader the idea that this work is not exclusive to some exotic IDE.

=== TODO
Anything else? Everything else feels like legacy now as we have  LSP.
Perhaps Jetbrains built in stuff is relavant, but why that and not anything else.
Also very language dependent so hard to say anything meaningful about that.

== Term search
I guess I can take the base from the document I have...

=== Term search in Agda
Should it have subsections or merge?

==== Agsy

==== Some alternatives
I've found some papers on improved versions of Agsy or alternatives to it.
I imagine I should compare them and see what is different.

=== Term search in Idris2
I think there is one and the only term serach implementation in Idris2.

== GitHub Copilot / LLM based autocompletions?
Should I talk about them?
They are legit alternative.
On the other hand I do not really want to go into neural nets and LLMs and not sure if talking about them only on the high level is a good idea.
Feels like if I point out shortcomings etc someone is like but there is another model that fixes it...

= Methods
Should this be somewhere before?

Should I list the implemention here as well? or is this kind of obvious?

== Usability
I guess this is explanation and justification what it does not do and why?
This is gonna be like 5 sentences max here as contents goes to results?

== Resynthesis

=== Chosen metrics

=== Chosen crates
Should I just say top5 or also list them out here?
I guess other option would be to list them in the validation paragraph

== Limitations of the methods
Or should it be under either of them

= Algorithm design
I guess very general overview here

=== Breath First Search
Why BFS and limitations of DFS (as the first implementation was DFS).

=== Tactics
Should I measure something per tactic?
Like how much does it help? There are many combinations so maybe not so good idea.

==== Tactic foo bar baz
Describe every tactic, what it does, what it does not do and why.

= Results

== Usability

== Resynthesis

= Future work
Or after related work?


= Related Work
What here?
Kind of similar to what is in Backgeround section.

