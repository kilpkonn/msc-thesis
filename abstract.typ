Rust is a general-purpose systems programming language that guarantees memory safety without the need for a garbage collector.
With on-par performance with C/C++, Rust attempts to challenge C/C++'s position in the market by providing better tooling and a better developer experience.

The Rust type system is similar to many functional programming languages as it features a rich type system, including sum and product types.
Developer experience is more similar to that of high-level functional programming languages than C/C++.
However, Rust does not have a tool for term search -- automatic program synthesis based on types.
Yet we believe it is a perfect candidate for one with its expressive type system.

In this thesis, we extend the official Rust language server `rust-analyzer` with a term search tool.
In addition to program synthesis, we experiment with using term search for autocompletion.
We develop the algorithm for term search in three iterations.
The first iteration is the simplest algorithm that follows one that is used in Agsy, a similar tool for Agda.
The second iteration improves on the first by reversing the search direction, simplifying the caching of intermediate results.
In the final iteration, we implement a bidirectional search.
This algorithm can synthesize terms in many more situations than in previous iterations,
without a significant decrease in performance.

To evaluate the performance of our algorithm, we run it on 155 popular open-source Rust libraries.
We delete parts of their source code, creating "holes".
We then let the algorithm re-synthesize the missing code,
and measure how many holes the algorithm can fill and how often the algorithm suggests the original code.

As an outcome of this thesis, we also upstream our tool to the official `rust-analyzer`.


The thesis is written in English and is #context counter(page).at(<end>).first() pages long,
including #context counter(heading).at(<conclusion>).first() chapters,
#context counter(figure.where(kind: image)).final().first() figures 
#context counter(figure.where(kind: raw)).final().first() code listings and 
#context counter(figure.where(kind: table)).final().first() tables.
