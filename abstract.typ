Rust is a general-purpose systems programming language that guarantees memory safety without the need for a garbage collector.
With on-par performance with C/C++, Rust attempts to challenge C/C++'s position in the market by providing better tooling and better developer experience.

Rust type system is similar to many functional programming languages as it features a rich type system, including sum and product types.
Developer experience is more similar to that of high level functional programming languages, rather than C/C++.
However, Rust does not have a tool for term search -- automatic program synthesis based on types.
Yet we believe it is a perfect candidate for one with its expressive type system.

In this thesis we extend the official Rust language server `rust-analyzer` with term search tool.
In addition to program synthesis, we experiment with using term search for autocompletion.
We develop the algorithm for term search in three iterations.
The first iteration is the simplest algorithm that follows one that is used in Agsy, a similar tool for Agda.
The second iteration improves on the first by reversing the search direction, simplifying caching of intermediate results.
The final iteration, we implement a bidirectional search.
This algorithm can synthesize terms in many more situation than the previous iterations,
without significant decrease in performance.

To evaluate the performance of our algorithm, we run it on 155 popular open source Rust libraries.
We delete parts of their source code, creating "holes".
We then let the algorithm re-synthesize the missing code,
and measure how many holes the algorithm can fill and how often the algorithm suggest the original code.

As an outcome of this thesis we also upstream our tool to the official `rust-analyzer`.
