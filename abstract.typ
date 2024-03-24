Rust is a general-purpose systems programming language that guarantees memory safety without the need for a garbage collector.
It's type system is similar to many functional programming languages as it features sum and product types.
Due to similar type system and many similar tools, the developer experience is similar to experience of developing in high level functional programming languages.
However, Rust does not have a tool for automatic program synthesis based on types (term search) although it is a perfect candidate for one.

In this thesis we extend the official Rust language server `rust-analyzer` with term search tool.
In addition to filling holes we experiment with using term search for autocompletion.
We develop the algorithm for term search in three iterations.
The first iteration is the simplest algorithm that follows one that is used in Agsy, similar tool in Agda.
The second iteration improves on first one by using some optimizations from other similar tools.
We also experiment with searching in the opposite direction compared to other tools.
The third iteration improves on the second iteration by making the search bidirectional.

To evaluate the performance of our algorithm we run it on 155 popular open source Rust libraries.
We measure how many holes the algorithm can fill, how often the algorithm suggest code that was written originaly by human and some other metrics.

As an outcome of this thesis we also upstream our tool to the official `rust-analyzer`.
