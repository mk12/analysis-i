# Analysis I

The goal of this project is to formalize all the definitions, axioms, propositions, lemmas, theorems, corollaries, and exercises from [_Analysis I_][1] by Terance Tao using the [Lean Theorem Prover][2]. It is a work in progress; I am formalizing the proofs as I work through the book.

[1]: https://terrytao.wordpress.com/books/analysis-i/
[2]: https://leanprover.github.io

## Build

First, install Lean. On OS X, just run `brew install lean`. You should end up with the executables `lean` and `linja`, among others. Run `linja` in the repository directory to compile all the Lean files.

To make changes and see Lean's output, you can use the official Emacs Lean mode. Or, if you prefer Vim, you can use my [vim-lean][3] plugin.

[3]: http://github.com/mk12/vim-lean

## License

© 2016 Mitchell Kember

This project is available under the MIT License; see [LICENSE](LICENSE.md) for details.