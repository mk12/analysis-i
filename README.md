# Analysis I

The goal of this project is to formalize all the definitions, axioms, propositions, lemmas, theorems, corollaries, and exercises from [_Analysis I_][a1] by Terance Tao. It is a work in progress; I am formalizing the proofs as I work through the book.

The proofs are written in [Coq][]. I started the project using the [Learn Theorem Prover][lean], but later restarted using Coq because Lean was changing too fast for me.

## Build

### Coq

First, install Coq (on macOS, `brew install coq`). Then, `cd coq && make`. To generate HTML documentation you can use `make html`.

To edit Coq files, I recommend using the Coq IDE (on macOS, `brew cask install coqide`).

### Lean

First, install Lean (on macOS, `brew install leanprover/lean/lean`). Then, run `lean --make` in the repository directory to compile all the Lean files.

To edit Lean files, you can use the official Emacs Lean mode. Or, if you prefer Vim, you can use my [vim-lean][] plugin.

## License

© 2020 Mitchell Kember

This project is available under the MIT License; see [LICENSE](LICENSE.md) for details.

[a1]: https://terrytao.wordpress.com/books/analysis-i/
[coq]: https://leanprover.github.io
[lean]: https://coq.inria.fr
[vim-lean]: http://github.com/mk12/vim-lean
