# Formalization of bounded arithmetic
In this project, I explore a way to formalize the results from the field of bounded arithmetic, most notably from the book [Logical Foundations of Proof Complexity](https://www2.karlin.mff.cuni.cz/~krajicek/cook-nguyen.pdf) from 2010 by Stephen Cook and Phuong Nguyen.

If successful, it could contribute towards:
- providing a sensible way to certify computational complexity bounds of computer programs
- providing a new way of extracting computer programs from mathematical theorems
- perhaps getting a few logicians interested in formal verification

For motivations and a brief introduction to why it is a promising direction, please see
- my [presentation](aitp-presentation.pdf) for [AITP 2025](https://aitp-conference.org/2025/)
- the [abstract](aitp-abstract.md) I had sent
- the [reviews](aitp-reviews.md) it has received

## Problems with mathlib.ModelTheory in this project
### Single-sorted logic only
The design is fundamentally single-sorted. When I started working on $V^0$, I re-wrote parts of the library to supports two sorts. It is feasible, but it is much easier to use explicit typing rules to encode two-sorted theory as a single-sorted one.
This is demonstrated in [file V0.lean](BoundedArithmetic/V0.lean)

### Too classical
ModelTheory sets $\exists \phi := \neg \forall \neg \phi$ internally. This is not ideal, as in our setting we need to check if a formula is $\Delta_0$, $\Sigma_1$\, $\Pi_1$ etc. and defining the existential quantifier like this completely breaks this. It also breaks the computational content of the proofs. For these reasons, I rewrote parts of ModelTheory to **not** do this substitution. I applied `sorry` where it was necessary for the library to work; these should be very safe, as the change is not important for the semantics.

Now it seems likely that we could do without modifying ModelTheory by just not caring about it. It is a task of a lower priority so I have left dealing with that for now.

### Many lemmas missing
Working on this project at this stage requires proving many lemmas about ModelTheory.BoundedFormula definitions for our types. This is good and perhaps will contribute to making this library even better.

### Very slow `simp`
This is something I have not dealt with yet, and it is a problem - simplifying the formulas resulting from creating the
induction axioms is very slow. It makes my VSCode laggy, my computer heat and, most annoyingly, the `apply?` and `rw?` tactics timeout. This definitely has to be addressed so that the simplifications are fast and simple.

## Existing works
### Foundation project
Most notably, there is an active project on formalizing logic in Lean 4, [`Foundations`](https://github.com/FormalizedFormalLogic/Foundation).
Their design, however, doesn't enable to solve the crux problem I want to solve - for the
theorems from arithmetic to be transferrable to the system. They reprove the theorems
and do so not in style of the weak arithmetic, but completely in *the* Lean model,
i.e. use theorems about natural numbers from the standard library of Lean etc.
This was addressed in [my discussion with the developers](https://github.com/orgs/FormalizedFormalLogic/discussions/358).

### Flypitch project
In a brekathrough effort, contributors of the [Flypitch project](https://github.com/flypitch/flypitch) managed to formalize the proof of
independence of continuum hypothesis from ZFC. They obviously considered the notion of provability. 

### Developments in Rocq
The environment of Rocq seemed to better foster this project, as the community of Lean is entirely nonconstructive and is
less likely to be interested in results about reverse mathematics. Importantly, these projects exist:
- [Rocq library to work with FOL](https://github.com/uds-psl/coq-library-fol.git)
- [Notable work on FOL in Rocq](https://ps.uni-saarland.de/~bailitis/bachelor.php)

### Just a shallow embedding
The obvious approach for this project is to embed our weak logic shallowly inside of Rocq / Lean / Isabelle.
It works well for the single axioms. There is a catch though - all these systems have a single `Prop` type (or equivalent)
and have completely no way of expressing `$\Delta_0-Prop$` or `$\Sigma_1-Prop$`. Without a deep embedding of at least the
syntax of logic, it doesn't seem possible to proceed in any of the existing systems. And a deep embedding of the logic obviously doesn't foster any way of proving these deeply embedded formulas without implementing the whole model theory
and proving in generalized model.

### Shallow embedding + nice syntactical macros to ease proving in object theory
Initially I had thought that the only feasible (i.e. not taking years of work) way to approach this is to
do everything in Lean, as a shallow embedding, but using syntactical macros provide frontend enabling
proving in the object theory and making cheating harder / easily visible to the reader.

I found some pointers on how could it looks like:
- [Presentation by Simon Hudon](https://lean-forward.github.io/lean-together/2019/slides/hudon.pdf)
- [Iris Proof mode for Lean](https://github.com/leanprover-community/iris-lean/blob/master/src/Iris/ProofMode/Display.lean)

Obviously, our current approach is good enough and doesn't need improving the frontend for now.

## Contact
Please contact me at ruplet+bounded at ruplet dot com.

## History of the project
This project is a part of my Master's thesis at the University of Warsaw.
My Master's project was to answer how to design programming languages to capture precisely a particular complexity class.
The works are in a [separate repository](https://github.com/ruplet/oracles).

This project, as my whole Master's program, has been supported by the [ZSM IDUB program](https://inicjatywadoskonalosci.uw.edu.pl/dzialania/iii-2-2/ios/).