# V0-theory

how to formalize arithmetic?

deep-embedding of deductive system? too much work
shallow embedding? coq expressive enough! proves totality of exp.

the way to go:
deep-embedding of syntax + shallow embedding of proving, but with model abstracted!

now:
- [solved] how to deal with many-sorted logic? (use explicit typing rules)
- [solved] how to deal with 'exists' quantifier in ModelTheory? (modify ModelTheory)
- [solved] how to deal with debruijn indices while formalizing axiom schemes? (use iAlls and special free variable types!)
- how to prove equivalence of bounded-logic formula to its deeply-embedded lift?