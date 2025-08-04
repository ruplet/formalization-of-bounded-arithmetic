Modern proof assistants are very powerful. It usually comes off as an advantage because we ultimately want their theory to prove difficult theorems.

But it also has disadvantages. Namely, it is difficult to reason about the actual expressive power of their formal systems. It is not obvious even to specify what are all the subtle effects introduced to the theory by the features of a proof assistant. And it is hard to compare the power of systems based on different theories, such as Lean (based on type theory) and Mizar (based on set theory) - but it is believed that these two particular have the same strength as ZFC + there exist infinitely many inaccessible cardinals [Mario Carneiro's master's thesis].

At the same time, a very lively branch of research requires us to adjust the power of formal systems very precisely - reverse mathematics and bounded arithmetic.

Modern proof assistants are not well-designed to limit the expressivity of their systems to very weak theories. For example in Coq, it doesn't seem feasible to conduct a proof in a formal system so weak it only supports induction over IDelta0 formulas. We would probably need to implement a deep embedding of the whole logic inside of Coq, which not only is work-heavy, but also might not be convenient to use. A shallow embedding is not obvious to come up with, as it is possible to define the specification (type) and implementation of an exponential function in Coq and prove its correctness. But IDelta0 does not prove the totality (termination) of this function; IDelta0 + exp is a stronger formal system. 

We postulate that it would be beneficial to start formalizing  results from reverse mathematics and bounded arithmetics. A very exciting branch of this work is Cook's ingenious connection of bounded arithmetics with complexity theory. In his and Nguyen's work[], the authors reasoned about logics in which theorems of the form (Forall x, exists y . phi(x, y)) are only provable if the corresponding function f(x)=y iff phi(x, y) is implementable in the complexity class corresponding to the logic - e.g. FAC0 (functions implementable by AC0 circuits) and its logic V0. 

It seems possible that implementing axiomatic systems and induction / comprehension schemes from their work, we could implement a very simple proof assistant, whose strength would be very well-studied.

Additionally, it also seems possible that in such a weak proof assistant, we could reason about the correctness of imperative computer programs, as V0, the theory of FAC0, is finitely axiomatizable.
