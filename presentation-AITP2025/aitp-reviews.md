TITLE: Simpler proof assistants via bounded arithmetic

----------------------- REVIEW 1 ---------------------

SUBMISSION: 7
TITLE: Simpler proof assistants via bounded arithmetic
AUTHORS: Paweł Balawender

----------- Overall evaluation -----------
SCORE: 0 (borderline paper)
----- TEXT:
The author presents foundational ideas for a proof assistant that would also support strong automation. This would be achieved by separating the reasoning into different modules (kernels)
which have a weaker logic. The author argue that, according to results in reverse mathematics, these weaker logics are expressive enough for produce most modern mathematics and simple enough that automation procedure could be developed. Finally, the author observes that it is not clear that the current theoretical results would produce practical procedure in these weaker logics. The topic is interesting but the ideas are too speculative to be presented at the moment, especially with the lack of a working prototype.


----------------------- REVIEW 2 ---------------------

SUBMISSION: 7
TITLE: Simpler proof assistants via bounded arithmetic
AUTHORS: Paweł Balawender

----------- Overall evaluation -----------
SCORE: 2 (accept)
----- TEXT:
Motivated by the results of reverse mathematics, the abstract proposes to develop a proof assistant based on a very weak logic (such as one of the logics discussed by Cook and Nguyen in their book on bounded arithmetic). Compared to the mainstream expressive systems (based on HOL and beyond), proofs checked here should correspond to a precisely controlled fragment (which the program of reverse mathematics should appreciate) and potentially even allow code extraction of programs provable in low complexity classes (if I understood the idea correctly).

The project proposal abstract should be of interest to the AITP audience and promises to lead to interesting discussions.


----------------------- REVIEW 3 ---------------------

SUBMISSION: 7
TITLE: Simpler proof assistants via bounded arithmetic
AUTHORS: Paweł Balawender

----------- Overall evaluation -----------
SCORE: 2 (accept)
----- TEXT:
I like the thinking of the author, and it seems relevant to AITP.

If reverse mathematics has reached the stage where something useful can be said about the weakest logical system needed to prove interesting results(I wasn't aware - but from the abstract it sounds very promising), then perhaps we in the ATP/ITP community should pay more attention. If the fragment turns out to be decidable or at least tractable, then the effect on attempts at automation could be huge.

This doesn't seem to be the main aim of the abstract, which is more concerned with precisely-controlled expressive power at a per-theorem level, but I'd like to hear more about both directions at AITP.