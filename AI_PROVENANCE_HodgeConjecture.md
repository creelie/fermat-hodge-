# AI provenance

Paper: *Algebraic Loci of Hodge Classes on Abelian Varieties and K3 Surfaces*, Deep Bhattacharjee and Ushashi Bhattacharya.

## What was done with AI assistance

The constructions on (F2) and (F3'), the search for a closure of the Hodge
conjecture, the text of the paper, the figures, the Lean 4 file and the
Python, Julia, C, C++ and shell programs were carried out by Deep
Bhattacharjee with the help of AI assistance (Claude, Anthropic), in sessions
in the Claude Code environment. The mathematical content was checked as
follows.

* Every hand proof in the paper was read against the cited literature
  (Markman, van Geemen, Schütt, Varesco, Buskin, Bloch, Buchweitz, Flenner,
  Moonen, Zarhin, André, Milne) and the earlier paper of the authors with
  Priyabrata Mandal.
* Every finite quantity (closures of the 256 subsets, Hilbert symbols and
  Hasse invariants, the 165 forms over Q(sqrt 6), the Fricke discriminants
  and Picard numbers, the dimension counts 57, 104 and 26, the Hecke algebra
  dimensions) is recomputed by programs in `code/` in at least two languages
  and the combinatorial and arithmetic ones are proved in
  `lean/HodgeClosure.lean`.
* Two numerical ranks (`product_object.py`, `convolution_checks.py`) are
  computed in floating point; no statement of the paper rests on them.

## What the AI did not do

The AI did not prove (F2), (F3') or the Hodge conjecture; the paper says so
and states at which step each construction stops. No result of the paper is
reported as proved on the strength of a machine computation alone.

## Where the AI was wrong and corrected

During the work three slips were found by the machine checks and corrected
in the text before release: the Hasse invariant at 2 of the form V_2
(it is -1, not +1); the Picard number of the twist family at level 5 (the
base change adds four fibres of type III); and the dimension of the dihedral
Hecke algebra ((n+1)/2, not (n+3)/2).

## Approval

Both authors approved the final version. Funding: none. Competing
interests: none.
