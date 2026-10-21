# Hexagon submission fields

Title: Dense Algebraic Loci of Hodge Classes

Abstract: We prove unconditionally that the Hodge conjecture is equivalent to two statements about abelian varieties, that the locus on which either statement holds is dense in every family and is either the whole family or a meagre set, that the real multiplications by sqrt 6 and by the cubic fields Q(zeta_7)^+ and Q(zeta_9)^+ are algebraic on explicit families of K3 surfaces, the cubic ones on the surfaces of Mumford type whose quaternion algebra is ramified at two real places, and that the Hodge conjecture holds on every power and every Hilbert scheme of points of the K3 surfaces of the one-dimensional Fricke families of levels 5 and 7, which carry complex multiplication by Q(sqrt -5) and Q(sqrt -7). For each of the two statements we build the object it needs next, a complex on a product of two Weil fourfolds and a class on an abelian fourteenfold, prove what it does, and prove at which step it stops; among the steps, every convolution of the Weil line bundles on E_0^8 whose shifts lie in seven consecutive integers fails the polarised criterion in eighteen of the twenty-eight arrangements of the shifts, an explicit curve of genus four makes the Prym map of cyclic triple covers étale onto the Weil domain of Q(sqrt -3), and the conjecture for a class is equivalent to the vanishing of the mass gap of a multiple of it plus a complete intersection, which Kollár's hypersurfaces show cannot be dropped for integral classes. Both statements remain open.

Primary subject: math.AG (Algebraic Geometry)
Cross-list subjects: math.NT (Number Theory), math.KT (K-Theory and Homology), math.RT (Representation Theory)
Tags: Hodge conjecture, abelian varieties, Weil classes, K3 surfaces
MSC2020: 14C30 Transcendental methods, Hodge theory (algebro-geometric aspects); 14K20 Analytic theory of abelian varieties; abelian integrals and differentials; 14J28 K3 surfaces and Enriques surfaces; 11E12 Quadratic forms over global rings and fields

Contributor 1 (submitting): Deep Bhattacharjee; ORCID 0000-0003-0466-750X; affiliation: Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India; formerly, University of Calcutta, 87/1 College Street, Kolkata 700073, India; itsdeep@live.com (second address d.bhattacharjee@erl-forschung.de)
Contributor 2: Ushashi Bhattacharya; ORCID 0009-0002-2254-3914; affiliation: Formerly, National Taiwan University, Taipei 106319, Taiwan; rai.bhattacharya.in@gmail.com

Text of the contribution: A mix of human-written and AI-generated.
Human understanding: "All parts" only after both authors have read every proof; otherwise "Some parts, but not all".

Provenance statement: The constructions on the two statements (F2) and (F3'), the search for a closure of the Hodge conjecture, the text, the figures, the Lean 4 file and the Python, Julia, C, C++ and shell programs were carried out by Deep Bhattacharjee with the help of AI assistance (Claude, Anthropic) in the Claude Code environment. Every hand proof was read against the cited literature; every finite quantity in the paper is recomputed by programs in at least two languages, and the combinatorial and arithmetic ones are proved in Lean 4 (sixty-two theorems, fifty-two free of every axiom, two on propext and Quot.sound, eight on propext). No proved statement rests on a floating-point computation; the enumerations of the paper (Proposition VI.13, Remark VI.25) and the linear-programming bounds that decide nine of the ten remaining arrangements of shifts on E_0^8 and leave the tenth open (Remark VI.39, solved in double precision) are stated as computations of the archive and no proved statement rests on them. Release v2.7.0 adds Propositions VI.37, VI.40, VIII.3 and VIII.4 with hand proofs, Corollary VI.38, and Remarks VI.39 and VI.41. The AI did not prove (F2), (F3') or the Hodge conjecture; the paper states at which step each construction stops. Four slips found by the machine checks were corrected before release (a Hasse invariant at 2, a Picard number of a twist family, the dimension of a dihedral Hecke algebra, the sign of the square of the Fricke isogeny, which is a complex and not a real multiplication). Both authors approved the final version.

Tools used: Anthropic - Claude (Claude Code); Lean community - Lean 4 (no Mathlib); Python; Julia; C; C++; shell.
arXiv identifier: none (not posted on arXiv).
Formalization: https://github.com/creelie/fermat-hodge-/blob/main/lean/HodgeClosure.lean (archived at Zenodo, release v2.7.0: DOI to be added when assigned; concept DOI of all versions https://doi.org/10.5281/zenodo.23439577)

Source files or ZIP: HodgeConjecture_tex.zip (the folder paper/ with main.tex, the section files, bibliography.tex and figures/; compiles with latexmk -pdf main.tex). Do not upload hcfinal.zip or Lean files here.
AI provenance files: AI_PROVENANCE_HodgeConjecture.md
License: CC BY 4.0

Data availability (in the paper): LaTeX source, programs and the Lean 4 file archived at Zenodo, release v2.7.0 (version DOI to be added when assigned), cited in the paper by the concept DOI 10.5281/zenodo.23439577; repository https://github.com/creelie/fermat-hodge-; the folder preprints holds the PDF only.
AI disclosure (in the paper, Data and code availability): Deep Bhattacharjee carried out the constructions on (F2) and (F3') and the Lean, Julia, C, C++, Python and shell verifications with the help of AI assistance (Claude, Anthropic); both authors approved the final version. No separate AI declaration.
Funding: none. Competing interests: none.
Device folder: D:\Hexagon\strings_seeds_hodge_YM_Bllm-anaxia\hodge.
