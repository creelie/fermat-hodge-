# Dense Algebraic Loci of Hodge Classes: journal package (release v2.7.0)

Authors: Deep Bhattacharjee (corresponding, ORCID 0000-0003-0466-750X) and Ushashi Bhattacharya (ORCID 0009-0002-2254-3914).

This folder contains three files and the checksum list:

- `HodgeConjecture-journal.pdf` is the manuscript, 81 pages in one column. It is `paper/main_journal.tex` of https://github.com/creelie/fermat-hodge-, and it has the same content as the 62-page two-column archive version.
- `HodgeConjecture-journal-tex.zip` is the LaTeX source with the figures. Running `latexmk -pdf main_journal.tex` compiles it on its own, with no errors, no overfull or underfull boxes and no undefined references.
- `SHA256SUMS` lists the checksums.

## Release

The code archive is release v2.7.0 of the repository. The paper cites it by its GitHub release page, https://github.com/creelie/fermat-hodge-/releases/tag/v2.7.0. Publish the release from this prefilled link:

https://github.com/creelie/fermat-hodge-/releases/new?tag=v2.7.0&target=main&title=v2.7.0%3A%20seven%20shifts%20on%20E0%5E8%2C%20the%20genus-four%20Prym%20map%2C%20residues%20and%20mass&body=Release%20v2.7.0%20of%20the%20paper%20Dense%20Algebraic%20Loci%20of%20Hodge%20Classes%20%28Deep%20Bhattacharjee%2C%20Ushashi%20Bhattacharya%29%2C%20with%20its%20programs%20and%20Lean%204%20certificate.%0A%0ANew%20in%20this%20release%3A%0A-%20Proposition%20VI.37%20and%20Corollary%20VI.38%3A%20convolutions%20of%20the%20128%20Weil%20line%20bundles%20on%20E_0%5E8%20whose%20shifts%20lie%20in%20seven%20consecutive%20integers%20fail%20the%20polarised%20criterion%20in%2018%20of%20the%2028%20arrangements%3B%20Remark%20VI.39%20records%20linear-programming%20bounds%20that%20decide%209%20of%20the%20other%2010%20%28least%20value%20125.8%20against%20104%29%20and%20leave%20one%20open%2C%20a%20computation%20no%20statement%20uses.%0A-%20Proposition%20VI.40%3A%20at%20the%20explicit%20curve%20x%5E3%20%2B%20y%5E3%20%2B%201%20%2B%20lambda%20x%5E3%20y%5E3%20%3D%200%20the%20Prym%20map%20of%20etale%20cyclic%20triple%20covers%20of%20genus-four%20curves%20is%20a%20local%20isomorphism%20onto%20the%20Weil%20domain%20of%20Q%28sqrt%20-3%29%20at%20n%20%3D%203.%0A-%20Remark%20VI.41%3A%20over%20twelve%20cubic%20fields%20the%20count%20for%20sextic%20CM%20fields%20excludes%20no%20integral%20character.%0A-%20Section%20VIII.C%2C%20Propositions%20VIII.3%20and%20VIII.4%3A%20residues%20of%20complete%20intersections%2C%20and%20the%20Hodge%20conjecture%20for%20a%20class%20as%20the%20vanishing%20of%20a%20mass%20gap.%0A-%20paper%2Fpaper1%20%28PDF%29%20and%20paper%2Fpaper2%20%28LaTeX%20zip%29.%0A%0A%28F2%29%2C%20%28F3%27%29%20and%20the%20Hodge%20conjecture%20remain%20open.


## What the paper claims

- The Hodge conjecture is equivalent to the conjunction of two statements about abelian varieties, (F2) and (F3').
- The locus where either statement is known is dense in every family. It is either the whole family or a meagre set.
- Real multiplications by sqrt 6, Q(zeta_7)^+ and Q(zeta_9)^+ are algebraic on explicit families of K3 surfaces.
- The Hodge conjecture holds on every power and every Hilbert scheme of the Fricke families of levels 5 and 7.
- New in this version:
  - Convolutions on E_0^8 with shifts in seven consecutive integers fail the polarised criterion in 18 of the 28 arrangements. A computation, which the paper states as such, decides 9 more and leaves 1 open.
  - An explicit genus-four curve makes the Prym map of étale triple covers a local isomorphism.
  - The residue criterion holds, and the conjecture for a class is equivalent to the vanishing of a mass gap.

The paper does not claim the Hodge conjecture, and (F2) and (F3') remain open.

## Where to send it

The journal must charge no fee on its subscription route and must accept AI use that is disclosed. The publishers' pages could not be opened from this session, so check both conditions on the journal page before submitting.

1. **Mathematische Zeitschrift** (Springer). It is hybrid, with no charge unless open access is chosen. Springer allows large language models if their use is documented in the manuscript, and the Data availability section does this. The paper on Fermat fourfolds (creelie/e84hc) is prepared for Mathematische Annalen, so submitting this one to a different journal avoids two related submissions at the same editor.
2. **Mathematische Annalen** (Springer). It has the same terms.
3. **Journal of Algebraic Geometry** (University Press). It has no page charges. Confirm its AI policy first.

## Cover letter

Dear Editor,

We submit the manuscript "Dense Algebraic Loci of Hodge Classes" for consideration.

The paper proves that the Hodge conjecture is equivalent to two statements about abelian varieties, (F2) and (F3'), where (F2) is the conjecture for abelian varieties. It also proves that the locus on which either statement holds is dense in every family and is either the whole family or a meagre set. It then proves the conjecture in explicit cases: on every power and every Hilbert scheme of the K3 surfaces of the Fricke families of levels 5 and 7, and for the algebraicity of real multiplication by sqrt 6 and by two cubic fields on explicit families.

For each of the two statements the paper builds the object the statement needs next and proves where that object stops. Among these results, convolutions of Weil line bundles on E_0^8 with shifts in seven consecutive integers fail the semiregularity criterion in eighteen of twenty-eight arrangements. An explicit curve of genus four makes the Prym map of étale triple covers a local isomorphism onto a Weil domain. For mass-minimising currents, the conjecture for a class is exactly the vanishing of a mass gap, and Kollár's hypersurfaces show that the multiplier cannot be removed.

Every proof is written by hand. The finite quantities are recomputed by programs, and the arithmetic ones are proved in Lean 4. The programs and the Lean file are published as GitHub release v2.7.0, https://github.com/creelie/fermat-hodge-/releases/tag/v2.7.0. The paper does not claim the Hodge conjecture.

The use of AI assistance (Claude, Anthropic) is stated in the Data availability section. There is no funding and there are no competing interests.

Yours sincerely,
Deep Bhattacharjee and Ushashi Bhattacharya
