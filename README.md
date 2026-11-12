<p align="center"><img src="assets/banner.svg" alt="Two Abelian Statements Equivalent to the Hodge Conjecture" width="100%"></p>

<p align="center">
  <a href="https://doi.org/10.5281/zenodo.23439577"><img src="https://img.shields.io/badge/DOI-10.5281%2Fzenodo.23439577-22d3ee?style=for-the-badge" alt="DOI"></a>
  <a href="papers/HodgePaper.pdf"><img src="https://img.shields.io/badge/paper-PDF-f472b6?style=for-the-badge" alt="paper"></a>
  <img src="https://img.shields.io/badge/Lean_4-63_theorems-7c5cff?style=for-the-badge" alt="Lean 4">
  <img src="https://img.shields.io/badge/Julia-665_checks-34d399?style=for-the-badge" alt="Julia">
  <img src="https://img.shields.io/badge/license-MIT-f59e0b?style=for-the-badge" alt="MIT">
</p>

**Deep Bhattacharjee** (corresponding author, head of the project), Ushashi Bhattacharya.

| Proved | Open |
| :--- | :--- |
| The Hodge conjecture is equivalent to two statements on abelian varieties, (F2) and (F3′) | (F2) and (F3′), hence the Hodge conjecture |
| The algebraic locus of a flat Hodge class is the whole base or a meagre set | Which alternative holds for the Mumford link class |
| For every real quadratic field, K3 surfaces with that real multiplication satisfying the conjecture on all powers | The K3 surfaces of Picard number 13 with real multiplication by a cubic field of Galois group S₃ |
| The link classes of Mumford fourfolds are algebraic on a dense set of special points | The very general point |

| Folder | Contents | Run |
| :--- | :--- | :--- |
| [`papers/`](papers) | the paper | |
| [`lean/`](lean) | Lean 4 file, no Mathlib | `lean lean/HodgeClosure.lean` |
| [`julia/`](julia) | 27 check programs | `julia julia/run_all.jl` |
