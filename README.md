<p align="center"><img src="assets/banner.svg" alt="Hodge Classes on K3 Powers and Sixfolds" width="100%"></p>

<p align="center">
  <a href="https://doi.org/10.5281/zenodo.23439577"><img src="https://img.shields.io/badge/DOI-10.5281%2Fzenodo.23439577-22d3ee?style=for-the-badge" alt="DOI"></a>
  <a href="papers/HodgePaper.pdf"><img src="https://img.shields.io/badge/paper-PDF-f472b6?style=for-the-badge" alt="paper"></a>
  <img src="https://img.shields.io/badge/Lean_4-90_theorems-7c5cff?style=for-the-badge" alt="Lean 4">
  <img src="https://img.shields.io/badge/Julia-842_checks-34d399?style=for-the-badge" alt="Julia">
  <img src="https://img.shields.io/badge/license-MIT-f59e0b?style=for-the-badge" alt="MIT">
</p>

**Deep Bhattacharjee** (corresponding author, head of the project), Ushashi Bhattacharya.

| Proved | Open |
| :--- | :--- |
| The Hodge conjecture on all powers of every K3 surface of Picard number at least 17 | The Hodge conjecture, hence (F2) and (F3′) |
| The Hodge conjecture on a dense union of curves in every family of K3 surfaces of transcendental rank at least 8 with real quadratic multiplication | The very general member of these families |
| Weil classes are algebraic on every abelian sixfold of Weil type with complex multiplication | Weil classes on the very general non-split sixfold |
| Weil classes on a dense union of special subvarieties of every family of non-split Weil sixfolds | A decomposition of the Weil class meeting the necessary condition of the paper |

| Folder | Contents | Run |
| :--- | :--- | :--- |
| [`papers/`](papers) | the paper | |
| [`lean/`](lean) | Lean 4 file, no Mathlib | `lean lean/HodgeClosure.lean` |
| [`julia/`](julia) | 43 check programs | `julia julia/run_all.jl` |
