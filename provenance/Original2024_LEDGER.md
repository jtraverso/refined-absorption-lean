# Ledger: the original article (Delcourt–Postle, arXiv:2402.17855v1)

All files are in `RequestProject/Original2024/`, namespace `RefinedAbsorption.Original2024`.
The survey interface (`RequestProject/Final.lean`, `RequestProject/Multigraph/Existence.lean`,
survey arXiv:2510.19978) is unchanged and still builds.  Theorem numbers below are those of the
**2024 article**.

Caveat: the statements in `Defs.lean` should be checked against the article, especially the
exact form of Theorem 3.8.

## Interface (`Defs.lean`)

| Article item | Lean | Notes |
| --- | --- | --- |
| Ambient vertex set | parameter `U`, `IsRGraphOn r U G` | Every structure takes the ambient set `U` as a parameter (`univ : Finset (Fin n)` in the theorems). The condition `V(X)=V(A)` means "same ambient set", **not** the stronger `vertexSet X = vertexSet A` that the survey's `IsRefiner` uses. |
| Def. 1.5 omni-absorber | `IsOmniAbsorberOn q r U X A F QA` | decomposition family `F` and function `QA` |
| Def. 1.6 `C`-refined | `IsRefinedOmni C X A F` | every edge of `X ∪ A` lies in `≤ C` cliques of `F` |
| (structural extra) | `OneXEdgePerClique r X F` | |
| Def. 1.8 refiner | `IsRefinerOn q r U X R F QR` | |
| Def. 1.9 `C`-refined refiner | `IsRefinedRefinerOn C X R F` | `≤ C` edges, `≤ C` vertices per piece, edge multiplicity `≤ C` |
| (structural extra) | `OneXEdgePerPiece X F` | |
| Def. 1.10 multi-refiner | `IsMultiRefinerOn q r C U ends X R 𝒲` | labelled copies `E → Finset (Fin n)` |
| Thm 1.4 (GKLO absorbers) | `Theorem_1_4 := AbsorberExistence` | |
| Thm 1.7 | `Theorem_1_7_for q r`, `Theorem_1_7_strong_for`, `Theorem_1_7` | host `G`: `IsRGraph r G`, `δ_{r-1}(G) ≥ (1-ε)n`, `X ⊆ G`, `Δ(X) ≤ D ≤ n/C`; conclusion has `A ⊆ G` and `Δ(A) ≤ C·max(D, n^{1-1/r} log n)` |
| Thm 1.11 | `Theorem_1_11_for`, `Theorem_1_11_strong_for`, `Theorem_1_11` | same host hypotheses; `R ⊆ G`; the strong form adds one `X`-edge per piece and the family degree bound |
| Thm 3.8 | `MultiRefinerConclusion q r`, `Theorem_3_8_for q r` | inductive form: (1.11 in all lower uniformities) → conclusion |
| Thm 6.1 | `Theorem_6_1_for`, `Theorem_6_1` | `λ = 1`, `δ_{r-1}(G) ≥ (1-ε)n`, `G` divisible, `n ≥ n₀` ⇒ decomposition |

The `D`-form (`Δ(X) ≤ D ≤ n/C`, conclusion in terms of `D`) is equivalent to the literal form:
take `D = Δ(X)`.

## Theorem-by-theorem status

| Article item | Lean theorem | Status |
| --- | --- | --- |
| Thm 1.4 | `theorem_1_4` | **proved** (in this project: `Absorber17.absorberExistence`); not an axiom |
| Thm 3.8 (with flatness) | `theorem_3_8_flat`, `multiRefinerFlat` (`FlatOne.lean`) | **proved** for all `q > r ≥ 1`. The conclusion `MultiRefinerFlatConclusion` adds the output: for **every** `Y` with `|Y| ≥ n/3`, `R` is `(r-1)`-flat to `Y` (`IsFlatTo`). The corollary `MultiRefinerFlatConclusion.exists_inside` covers the other reading. |
| Thm 3.8 | `theorem_3_8 : ∀ q r, 1 ≤ r → r < q → Theorem_3_8_for q r` | **proved without flatness** (superseded by `theorem_3_8_flat`). Proved outright (the induction hypothesis is not used), including the strong invariants: one copy of `X` per piece, `Δ(R)` and family degree `≤ C·B`, multiplicity, and ambient support. **Gap:** the article's `Y`-flatness output (`R` is `(r-1)`-flat to a set `Y` with `|Y| ≥ n/3`) is **not** part of `MultiRefinerConclusion`. |
| Thm 1.11 | `theorem_1_11`, `theorem_1_11_strong` | **proved** for all `q > r ≥ 1`, inside a dense host `G` (not only in `K_n^r`). The strong form keeps one `X`-edge per piece and the family degree bound. |
| Thm 1.7 | `theorem_1_7`, `theorem_1_7_strong` | **proved** for all `q > r ≥ 1`, inside a dense host `G`, with `A ⊆ G`. The strong form keeps one `X`-edge per clique of the family. |
| Thm 6.1 | `theorem_6_1` | **proved** for all `q > r ≥ 1` |

### Theorem 1.4 assumptions used

The only external absorber input is `AbsorberExistence`: every `K_q^r`-divisible `r`-graph has a
`K_q^r`-absorber.  It is used through bounded attached absorbers (`Absorber17.absorberLibrary`,
`exists_boundedAttachedAbsorbers`), i.e. absorbers of size bounded in terms of `q, r` for the
finitely many isomorphism types of refiner pieces.  It is proved in the project, so nothing is
assumed.

## Build / axioms

* The full project builds without errors.
* No `sorry`, `admit`, `native_decide`, `axiom` or `implemented_by` occurs in
  `RequestProject/Original2024/`.
* `checks/Original2024Axioms.lean` prints the axioms of `theorem_1_4`, `theorem_3_8`,
  `theorem_1_11`, `theorem_1_11_strong`, `theorem_1_7`, `theorem_1_7_strong` and `theorem_6_1`.
  Each depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Continuation: flatness, corollaries

### Theorem 3.8 with flatness (`FlatChain.lean`, `Flat.lean`, `FlatOne.lean`)

| Lean | Content |
| --- | --- |
| `PlacedOutM`, `placedStep_of_levelS_M`, `placedChainS_M`, `multiStageS_M` | the sparse refine-down stage and its chain of flat levels, with the extra output "every new copy meets the reserve `Z`" |
| `IsFlatTo i Y ends R` | every copy of `R` has at most `i` vertices outside `Y` |
| `pdeg_le_of_clique` | piece degrees of clique pieces are bounded by copy degrees |
| `multiRefinerFlat_two_le` | `r ≥ 2`: split `Y = Z ⊔ P`; refine down into `Z` (new copies meet `Z`); Theorem 3.7 for the residue inside `Z ∪ P` (new copies meet `P`); compose |
| `hostChainPool`, `multiRefinerFlat_one` | `r = 1`: chain refiner with the new vertices in `Y` |
| **`theorem_3_8_flat`**, `multiRefinerFlat` | Theorem 3.8 with flatness, all `q > r ≥ 1` |
| `MultiRefinerFlatConclusion.toConclusion`, `.exists_inside` | the version without flatness; the other reading of flatness |

### Corollaries (`Corollaries.lean`)

| Lean | Content |
| --- | --- |
| `decomposition_complete_minus_sparse` | `K_n^r \ H` has a `K_q^r`-decomposition when `Δ(H) ≤ εn` and `K_n^r \ H` is divisible (from Thm 6.1) |
| `theorem_1_1_steiner` | Existence Conjecture for Steiner systems, from Thm 6.1 |
| `theorem_1_1` | Existence Conjecture for every `λ ≥ 1` |
| `theorem_3_7_local` | Theorem 3.7 (local flat form, clique pieces), all `2 ≤ k < q` |

All of the above depend only on `propext`, `Classical.choice` and `Quot.sound`.
