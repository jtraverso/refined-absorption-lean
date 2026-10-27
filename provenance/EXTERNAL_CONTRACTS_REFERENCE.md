# Referencias externas para el ensamblaje cuantitativo

Copias de referencia de GitHub verificadas el 26 de octubre de 2026. Estas copias no son modulos para importar al proyecto; sirven para transcribir interfaces como hipotesis explicitas. Los teoremas ya tienen pruebas en sus repositorios. No hay que reconstruir sus bibliotecas.

## pippenger-spencer Solution.lean

Fuente: https://github.com/jtraverso/pippenger-spencer/blob/b19273396d369332fb489fe07e61e27c9e7f9233/Solution.lean
Blob SHA: 5e56001a4a646721b6c6a889453b212e374cb1a1

```lean
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import PseudorandomLib.PippengerSpencer.Main
public import PseudorandomLib.PippengerSpencer.Polynomial

/-!
# Proofs of the statements in `Challenge.lean`

The definitions are copied verbatim from `Challenge.lean`; each theorem is closed by the
corresponding theorem of `PseudorandomLib` (namespace `Pseudorandom`), whose definitions are
literally the same.
-/

@[expose] public section

namespace PippengerSpencer

open Finset

section Hypergraphs

variable {V : Type*} [DecidableEq V]

/-- `H` is `r`-uniform: every edge has exactly `r` vertices. -/
def IsUniform (H : Finset (Finset V)) (r : ℕ) : Prop := ∀ e ∈ H, e.card = r

/-- The degree `deg_H(v)`: the number of edges containing `v`. -/
def degree (H : Finset (Finset V)) (v : V) : ℕ := (H.filter (fun e => v ∈ e)).card

/-- The codegree `deg_H(uv)`: the number of edges containing both `u` and `v`. -/
def codegree (H : Finset (Finset V)) (u v : V) : ℕ :=
  (H.filter (fun e => u ∈ e ∧ v ∈ e)).card

/-- A proper edge colouring of `H` with `m` colours: edges of the same colour are disjoint. -/
def IsProperEdgeColouring (H : Finset (Finset V)) (m : ℕ) (c : Finset V → Fin m) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → c e = c f → Disjoint e f

end Hypergraphs

/-- **The Pippenger–Spencer theorem.** For `r ≥ 2` and `ε > 0` there are `μ > 0` and `D₀`
such that every `r`-uniform hypergraph whose degrees lie in `[(1 - μ) D, D]` and whose codegrees
are at most `μ D`, with `D ≥ D₀`, has a proper edge colouring with at most `(1 + ε) D` colours. -/
theorem pippenger_spencer (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ D₀ : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V))
      (D : ℝ), D₀ ≤ D → IsUniform H r →
      (∀ v, (1 - μ) * D ≤ degree H v ∧ (degree H v : ℝ) ≤ D) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ μ * D) →
      ∃ (m : ℕ) (c : Finset V → Fin m), (m : ℝ) ≤ (1 + ε) * D ∧ IsProperEdgeColouring H m c :=
  Pseudorandom.pippenger_spencer r hr ε hε

/-- **Chromatic index under polynomial codegrees.** For `r ≥ 2` and `0 < δ < 1` there are
`γ > 0` and `D₀` such that every `r`-uniform hypergraph with maximum degree at most `D ≥ D₀`,
codegrees at most `D^{1-δ}` and at most `exp(D^γ)` edges has a proper edge colouring with at
most `D + D^{1-γ}` colours. -/
theorem chromatic_index_polynomial (r : ℕ) (hr : 2 ≤ r) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ D₀ : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V))
      (D : ℝ), D₀ ≤ D → IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ D ^ (1 - δ)) →
      (H.card : ℝ) ≤ Real.exp (D ^ γ) →
      ∃ (m : ℕ) (c : Finset V → Fin m), (m : ℝ) ≤ D + D ^ (1 - γ) ∧
        IsProperEdgeColouring H m c :=
  Pseudorandom.chromatic_index_polynomial r hr δ hδ0 hδ1

end PippengerSpencer

```

## nash-williams-lean Challenge.lean

Fuente: https://github.com/jtraverso/nash-williams-lean/blob/2603197abdbf0a600ec663f6f046f70fbd209d4a/Challenge.lean
Blob SHA: bb8c4ffb2e2183ef0585eceda43a63767a2a063a

```lean
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# The Nash–Williams triangle-decomposition theorem

* `NashWilliamsTheorem.nash_williams`: **the Nash–Williams theorem for large graphs
  (Delcourt–Postle, Theorem 1.8).** There is `N` such that every finite simple graph on
  `n ≥ N` vertices that is triangle-divisible (`3 ∣ e(G)` and every degree even) and has minimum
  degree `δ(G) ≥ 3n/4` (stated as `3 n ≤ 4 δ(G)`) has a triangle decomposition: a family of
  triangles of `G` such that every edge of `G` lies in exactly one of them.
* `NashWilliamsTheorem.fractional_nash_williams`: **the fractional threshold (Delcourt–Postle,
  Theorem 1.4).** Every finite simple graph with `3 n ≤ 4 δ(G)` has a fractional triangle
  decomposition: nonnegative real weights on vertex sets such that, for every edge, the weights
  of the triangles containing it sum to one. Neither divisibility nor large order is assumed.
* `NashWilliamsTheorem.fractional_stability`: **fractional stability (Delcourt–Postle,
  Theorem 1.6), with an order threshold.** Some `σ₀ > 0` works so that for every
  `0 < σ ≤ σ₀` there are `ε > 0` and `n₀`: every graph on `n ≥ n₀` vertices with
  `δ(G) ≥ (3/4 − ε) n` has a fractional triangle decomposition or is `σ`-extremal
  (`NashWilliams18.IsExtremal`: at least `(1 − σ) n` vertices have degree at most
  `(3/4 + σ) n`, and some cut has at least `(1 − σ) n²/4` edges).

The definitions below are reproduced verbatim, with the same names, from
`RequestProject/NashWilliamsBasic.lean` (namespace `NashWilliams`) and
`RequestProject/NW18/Defs.lean` (namespace `NashWilliams18`) of the formalization.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

namespace NashWilliams

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A *triangle* of `G` is a 3-clique, i.e. a 3-element set of pairwise adjacent vertices. -/
abbrev IsTriangle (G : SimpleGraph V) (t : Finset V) : Prop := G.IsNClique 3 t

/-- A *triangle decomposition* (`K₃`-decomposition) of `G`: a family `D` of triangles of `G`
such that every edge of `G` lies in exactly one triangle of `D`
(equivalently, the edge sets of the triangles of `D` partition `E(G)`). -/
def IsTriangleDecomposition (G : SimpleGraph V) (D : Finset (Finset V)) : Prop :=
  (∀ t ∈ D, IsTriangle G t) ∧ ∀ u v, G.Adj u v → ∃! t, t ∈ D ∧ u ∈ t ∧ v ∈ t

/-- `G` admits a triangle decomposition. -/
def HasTriangleDecomposition (G : SimpleGraph V) : Prop :=
  ∃ D, IsTriangleDecomposition G D

/-- `G` is `K₃`-divisible: `3 ∣ e(G)` and every vertex has even degree. -/
def IsTriangleDivisible (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)

/-- A *fractional triangle decomposition* of `G`: a non-negative weighting of the triangles
of `G` such that, for every edge, the total weight of the triangles containing it is `1`. -/
def IsFractionalTriangleDecomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
    ∀ u v, G.Adj u v → ∑ t ∈ G.cliqueFinset 3 with u ∈ t ∧ v ∈ t, w t = 1

/-- `G` admits a fractional triangle decomposition. -/
def HasFractionalTriangleDecomposition (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ w, IsFractionalTriangleDecomposition G w

end NashWilliams

namespace NashWilliams18

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of edges of `G` with exactly one end in `S` (the cut `(S, V ∖ S)`). -/
def cutSize (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∉ S)).card

/-- **`σ`-extremal** (Definition 12.2): (i) at least `(1 - σ) n` vertices have degree at most
`(3/4 + σ) n`, and (ii) the maximum cut of `G` has at least `(1 - σ) n² / 4` edges. -/
def IsExtremal (σ : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (1 - σ) * Fintype.card V ≤
      ((univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V)).card : ℝ) ∧
    ∃ S : Finset V, (1 - σ) * (Fintype.card V : ℝ) ^ 2 / 4 ≤ (cutSize G S : ℝ)

end NashWilliams18

namespace NashWilliamsTheorem

open Finset

/-- **The Nash–Williams theorem for large graphs (Delcourt–Postle, Theorem 1.8).** Every
sufficiently large triangle-divisible graph with `3 n ≤ 4 δ(G)` has a triangle decomposition. -/
theorem nash_williams :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree →
          NashWilliams.HasTriangleDecomposition G := by
  sorry

/-- **The fractional threshold (Delcourt–Postle, Theorem 1.4).** Every finite simple graph with
`3 n ≤ 4 δ(G)` has a fractional triangle decomposition. -/
theorem fractional_nash_williams {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) :
    ∃ w : Finset V → ℝ, (∀ t, 0 ≤ w t) ∧
      ∀ u v, G.Adj u v → ∑ t ∈ G.cliqueFinset 3 with u ∈ t ∧ v ∈ t, w t = 1 := by
  sorry

/-- **Fractional stability (Delcourt–Postle, Theorem 1.6), with an order threshold.** There is
`σ₀ > 0` such that for every `0 < σ ≤ σ₀` there are `ε > 0` and `n₀` such that every graph on
`n ≥ n₀` vertices with `δ(G) ≥ (3/4 − ε) n` either has a fractional triangle decomposition or is
`σ`-extremal. -/
theorem fractional_stability :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, 0 < σ → σ ≤ σ₀ → ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W] (Gr : SimpleGraph W) [DecidableRel Gr.Adj],
        n₀ ≤ Fintype.card W → (3 / 4 - ε) * (Fintype.card W : ℝ) ≤ (Gr.minDegree : ℝ) →
        ¬ NashWilliams.HasFractionalTriangleDecomposition Gr →
        NashWilliams18.IsExtremal σ Gr := by
  sorry

end NashWilliamsTheorem

```

## nash-williams-lean Solution.lean

Fuente: https://github.com/jtraverso/nash-williams-lean/blob/2603197abdbf0a600ec663f6f046f70fbd209d4a/Solution.lean
Blob SHA: 1b9e307532c82b5bb3cc603758252d3fcb7722cd

```lean
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import RequestProject.NW18.PaperIIAssembly
public import RequestProject.Fractional.Final
public import RequestProject.FracStab.Main

@[expose] public section

/-!
# Proofs of the statements in `Challenge.lean`

The definitions `NashWilliams.IsTriangle`, `IsTriangleDecomposition`, `HasTriangleDecomposition`,
`IsTriangleDivisible`, `IsFractionalTriangleDecomposition` and `HasFractionalTriangleDecomposition`
are those of `RequestProject/NashWilliamsBasic.lean`, and `NashWilliams18.cutSize` and
`IsExtremal` those of `RequestProject/NW18/Defs.lean`; they are reproduced verbatim in
`Challenge.lean`.

The main theorem is `NashWilliams18.PaperI.nash_williams_via_paperII`
(`RequestProject/NW18/PaperIIAssembly.lean`), which follows Delcourt–Postle's division into
extremal and non-extremal cases: the extremal residuals are decomposed with the typed absorption
inputs `PaperII.theorem146_F0`, `theorem147_F1` and `theorem147_F2` (Paper II of the series,
developed under `PartitionedTriangleAbsorption/`), and the non-extremal case with a protected
covering-round argument (`roundUnivSpec124_holds`), without assuming Delcourt–Postle's Theorem
13.16. The fractional threshold is `NashWilliams.Frac.exists_fractional_weights`
(`RequestProject/Fractional/Final.lean`), by a dual discharging argument and Farkas' lemma, and
fractional stability is `NashWilliams.Frac.theorem_1_6_proof` (`RequestProject/FracStab/Main.lean`).
-/

namespace NashWilliamsTheorem

open Finset

/-- **The Nash–Williams theorem for large graphs (Delcourt–Postle, Theorem 1.8).** Every
sufficiently large triangle-divisible graph with `3 n ≤ 4 δ(G)` has a triangle decomposition. -/
theorem nash_williams :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree →
          NashWilliams.HasTriangleDecomposition G :=
  NashWilliams18.PaperI.nash_williams_via_paperII

/-- **The fractional threshold (Delcourt–Postle, Theorem 1.4).** Every finite simple graph with
`3 n ≤ 4 δ(G)` has a fractional triangle decomposition. -/
theorem fractional_nash_williams {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) :
    ∃ w : Finset V → ℝ, (∀ t, 0 ≤ w t) ∧
      ∀ u v, G.Adj u v → ∑ t ∈ G.cliqueFinset 3 with u ∈ t ∧ v ∈ t, w t = 1 :=
  NashWilliams.Frac.exists_fractional_weights G hδ

/-- **Fractional stability (Delcourt–Postle, Theorem 1.6), with an order threshold.** There is
`σ₀ > 0` such that for every `0 < σ ≤ σ₀` there are `ε > 0` and `n₀` such that every graph on
`n ≥ n₀` vertices with `δ(G) ≥ (3/4 − ε) n` either has a fractional triangle decomposition or is
`σ`-extremal. -/
theorem fractional_stability :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, 0 < σ → σ ≤ σ₀ → ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W] (Gr : SimpleGraph W) [DecidableRel Gr.Adj],
        n₀ ≤ Fintype.card W → (3 / 4 - ε) * (Fintype.card W : ℝ) ≤ (Gr.minDegree : ℝ) →
        ¬ NashWilliams.HasFractionalTriangleDecomposition Gr →
        NashWilliams18.IsExtremal σ Gr :=
  NashWilliams.Frac.theorem_1_6_proof

end NashWilliamsTheorem

```

