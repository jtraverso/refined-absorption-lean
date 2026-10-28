/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RefinedAbsorption.Faithful2024.Section1

/-!
# Theorem 1.10 (refined efficient omni-absorber), faithful form

The registry endpoint for Theorem 1.10 of Delcourt–Postle, *Proof of the Existence Conjecture via
refined absorption*, stated with the omni-absorber of Definition 1.5 and the refinedness of
Definition 1.6 (`Faithful2024.IsOmniAbsorber`, `Faithful2024.IsCRefinedOmni`): every member of the
decomposition family is a copy of `K_q^r` in `X ∪ A` containing at most one edge of `X`.

It is derived from the faithful Theorem 1.7 on `Fin n` (`Faithful2024.theorem_1_7_fin`) with the
complete `r`-graph `K_n^r` as host.  For `n` below a constant the degree bound `D ≤ n / C` forces
`X` to have no edges, and the empty absorber works.
-/

@[expose] public section

namespace RefinedAbsorption.Final

open Finset RefinedAbsorption

/-- **Theorem 1.10 (Refined efficient omni-absorber, Delcourt–Postle)**, with the omni-absorber
and refinedness of Definitions 1.5 and 1.6 of arXiv:2402.17855: for `q > r ≥ 1` there is `C ≥ 1` such that if `X` is an `r`-graph on `Fin n` with
`Δ(X) ≤ D ≤ n / C`, then there is a `C`-refined `K_q^r`-omni-absorber `A` for `X` (decomposition
family `𝓗` of copies of `K_q^r` in `X ∪ A`, each with at most one edge of `X`) with
`Δ(A) ≤ C · max(D, n^{1-1/r} log n)`. -/
def RefinedEfficientOmniAbsorberFaithful : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∃ C : ℕ, 1 ≤ C ∧
    ∀ (n : ℕ) (X : Faithful2024.HGraph (Fin n)) (D : ℝ),
      X.verts = univ → X.IsUniform r → (X.maxDeg r : ℝ) ≤ D → D ≤ n / C →
      ∃ (A : Faithful2024.HGraph (Fin n)) (𝓗 : Finset (Finset (Fin n)))
        (QA : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
        Faithful2024.IsOmniAbsorber q r X A 𝓗 QA ∧ Faithful2024.IsCRefinedOmni r C X A 𝓗 ∧
          (A.maxDeg r : ℝ) ≤ C * max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n)

/-- In `K_n^r`, every `(r-1)`-set lies in at least `n - (r - 1)` edges. -/
theorem le_deg_complete {n r : ℕ} {S : Finset (Fin n)} (hS : S.card + 1 = r) :
    n - (r - 1) ≤ deg (univ.powersetCard r) S := by
  have hsub : (univ \ S).image (fun x => insert x S) ⊆
      (univ.powersetCard r).filter (fun e => S ⊆ e) := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := mem_image.1 he
    have hxS : x ∉ S := (mem_sdiff.1 hx).2
    refine mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, ?_⟩, subset_insert _ _⟩
    rw [card_insert_of_notMem hxS]
    omega
  have hinj : Set.InjOn (fun x => insert x S) ↑(univ \ S) := by
    intro x hx y _ hxy
    have hxS : x ∉ S := (mem_sdiff.1 (mem_coe.1 hx)).2
    have hxy' : insert x S = insert y S := hxy
    have : x ∈ insert y S := by rw [← hxy']; exact mem_insert_self x S
    rcases mem_insert.1 this with h | h
    · exact h
    · exact absurd h hxS
  have := card_le_card hsub
  rw [card_image_of_injOn hinj, card_univ_sdiff, Fintype.card_fin] at this
  unfold deg
  omega

/-- An `r`-graph with an edge has `Δ(X) ≥ 1`. -/
theorem one_le_maxDeg {n r : ℕ} (hr : 1 ≤ r) {X : Faithful2024.HGraph (Fin n)}
    (hXv : X.verts = univ) (hXu : X.IsUniform r) {e : Finset (Fin n)} (he : e ∈ X.edges) :
    1 ≤ X.maxDeg r := by
  obtain ⟨S, hSe, hScard⟩ :=
    Finset.exists_subset_card_eq (show r - 1 ≤ e.card by rw [(hXu e he).1]; omega)
  have hdeg : 1 ≤ deg X.edges S := card_pos.2 ⟨e, mem_filter.2 ⟨he, hSe⟩⟩
  have hmem : S ∈ X.verts.powersetCard (r - 1) :=
    mem_powersetCard.2 ⟨by rw [hXv]; exact subset_univ _, hScard⟩
  exact hdeg.trans (le_sup (f := deg X.edges) hmem)

/-- **Theorem 1.10 (Refined efficient omni-absorber)**, faithful form. -/
theorem theorem_1_10_faithful : RefinedEfficientOmniAbsorberFaithful := by
  intro q r hr hrq
  obtain ⟨C, hC, ε, hε, hε1, h⟩ := Faithful2024.theorem_1_7_fin q r hr hrq
  set N : ℕ := ⌈((r : ℝ) - 1) / ε⌉₊ + 1 with hN
  refine ⟨max C N, le_max_of_le_left hC, ?_⟩
  intro n X D hXv hXu hXD hDn
  have hD0 : 0 ≤ D := (Nat.cast_nonneg _).trans hXD
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hCN : (C : ℝ) ≤ ((max C N : ℕ) : ℝ) := by exact_mod_cast le_max_left C N
  have hmax0 : 0 ≤ max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n) := le_max_of_le_left hD0
  by_cases hn : N ≤ n
  · -- the complete `r`-graph is a valid host
    let G : Faithful2024.HGraph (Fin n) := ⟨univ, univ.powersetCard r⟩
    have hGu : G.IsUniform r := fun e he => ⟨(mem_powersetCard.1 he).2, subset_univ _⟩
    have hNle : ((r : ℝ) - 1) / ε ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈((r : ℝ) - 1) / ε⌉₊ ≤ n by omega))
    have hεn : (r : ℝ) - 1 ≤ ε * n := by
      rw [div_le_iff₀ hε] at hNle
      linarith
    have hr1 : ((r - 1 : ℕ) : ℝ) = r - 1 := by
      rw [Nat.cast_sub hr]
      simp
    have hrn : r - 1 ≤ n := by
      have : ((r - 1 : ℕ) : ℝ) ≤ n := by
        rw [hr1]
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      exact_mod_cast this
    have hδ : G.MinDegGE r ((1 - ε) * n) := by
      intro S _ hS
      have h1 := le_deg_complete (n := n) hS
      have h2 : ((n - (r - 1) : ℕ) : ℝ) = n - ((r - 1 : ℕ) : ℝ) := Nat.cast_sub hrn
      have h3 : ((n - (r - 1) : ℕ) : ℝ) ≤ (deg G.edges S : ℝ) := by exact_mod_cast h1
      rw [h2, hr1] at h3
      nlinarith
    have hXG : X.IsSpanningSubgraph G :=
      ⟨hXv, fun e he => mem_powersetCard.2 ⟨subset_univ _, (hXu e he).1⟩⟩
    have hXn : (X.maxDeg r : ℝ) ≤ n / C :=
      hXD.trans (hDn.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hCpos hCN))
    obtain ⟨A, 𝓗, QA, hom, href, -, hdeg⟩ := h n G X rfl hGu hδ hXG hXn
    refine ⟨A, 𝓗, QA, hom, fun e he => (href e he).trans (le_max_left _ _), ?_⟩
    calc (A.maxDeg r : ℝ) ≤ C * max (X.maxDeg r : ℝ) (Faithful2024.budget n r) := hdeg
      _ ≤ ((max C N : ℕ) : ℝ) * max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n) :=
          mul_le_mul hCN (max_le_max hXD le_rfl) (le_max_of_le_left (Nat.cast_nonneg _))
            (by positivity)
  · -- small `n`: `X` has no edges and the empty absorber works
    push Not at hn
    have hD1 : D < 1 := by
      refine hDn.trans_lt ?_
      have hNpos : (0 : ℝ) < ((max C N : ℕ) : ℝ) := hCpos.trans_le hCN
      rw [div_lt_one hNpos]
      have h1 : (n : ℝ) < N := by exact_mod_cast hn
      have h2 : (N : ℝ) ≤ ((max C N : ℕ) : ℝ) := by exact_mod_cast le_max_right C N
      linarith
    have hX0 : X.edges = ∅ := by
      by_contra hne
      obtain ⟨e, he⟩ := nonempty_iff_ne_empty.2 hne
      have : (1 : ℝ) ≤ X.maxDeg r := by exact_mod_cast one_le_maxDeg hr hXv hXu he
      linarith
    refine ⟨⟨univ, ∅⟩, ∅, fun _ => ∅, ⟨?_, ?_, hXv, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro e he
      rw [hX0] at he
      simp at he
    · intro e he
      simp at he
    · simp [hX0]
    · intro Q hQ
      simp at hQ
    · intro Q hQ
      simp at hQ
    · intro L _ _
      exact subset_refl _
    · intro L hL _
      rw [hX0, subset_empty] at hL
      subst hL
      exact ⟨by simp, by simp, by simp⟩
    · intro e _
      simp
    · have : (Faithful2024.HGraph.maxDeg r (⟨univ, ∅⟩ : Faithful2024.HGraph (Fin n))) = 0 := by
        simp [Faithful2024.HGraph.maxDeg, deg]
      rw [this, Nat.cast_zero]
      positivity

end RefinedAbsorption.Final
