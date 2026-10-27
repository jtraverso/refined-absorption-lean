module
public import Mathlib.Analysis.Complex.ExponentialBounds
public import RefinedAbsorption.LocalRefiner.Loads
public import RefinedAbsorption.Placement.Assembly

/-!
# Strong multi-refiners with the exact budget for `r = 2` and `q` even

Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

* `nativeStrongMultiRefiners_two_even`: for every even `q ≥ 4`, `NativeStrongMultiRefiners q 2`
  holds; in fact the budget is `⌊D⌋ + 1 = O(max(D, 1))`, which is at most
  `C · max(D, √n log n)`.
* `refinerAbsorbersFor_two_even`: hence `RefinerAbsorbersFor q 2` (refined refiners with attached
  absorbers and the degree bound of Theorem 1.10) for every even `q ≥ 4`.

The construction (`LocalRefiner.Construction`) gives every vertex `u` its own reserve
`{u, u+1, u+2}`, on which a chain refiner absorbs the *tokens* left at `u` by the edges of `L`,
and a global chain (the connector) absorbs the edge-count condition at `S = ∅`.  Tokens with
degree `≡ 1` at `u` and `≡ 0` elsewhere modulo `q - 1` exist on three vertices only because
`q - 1` is odd; for odd `q` every multigraph has an even degree sum, so this local construction
does not apply.
-/

@[expose] public section

namespace RefinedAbsorption.LocalRefiner

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement

lemma one_le_sqrt_log {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) ≤ (n : ℝ) ^ (1 - 1 / ((2 : ℕ) : ℝ)) * Real.log n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 - 1 / ((2 : ℕ) : ℝ)) :=
    Real.one_le_rpow hn1 (by norm_num)
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : (1 : ℝ) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  nlinarith

/-- **`NativeStrongMultiRefiners q 2` for even `q`.** -/
theorem nativeStrongMultiRefiners_two_even {q : ℕ} (hq : 4 ≤ q) (heven : Even q) :
    NativeStrongMultiRefiners q 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 2 * k + 4 := by
    obtain ⟨m, hm⟩ := heven; exact ⟨m - 2, by omega⟩
  have hC2 : 2 ≤ Cloc k := by
    unfold Cloc; have : 1 ≤ (2 * k + 4) ^ 4 := Nat.one_le_pow _ _ (by omega); omega
  refine ⟨Cloc k, by omega, 3, ?_⟩
  intro n hn X D hX hXD _
  haveI : NeZero n := ⟨by omega⟩
  set Dn := ⌊D⌋₊
  have hD : ∀ y : Fin n, (X.filter (y ∈ ·)).card ≤ Dn := by
    intro y
    have h := hXD {y} (by simp)
    have heq : deg X {y} = (X.filter (y ∈ ·)).card := by
      unfold deg; congr 1; apply filter_congr; intro e _; exact singleton_subset_iff
    rw [heq] at h
    exact Nat.le_floor h
  refine ⟨Lb n × ℕ × ℕ, inferInstance, endsX k X, XlX X, XlX X, RX k X, WX k X, Dn + 1,
    ?_, ?_, ?_⟩
  · ext e
    simp only [XlX, mem_image]
    constructor
    · rintro ⟨_, ⟨e', he', rfl⟩, rfl⟩; simpa [endsX, cpEnds, segAt, segs] using he'
    · intro he; exact ⟨_, ⟨e, he, rfl⟩, by simp [endsX, cpEnds, segAt, segs]⟩
  · set L := (n : ℝ) ^ (1 - 1 / ((2 : ℕ) : ℝ)) * Real.log n
    have hL : 1 ≤ L := one_le_sqrt_log hn
    have hfl : (Dn : ℝ) ≤ max D 0 := by
      rcases le_or_gt 0 D with h0 | h0
      · exact (Nat.floor_le h0).trans (le_max_left _ _)
      · have : Dn = 0 := Nat.floor_eq_zero.2 (by linarith)
        rw [this]; simp
    have hC : (2 : ℝ) ≤ Cloc k := by exact_mod_cast hC2
    have hmax : max D 0 ≤ max D L := max_le_max le_rfl (by linarith)
    have hm1 : 1 ≤ max D L := le_max_of_le_right hL
    push_cast
    calc (Dn : ℝ) + 1 ≤ max D L + max D L := by linarith
      _ = 2 * max D L := by ring
      _ ≤ Cloc k * max D L := by nlinarith
  · refine ⟨isMultiRefiner_local hX (by omega), subset_refl _, ?_, fun W hW => oneX_le hW,
      ?_, ?_, ?_⟩
    · intro a ha b hb h
      simp only [XlX, coe_image, Set.mem_image, mem_coe] at ha hb
      obtain ⟨e, -, rfl⟩ := ha
      obtain ⟨e', -, rfl⟩ := hb
      simp only [endsX, cpEnds, segAt, segs, List.getD_cons_zero] at h
      rw [h]
    · intro S hS
      obtain ⟨x, rfl⟩ := card_eq_one.1 (by simpa using hS)
      rw [degX_eq]; exact (hD x).trans (Nat.le_succ _)
    · intro S hS
      obtain ⟨x, rfl⟩ := card_eq_one.1 (by simpa using hS)
      exact degR_le hD x
    · intro S hS
      obtain ⟨x, rfl⟩ := card_eq_one.1 (by simpa using hS)
      exact pieceDeg_le hD x

/-- **`RefinerAbsorbersFor q 2` for even `q`**: refined refiners with attached absorbers and
`Δ(R ∪ ⋃ A_W) ≤ C · max(D, √n log n)`, i.e. the conclusion of Theorem 1.10 for `r = 2` in the
form used by the project, for every even `q ≥ 4`. -/
theorem refinerAbsorbersFor_two_even {q : ℕ} (hq : 4 ≤ q) (heven : Even q) :
    RefinerAbsorbersFor q 2 :=
  refinerAbsorbersFor_of_native le_rfl (by omega) (nativeStrongMultiRefiners_two_even hq heven)

end RefinedAbsorption.LocalRefiner
