module
public import RequestProject.HyperPlan.Strong
public import RequestProject.OddGrid.Native

/-!
# `NativeStrongMultiRefiners q r` from `r`-uniform plans

This file reduces the native construction `NativeStrongMultiRefiners q r` (strong multi-refiners
with degree budget `C · max(D, n^{1-1/r} log n)`) to a purely combinatorial statement about
*plans* (`RPlans q r`): sequences of stages in which every current `r`-set is rerouted along a
signed list of `r`-sets (for instance a box, `HyperPlan.Box`), with

* class-preserving routes (`PlanOKR`: the defect of every route, multiplied by every weight that
  can occur, is divisible by the moduli; the weights that can occur are restricted by loneliness),
* a bounded number of final sets,
* route loads `Σ_t passR sp X t S ≤ C · max(D, n^{1-1/r} log n)` at every `(r - 1)`-set `S`.

`nativeStrongMultiRefiners_of_rPlans`: `RPlans q r → NativeStrongMultiRefiners q r` for
`1 ≤ r < q`.  All the bookkeeping of refiners (switches, accumulator chains, divisibility of
pieces and residues, multiplicities, piece degrees, lifting to multigraphs) is done once and for
all by `plan_strongR`; what remains for `r ≥ 3` is the construction of the plans themselves.
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid RefinedAbsorption.Placement

/-- The modulus of the weights: the product of the moduli `binom(q - i, r - i)`, `i < r`. -/
def Kmod (q r : ℕ) : ℕ := ∏ i ∈ range r, (q - i).choose (r - i)

lemma modsOK_Kmod (q r : ℕ) : ModsOK q r (Kmod q r) := fun _ hi =>
  dvd_prod_of_mem (fun i => (q - i).choose (r - i)) (mem_range.2 hi)

lemma one_lt_Kmod {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) : 1 < Kmod q r := by
  unfold Kmod
  have hpos : ∀ i ∈ range r, 1 ≤ (q - i).choose (r - i) := fun i hi =>
    Nat.one_le_iff_ne_zero.2 (Nat.choose_pos (by have := mem_range.1 hi; omega)).ne'
  have h0 : 1 < (q - 0).choose (r - 0) := by
    simp only [Nat.sub_zero]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Nat.choose_succ_succ]
    have h1 := Nat.choose_pos (show r' ≤ q' by omega)
    have h2 := Nat.choose_pos (show r'.succ ≤ q' by omega)
    omega
  rw [← mul_prod_erase (range r) _ (mem_range.2 (by omega : 0 < r))]
  have : 1 ≤ ∏ i ∈ (range r).erase 0, (q - i).choose (r - i) :=
    one_le_prod' fun i hi => hpos i (mem_of_mem_erase hi)
  nlinarith

/-- **Good `r`-uniform plans** (a purely combinatorial statement): for large `n`, every `r`-graph
`X` on `Fin n` with `Δ_{r-1}(X) ≤ D ≤ n / C` has a valid plan (routes of length `≤ L`, at most
`M` final sets) whose route loads at every `(r - 1)`-set are at most
`C · max(D, n^{1-1/r} log n)`. -/
def RPlans (q r : ℕ) : Prop :=
  ∃ C L M : ℕ, 1 ≤ C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Finset (Fin n)), ∀ D : ℝ,
    IsRGraph r X → MaxDegLE r X D → D ≤ n / C →
    ∃ _ : NeZero (Kmod q r), ∃ sp : List (SpecR n (Kmod q r)), PlanOKR q r L sp X ∧
      1 ≤ sp.length ∧ (prunR sp X sp.length).card ≤ M ∧
      ∀ S : Finset (Fin n), S.card = r - 1 →
        ((∑ t ∈ range sp.length, passR sp X t S : ℕ) : ℝ) ≤
          C * max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n)

lemma one_le_rpow_log {r n : ℕ} (hr : 1 ≤ r) (hn : 3 ≤ n) :
    1 ≤ (n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hexp : 0 ≤ 1 - 1 / (r : ℝ) := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  have h1 : 1 ≤ (n : ℝ) ^ (1 - 1 / (r : ℝ)) := Real.one_le_rpow hn1 hexp
  have h2 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  nlinarith

/-- **`NativeStrongMultiRefiners q r` from good `r`-uniform plans.** -/
theorem nativeStrongMultiRefiners_of_rPlans {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q)
    (h : RPlans q r) : NativeStrongMultiRefiners q r := by
  obtain ⟨C, L, M, hC, n₀, hN⟩ := h
  have hK1 : 1 < Kmod q r := one_lt_Kmod hr hrq
  haveI : NeZero (Kmod q r) := ⟨by omega⟩
  refine ⟨CplR (Kmod q r) M L + C, by omega, max n₀ 3, ?_⟩
  intro n hn X D hX hXD hDn
  have hC0 : (0 : ℝ) < C := by exact_mod_cast hC
  have hDn' : D ≤ n / C := by
    refine hDn.trans ?_
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hC0
    exact_mod_cast (show C ≤ CplR (Kmod q r) M L + C by omega)
  obtain ⟨_, sp, hok, hT, hM, hP⟩ := hN n (le_of_max_le_left hn) X D hX hXD hDn'
  set Lg := (n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n with hLg
  have hL1 : 1 ≤ Lg := one_le_rpow_log hr (le_of_max_le_right hn)
  set x := (C : ℝ) * max D Lg with hx
  have hmax : 1 ≤ max D Lg := hL1.trans (le_max_right _ _)
  have hx1 : 1 ≤ x := by
    have : (1 : ℝ) ≤ C := by exact_mod_cast hC
    nlinarith
  set B := ⌊x⌋₊ with hBdef
  have hB1 : 1 ≤ B := Nat.le_floor (by exact_mod_cast hx1)
  have hDx : D ≤ x := by
    have : (1 : ℝ) ≤ C := by exact_mod_cast hC
    have h0 : 0 ≤ max D Lg := le_trans zero_le_one hmax
    nlinarith [le_max_left D Lg]
  have hX' : ∀ S : Finset (Fin n), S.card = r - 1 → (X.filter (S ⊆ ·)).card ≤ B := by
    intro S hS
    apply Nat.le_floor
    have := hXD S (by omega)
    exact this.trans hDx
  have hP' : ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ t ∈ range sp.length, passR sp X t S ≤ B := fun S hS => Nat.le_floor (hP S hS)
  obtain ⟨himg, hS⟩ := plan_strongR (modsOK_Kmod q r) hK1 hok hT hM hB1 hX' hP'
  refine ⟨_, inferInstance, _, _, _, _, _, B, himg, ?_, IsStrongMultiRefiner.mono' hS (by omega)⟩
  have hBx : (B : ℝ) ≤ x := Nat.floor_le (by linarith)
  refine hBx.trans ?_
  have : (C : ℝ) ≤ ((CplR (Kmod q r) M L + C : ℕ) : ℝ) := by exact_mod_cast (show C ≤ CplR (Kmod q r) M L + C by omega)
  have h0 : 0 ≤ max D Lg := le_trans zero_le_one hmax
  exact mul_le_mul_of_nonneg_right this h0

end RefinedAbsorption.HyperPlan
