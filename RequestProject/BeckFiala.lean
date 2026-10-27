module
public import Mathlib

/-!
# Iterated rounding (Beck–Fiala)

Let `(S i)_{i ∈ I}` be a finite family of finite sets such that every point lies in at most
`t` of them, and let `x` be a fractional point of `[0,1]^α`.  Then `x` can be rounded to a
`0/1` vector `y` such that for every `i ∈ I` the sums of `x` and of `y` over `S i` differ by at
most `t`.

This is the classical linear-algebraic iterated rounding argument of Beck and Fiala: as long as
some coordinates are fractional, the sets containing more than `t` fractional coordinates are
fewer than the fractional coordinates, so we can move `x` in a direction which keeps the sums
over those sets fixed until one more coordinate becomes integral.  A set with at most `t`
fractional coordinates can change by at most `t` afterwards.

This is used to prove the boost lemma (Lemma 2.2) from a fractional version of it.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

/-- A nonzero vector supported on `F` whose sums over the sets `S i`, `i ∈ A`, all vanish,
provided `|A| < |F|`. -/
theorem exists_kernel_vec {α ι : Type*} [DecidableEq α] (F : Finset α) (A : Finset ι)
    (S : ι → Finset α) (h : A.card < F.card) :
    ∃ z : α → ℝ, (∀ a ∉ F, z a = 0) ∧ (∃ a ∈ F, z a ≠ 0) ∧ ∀ i ∈ A, ∑ a ∈ S i, z a = 0 := by
  classical
  let v : F → (A → ℝ) := fun a i => if (a : α) ∈ S i then 1 else 0
  have hv : ¬ LinearIndependent ℝ v := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at this
    simp only [Fintype.card_coe] at this
    omega
  obtain ⟨g, hg, a₀, ha₀⟩ := Fintype.not_linearIndependent_iff.1 hv
  let z : α → ℝ := fun a => if h : a ∈ F then g ⟨a, h⟩ else 0
  refine ⟨z, fun a ha => dif_neg ha,
    ⟨a₀.1, a₀.2, by simpa [z] using ha₀⟩, fun i hi => ?_⟩
  have h1 := congrFun hg ⟨i, hi⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at h1
  have h2 : ∀ a : F, g a * (if (a : α) ∈ S i then 1 else 0) =
      (fun b : α => z b * (if b ∈ S i then 1 else 0)) a := by
    intro a; simp [z]
  rw [Fintype.sum_congr _ _ h2, Finset.sum_coe_sort F
    (fun b : α => z b * (if b ∈ S i then 1 else 0))] at h1
  rw [← h1]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  symm
  apply sum_subset
  · intro a ha; simp at ha; exact ha.2
  · intro a ha ha'
    have : a ∉ F := by simp_all
    exact dif_neg this

/-- Moving from `x ∈ [0,1]^α` in a direction `z ≠ 0` supported on `F` until a coordinate of `F`
hits `0` or `1`. -/
theorem exists_step {α : Type*} (F : Finset α) (x z : α → ℝ) (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hz0 : ∀ a ∉ F, z a = 0) (hz : ∃ a ∈ F, z a ≠ 0) :
    ∃ s : ℝ, (∀ a, 0 ≤ x a + s * z a ∧ x a + s * z a ≤ 1) ∧
      ∃ a ∈ F, x a + s * z a = 0 ∨ x a + s * z a = 1 := by
  classical
  let P := F.filter (fun a => z a ≠ 0)
  let ρ : α → ℝ := fun a => if 0 < z a then (1 - x a) / z a else x a / (- z a)
  have hP : P.Nonempty := by
    obtain ⟨a, ha, hza⟩ := hz; exact ⟨a, mem_filter.2 ⟨ha, hza⟩⟩
  obtain ⟨a₀, ha₀, hmin⟩ := P.exists_min_image ρ hP
  have hρnn : ∀ a, 0 ≤ ρ a := by
    intro a
    simp only [ρ]
    split_ifs with h
    · exact div_nonneg (by linarith [(hx a).2]) h.le
    · rcases eq_or_lt_of_le (not_lt.1 h) with h' | h'
      · simp [h']
      · exact div_nonneg (hx a).1 (by linarith)
  refine ⟨ρ a₀, fun a => ?_, a₀, (mem_filter.1 ha₀).1, ?_⟩
  · by_cases hza : z a = 0
    · simp [hza, hx a]
    · have haP : a ∈ P := mem_filter.2 ⟨by by_contra h; exact hza (hz0 a h), hza⟩
      have hle := hmin a haP
      have hs := hρnn a₀
      obtain ⟨h0, h1⟩ := hx a
      rcases lt_or_gt_of_ne hza with hneg | hpos
      · have hr : ρ a = x a / (- z a) := by simp [ρ, not_lt.2 hneg.le]
        rw [hr, le_div_iff₀ (by linarith)] at hle
        constructor <;> nlinarith
      · have hr : ρ a = (1 - x a) / z a := by simp [ρ, hpos]
        rw [hr, le_div_iff₀ hpos] at hle
        constructor <;> nlinarith
  · have hza := (mem_filter.1 ha₀).2
    rcases lt_or_gt_of_ne hza with hneg | hpos
    · left
      have hr : ρ a₀ = x a₀ / (- z a₀) := by simp [ρ, not_lt.2 hneg.le]
      rw [hr]; field_simp; ring
    · right
      have hr : ρ a₀ = (1 - x a₀) / z a₀ := by simp [ρ, hpos]
      rw [hr]; field_simp; ring

/-- The fractional coordinates of `x` inside `U`. -/
noncomputable def fracCoords {α : Type*} (U : Finset α) (x : α → ℝ) : Finset α :=
  U.filter (fun a => 0 < x a ∧ x a < 1)

/-- If every point is in at most `t` of the sets `S i` (`i ∈ I`), fewer than `|F|` of these
sets contain more than `t` points of a nonempty set `F`. -/
theorem card_heavy_lt {α ι : Type*} [DecidableEq α] (I : Finset ι) (S : ι → Finset α) (t : ℕ)
    (ht : ∀ a, (I.filter (fun i => a ∈ S i)).card ≤ t) (F : Finset α) (hF : F.Nonempty) :
    (I.filter (fun i => t < ((S i).filter (· ∈ F)).card)).card < F.card := by
  classical
  set A := I.filter (fun i => t < ((S i).filter (· ∈ F)).card)
  have h1 : (t + 1) * A.card ≤ ∑ i ∈ A, ((S i).filter (· ∈ F)).card := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun i hi => (mem_filter.1 hi).2
  have h2 : ∑ i ∈ A, ((S i).filter (· ∈ F)).card = ∑ a ∈ F, (A.filter (fun i => a ∈ S i)).card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_filter, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext a; simp [and_comm]
  have h3 : ∑ a ∈ F, (A.filter (fun i => a ∈ S i)).card ≤ t * F.card := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun a _ => le_trans (card_le_card ?_) (ht a)
    exact filter_subset_filter _ (filter_subset _ _)
  have hFpos := hF.card_pos
  by_contra hcon
  push_neg at hcon
  nlinarith

/-- **Beck–Fiala rounding.**  If every point lies in at most `t` of the sets `S i` (`i ∈ I`)
and `x ∈ [0,1]^α`, then there is `y` which is `0/1`-valued on `⋃ S i` such that
`|∑_{a ∈ S i} (y a - x a)| ≤ t` for all `i ∈ I`. -/
theorem beck_fiala {α ι : Type*} [DecidableEq α] (I : Finset ι) (S : ι → Finset α) (t : ℕ)
    (ht : ∀ a, (I.filter (fun i => a ∈ S i)).card ≤ t) (x : α → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1) :
    ∃ y : α → ℝ, (∀ a ∈ I.biUnion S, y a = 0 ∨ y a = 1) ∧
      ∀ i ∈ I, |∑ a ∈ S i, (y a - x a)| ≤ t := by
  classical
  set U := I.biUnion S
  suffices key : ∀ k : ℕ, ∀ x : α → ℝ, (∀ a, 0 ≤ x a ∧ x a ≤ 1) → (fracCoords U x).card ≤ k →
      ∃ y : α → ℝ, (∀ a ∈ U, y a = 0 ∨ y a = 1) ∧ (∀ a ∈ U, a ∉ fracCoords U x → y a = x a) ∧
        ∀ i ∈ I, |∑ a ∈ S i, (y a - x a)| ≤ t by
    obtain ⟨y, hy1, -, hy3⟩ := key _ x hx le_rfl
    exact ⟨y, hy1, hy3⟩
  intro k
  induction k with
  | zero =>
    intro x hx hk
    have hF : fracCoords U x = ∅ := card_eq_zero.1 (by omega)
    refine ⟨x, fun a ha => ?_, fun _ _ _ => rfl, fun i _ => by simp⟩
    have : a ∉ fracCoords U x := by simp [hF]
    simp only [fracCoords, mem_filter, not_and, not_lt] at this
    have h := this ha
    rcases eq_or_lt_of_le (hx a).1 with h0 | h0
    · left; exact h0.symm
    · right; exact le_antisymm (hx a).2 (h h0)
  | succ k ih =>
    intro x hx hk
    set F := fracCoords U x with hFdef
    rcases F.eq_empty_or_nonempty with hF | hF
    · exact ih x hx (by rw [← hFdef, hF]; simp)
    set A := I.filter (fun i => t < ((S i).filter (· ∈ F)).card) with hAdef
    obtain ⟨z, hz0, hz, hzA⟩ := exists_kernel_vec F A S (card_heavy_lt I S t ht F hF)
    obtain ⟨s, hs01, a₀, ha₀F, ha₀⟩ := exists_step F x z hx hz0 hz
    set x' : α → ℝ := fun a => x a + s * z a with hx'
    have hFU : F ⊆ U := filter_subset _ _
    have hsub : fracCoords U x' ⊆ F.erase a₀ := by
      intro a ha
      simp only [fracCoords, mem_filter] at ha
      rw [mem_erase]
      constructor
      · rintro rfl
        rcases ha₀ with h | h <;> simp only [hx'] at ha <;> linarith [ha.2.1, ha.2.2]
      · by_contra haF
        have := hz0 a haF
        simp only [hx', this, mul_zero, add_zero] at ha
        exact haF (mem_filter.2 ⟨ha.1, ha.2⟩)
    have hcard : (fracCoords U x').card ≤ k := by
      have := card_le_card hsub
      rw [card_erase_of_mem ha₀F] at this
      omega
    obtain ⟨y, hy1, hy2, hy3⟩ := ih x' hs01 hcard
    have hyx : ∀ a ∈ U, a ∉ F → y a = x a := by
      intro a haU haF
      rw [hy2 a haU (fun h => haF (hsub h |> mem_of_mem_erase))]
      simp [hx', hz0 a haF]
    refine ⟨y, hy1, hyx, fun i hi => ?_⟩
    by_cases hiA : i ∈ A
    · have h1 : ∑ a ∈ S i, (y a - x a) = ∑ a ∈ S i, (y a - x' a) := by
        have : ∑ a ∈ S i, (y a - x' a) = ∑ a ∈ S i, (y a - x a) - s * ∑ a ∈ S i, z a := by
          rw [mul_sum, ← sum_sub_distrib]
          refine sum_congr rfl fun a _ => ?_
          simp only [hx']; ring
        rw [this, hzA i hiA, mul_zero, sub_zero]
      rw [h1]
      exact hy3 i hi
    · have hsmall : ((S i).filter (· ∈ F)).card ≤ t := by
        by_contra h
        exact hiA (mem_filter.2 ⟨hi, by omega⟩)
      have hSU : S i ⊆ U := subset_biUnion_of_mem S hi
      have h1 : ∑ a ∈ S i, (y a - x a) = ∑ a ∈ (S i).filter (· ∈ F), (y a - x a) := by
        rw [sum_filter]
        refine sum_congr rfl fun a ha => ?_
        split_ifs with haF
        · rfl
        · rw [hyx a (hSU ha) haF, sub_self]
      rw [h1]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans ?_ (Nat.cast_le.2 hsmall)
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      refine sum_le_sum fun a ha => ?_
      have haU : a ∈ U := hSU (mem_filter.1 ha).1
      rw [abs_le]
      rcases hy1 a haU with h | h <;> rw [h] <;> constructor <;> linarith [(hx a).1, (hx a).2]

end RefinedAbsorption
