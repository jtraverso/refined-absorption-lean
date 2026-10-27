module
public import RequestProject.OddGrid.StageDiv

/-!
# Weighted labels of uniformity `r`: face classes and divisibility

This file starts the `r`-uniform analogue of the grid refiner of `RequestProject/OddGrid/`
(which is specific to `r = 2`).  A label `ℓ` with `pw ℓ = (e, w)`, `w : ZMod K`, stands for
`w.val` parallel copies of the set `e` (`wsg`, `liftS`).

* `LDivR q r pw Q`: the lift of the label set `Q` is `K_q^r`-divisible.
* `fcl pw Q S`: the *face class* of `Q` at the vertex set `S`, i.e. `Σ_{ℓ ∈ Q, S ⊆ e_ℓ} w_ℓ` in
  `ZMod K`.
* `ldivR_iff`: when `K` is a multiple of every `binom(q - i, r - i)` (`i < r`, `ModsOK`), the lift
  is divisible iff every face class at a set `S` with `|S| < r` is divisible by
  `binom(q - |S|, r - |S|)`.
* Divisibility is preserved by disjoint unions, passes to residues of partitions, and holds for
  label sets on one set `e` with total weight `0` (`ldivR_of_one_set`).
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid

variable {K : ℕ}

/-- `K` is a multiple of all the moduli `binom(q - i, r - i)`, `i < r`. -/
def ModsOK (q r K : ℕ) : Prop := ∀ i < r, (q - i).choose (r - i) ∣ K

section Defs

variable {Λ V : Type} [DecidableEq Λ] [DecidableEq V]

/-- Divisibility of the lift of a set of weighted labels (uniformity `r`). -/
abbrev LDivR (q r : ℕ) (pw : Λ → Finset V × ZMod K) (Q : Finset Λ) : Prop :=
  MIsDivisible q r (cpEnds (wsg pw)) (liftS (wsg pw) Q)

/-- The face class of a set of labels at the vertex set `S`. -/
def fcl (pw : Λ → Finset V × ZMod K) (Q : Finset Λ) (S : Finset V) : ZMod K :=
  ∑ ℓ ∈ Q, if S ⊆ (pw ℓ).1 then (pw ℓ).2 else 0

lemma fcl_union (pw : Λ → Finset V × ZMod K) {P Q : Finset Λ} (h : Disjoint P Q) (S : Finset V) :
    fcl pw (P ∪ Q) S = fcl pw P S + fcl pw Q S := by
  unfold fcl; rw [sum_union h]

lemma fcl_empty (pw : Λ → Finset V × ZMod K) (S : Finset V) : fcl pw (∅ : Finset Λ) S = 0 := by
  simp [fcl]

lemma fcl_singleton (pw : Λ → Finset V × ZMod K) (ℓ : Λ) (S : Finset V) :
    fcl pw {ℓ} S = if S ⊆ (pw ℓ).1 then (pw ℓ).2 else 0 := by
  simp [fcl]

end Defs

/-! ### The divisibility criterion -/

section Criterion

variable {Λ V : Type} [DecidableEq Λ] [DecidableEq V] [NeZero K] {q r : ℕ}
  {pw : Λ → Finset V × ZMod K}

/-- The degree of a lift, cast to `ZMod K`, is the face class. -/
lemma cast_mdeg_liftS (Q : Finset Λ) (S : Finset V) :
    ((mdeg (cpEnds (wsg pw)) (liftS (wsg pw) Q) S : ℕ) : ZMod K) = fcl pw Q S := by
  rw [mdeg_liftS, fcl]
  push_cast
  refine sum_congr rfl fun ℓ _ => ?_
  rw [wdeg_wsg]
  split_ifs <;> simp [ZMod.natCast_val]

/-- `m ∣ a` iff `m ∣ (a : ZMod K).val`, for `m ∣ K`. -/
lemma dvd_iff_dvd_val {m : ℕ} (hm : m ∣ K) (a : ℕ) : m ∣ a ↔ m ∣ ((a : ZMod K)).val := by
  rw [ZMod.val_natCast]
  constructor
  · intro h; exact (Nat.dvd_mod_iff hm).2 h
  · intro h; exact (Nat.dvd_mod_iff hm).1 h

/-- **Divisibility criterion** for lifts of weighted labels, in terms of face classes. -/
theorem ldivR_iff (hK : ModsOK q r K) (Q : Finset Λ) :
    LDivR q r pw Q ↔ ∀ S : Finset V, S.card < r →
      (q - S.card).choose (r - S.card) ∣ (fcl pw Q S).val := by
  constructor
  · intro h S hS
    rw [← cast_mdeg_liftS, ← dvd_iff_dvd_val (hK _ hS)]
    exact h S hS
  · intro h S hS
    rw [dvd_iff_dvd_val (hK _ hS), cast_mdeg_liftS]
    exact h S hS

/-- A label set whose face classes vanish identically is divisible. -/
lemma ldivR_of_fcl_zero (hK : ModsOK q r K) {Q : Finset Λ} (h : ∀ S : Finset V, S.card < r →
    fcl pw Q S = 0) : LDivR q r pw Q :=
  (ldivR_iff hK Q).2 fun S hS => by rw [h S hS, ZMod.val_zero]; exact dvd_zero _

/-- Labels on one set `e` with total weight `0` are divisible. -/
lemma ldivR_of_one_set (hK : ModsOK q r K) {Q : Finset Λ} {e : Finset V}
    (h : ∀ ℓ ∈ Q, (pw ℓ).1 = e) (h0 : ∑ ℓ ∈ Q, (pw ℓ).2 = 0) : LDivR q r pw Q := by
  refine ldivR_of_fcl_zero hK fun S _ => ?_
  unfold fcl
  by_cases hS : S ⊆ e
  · rw [← h0]; exact sum_congr rfl fun ℓ hℓ => by rw [h ℓ hℓ, if_pos hS]
  · exact sum_eq_zero fun ℓ hℓ => by rw [h ℓ hℓ, if_neg hS]

end Criterion

/-! ### Partitions -/

section Partition

variable {Λ V : Type} [DecidableEq Λ] [DecidableEq V] {q r : ℕ} {pw : Λ → Finset V × ZMod K}

lemma ldivR_union {P Q : Finset Λ} (h : Disjoint P Q) (hP : LDivR q r pw P)
    (hQ : LDivR q r pw Q) : LDivR q r pw (P ∪ Q) := by
  unfold LDivR; rw [liftS_union]
  exact MIsDivisible.union (disjoint_liftS h) hP hQ

lemma ldivR_empty : LDivR q r pw (∅ : Finset Λ) := by
  unfold LDivR; rw [liftS_empty]; exact mIsDivisible_empty q r _

lemma ldivR_sup {𝒰 : Finset (Finset Λ)} (h : (𝒰 : Set (Finset Λ)).PairwiseDisjoint id)
    (hd : ∀ P ∈ 𝒰, LDivR q r pw P) : LDivR q r pw (𝒰.sup id) := by
  unfold LDivR
  rw [← liftS_sup]
  intro S hS
  rw [mdeg_sup_eq_sum _ _ (pd_image_liftS h)]
  exact Finset.dvd_sum fun W hW => by
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    exact hd P hP S hS

lemma ldivR_of_partition {A Res : Finset Λ} {𝒰 : Finset (Finset Λ)} (hA : LDivR q r pw A)
    (h : (𝒰 : Set (Finset Λ)).PairwiseDisjoint id) (hd : ∀ P ∈ 𝒰, LDivR q r pw P)
    (hdj : Disjoint (𝒰.sup id) Res) (heq : 𝒰.sup id ∪ Res = A) : LDivR q r pw Res := by
  unfold LDivR at *
  refine divisible_of_partition hA (pd_image_liftS (pw := pw) h) ?_ ?_ ?_
  · intro W hW
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    exact hd P hP
  · rw [liftS_sup]; exact disjoint_liftS hdj
  · rw [liftS_sup, ← liftS_union, heq]

lemma ldivR_of_wt_zero {Q : Finset Λ} (h : ∀ ℓ ∈ Q, (pw ℓ).2 = 0) : LDivR q r pw Q := by
  unfold LDivR; rw [liftS_eq_empty h]; exact mIsDivisible_empty q r _

end Partition

end RefinedAbsorption.HyperPlan
