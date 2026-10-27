module
public import RequestProject.HyperPlan.Load
public import RequestProject.HyperPlan.Box

/-!
# Valid moves for `r`-sets

The basic signed routes from which `r`-uniform plans are built, with their validity (`RouteOKR`).

* `boxRoute e F ρ`: replace `e` by the other transversals of the box with fixed set `F` and
  replacement map `ρ` (`HyperPlan.Box`), with signs `-(-1)^{|e \ J|}`, so that `e` minus the route
  is the box.  Its defect at `S` is minus the class of the box at `S` (`defect_boxRoute`).
* `routeOKR_fullBox`: a full box (`F = ∅`) is valid for every weight.
* `routeOKR_loneBox`: a box whose moved part `e \ F` lies in no other current set is valid for every
  value allowed by loneliness (`allowedR`).  For `F = e \ {v}` this is the move of a set out of a
  vertex `v` that lies in no other current set, the `r`-uniform version of the moves of `OddGrid`.
* `routeOKR_stay`: the trivial route `[(e, 1)]`.
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid

variable {n K : ℕ}

/-- The class of the box at `S`. -/
def boxCl (e F : Finset (Fin n)) (ρ : Fin n → Fin n) (S : Finset (Fin n)) : ZMod K :=
  ∑ J ∈ bJs e F, (if S ⊆ bt e ρ J then (-1 : ZMod K) ^ (e \ J).card else 0)

/-- The route of `e` along the box with fixed set `F` and replacement map `ρ`. -/
noncomputable def boxRoute (e F : Finset (Fin n)) (ρ : Fin n → Fin n) :
    List (Finset (Fin n) × ZMod K) :=
  ((bJs e F).erase e).toList.map fun J => (bt e ρ J, -(-1 : ZMod K) ^ (e \ J).card)

lemma lfcl_boxRoute {e F : Finset (Fin n)} {ρ : Fin n → Fin n} (h : BoxOK e F ρ)
    (S : Finset (Fin n)) :
    lfcl (boxRoute (K := K) e F ρ) S = (if S ⊆ e then 1 else 0) - boxCl e F ρ S := by
  unfold lfcl boxRoute boxCl
  rw [List.map_map, sum_map_toList, ← add_sum_erase _ _ (self_mem_bJs h)]
  simp only [Function.comp, bt_self, sdiff_self]
  have h1 : ((if S ⊆ e then (1 : ZMod K) else 0) -
      if S ⊆ e then (-1) ^ (⊥ : Finset (Fin n)).card else 0) = 0 := by
    split_ifs <;> simp
  rw [sub_add_eq_sub_sub, h1, zero_sub, ← sum_neg_distrib]
  apply sum_congr rfl
  intro J _
  split_ifs <;> simp

lemma defect_boxRoute {e F : Finset (Fin n)} {ρ : Fin n → Fin n} (h : BoxOK e F ρ)
    (S : Finset (Fin n)) :
    defect (boxRoute (K := K) e F ρ) e S = -boxCl e F ρ S := by
  rw [defect, lfcl_boxRoute h]; ring

lemma mem_boxRoute {e F : Finset (Fin n)} {ρ : Fin n → Fin n} {p : Finset (Fin n) × ZMod K}
    (hp : p ∈ boxRoute (K := K) e F ρ) : ∃ J ∈ bJs e F, J ≠ e ∧ p.1 = bt e ρ J := by
  unfold boxRoute at hp
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hp
  rw [mem_toList, mem_erase] at hJ
  exact ⟨J, hJ.2, hJ.1, rfl⟩

lemma card_boxRoute_sets {e F : Finset (Fin n)} {ρ : Fin n → Fin n} (h : BoxOK e F ρ)
    {p : Finset (Fin n) × ZMod K} (hp : p ∈ boxRoute (K := K) e F ρ) : p.1.card = e.card := by
  obtain ⟨J, hJ, -, hp⟩ := mem_boxRoute hp
  rw [hp, card_bt h hJ]

lemma boxRoute_sets_subset {e F : Finset (Fin n)} {ρ : Fin n → Fin n} (h : BoxOK e F ρ)
    {p : Finset (Fin n) × ZMod K} (hp : p ∈ boxRoute (K := K) e F ρ) :
    p.1 ⊆ e ∪ (e \ F).image ρ := by
  obtain ⟨J, hJ, -, hp⟩ := mem_boxRoute hp
  rw [hp]; exact bt_subset h hJ

/-- The vertices visited by a box route. -/
lemma visitR_boxRoute {e F : Finset (Fin n)} {ρ : Fin n → Fin n} (h : BoxOK e F ρ) :
    visitR e (boxRoute (K := K) e F ρ) ⊆ e ∪ (e \ F).image ρ := by
  unfold visitR
  refine union_subset subset_union_left ?_
  intro x hx
  obtain ⟨f, hf, hxf⟩ := mem_sup.1 hx
  revert x
  suffices f ⊆ e ∪ (e \ F).image ρ from fun x _ hxf => this hxf
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hf)
  exact boxRoute_sets_subset h hp

lemma length_boxRoute (e F : Finset (Fin n)) (ρ : Fin n → Fin n) :
    (boxRoute (K := K) e F ρ).length ≤ 2 ^ e.card := by
  unfold boxRoute
  rw [List.length_map, length_toList]
  refine (card_erase_le).trans ((card_filter_le _ _).trans ?_)
  rw [card_powerset]

/-- The trivial route. -/
def stayRoute (e : Finset (Fin n)) : List (Finset (Fin n) × ZMod K) := [(e, 1)]

variable [NeZero K] {q r : ℕ}

lemma dvd_val_mul {m : ℕ} (hm : m ∣ K) {a s : ZMod K} (hs : m ∣ s.val) : m ∣ (a * s).val := by
  have h1 : ((s.val : ℕ) : ZMod K) = s := ZMod.natCast_zmod_val s
  have : (a * s).val = (a.val * s.val) % K := by
    rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [this]
  exact (Nat.dvd_mod_iff hm).2 (Dvd.dvd.mul_left hs _)


omit [NeZero K] in
lemma routeOKR_stay {e : Finset (Fin n)} (he : e.card = r) (A : Finset (ZMod K)) :
    RouteOKR q r e (stayRoute e) A := by
  refine ⟨fun p hp => by simp [stayRoute] at hp; rw [hp]; exact he, fun s _ S _ => ?_⟩
  have : defect (stayRoute (K := K) e) e S = 0 := by
    simp [defect, lfcl, stayRoute]
  rw [this, zero_mul, ZMod.val_zero]
  exact dvd_zero _

omit [NeZero K] in
/-- **A full box is a valid route for every weight.** -/
theorem routeOKR_fullBox {e : Finset (Fin n)} {ρ : Fin n → Fin n} (he : e.card = r)
    (h : BoxOK e ∅ ρ) (A : Finset (ZMod K)) : RouteOKR q r e (boxRoute e ∅ ρ) A := by
  refine ⟨fun p hp => (card_boxRoute_sets h hp).trans he, fun s _ S hS => ?_⟩
  rw [defect_boxRoute h, boxCl, box_sum_eq_zero h (by omega), neg_zero, zero_mul, ZMod.val_zero]
  exact dvd_zero _

/-- **A box is valid for the weights that are divisible at every face containing the moved
part.** -/
theorem routeOKR_box {e F : Finset (Fin n)} {ρ : Fin n → Fin n} (hK : ModsOK q r K)
    (he : e.card = r) (h : BoxOK e F ρ) {A : Finset (ZMod K)}
    (hA : ∀ s ∈ A, ∀ S' : Finset (Fin n), e \ F ⊆ S' → S' ⊆ e → S'.card < r →
      (q - S'.card).choose (r - S'.card) ∣ s.val) :
    RouteOKR q r e (boxRoute e F ρ) A := by
  refine ⟨fun p hp => (card_boxRoute_sets h hp).trans he, fun s hs S hS => ?_⟩
  rw [defect_boxRoute h]
  by_cases h0 : boxCl (K := K) e F ρ S = 0
  · rw [h0, neg_zero, zero_mul, ZMod.val_zero]; exact dvd_zero _
  · obtain ⟨S', h1, h2, h3⟩ := box_cover_card (R := ZMod K) h h0
    have hdiv := hA s hs S' h1 h2 (by omega)
    rw [h3] at hdiv
    exact dvd_val_mul (hK _ hS) hdiv

/-- **A box moving a part that lies in no other current set is valid for the allowed values.** -/
theorem routeOKR_loneBox {e F : Finset (Fin n)} {ρ : Fin n → Fin n} (hK : ModsOK q r K)
    (he : e.card = r) (h : BoxOK e F ρ) {P : Finset (Finset (Fin n))}
    (hlone : LoneIn P e (e \ F)) : RouteOKR q r e (boxRoute e F ρ) (allowedR (K := K) q r P e) := by
  refine routeOKR_box hK he h fun s hs S' h1 h2 h3 => ?_
  simp only [allowedR, mem_filter, mem_univ, true_and] at hs
  exact hs S' (mem_powerset.2 h2) h3 fun f hf hsub => hlone f hf (h1.trans hsub)

end RefinedAbsorption.HyperPlan
