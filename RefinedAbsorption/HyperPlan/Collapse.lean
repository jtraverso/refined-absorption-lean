module
public import RefinedAbsorption.HyperPlan.Moves
public import RefinedAbsorption.HyperPlan.Strong

/-!
# Collapsing an `r`-partite `r`-graph onto a single set

This file gives a first complete `r`-uniform plan for every `r`, built only from the moves of
`HyperPlan.Moves`.  The vertex set is split into `r` classes by `σ : Fin n → Fin r`, and every class
`i` has a *hub* `z i` (`σ (z i) = i`).  A set is *partite* if it has one vertex in each class; a
partite set is determined by its *non-hub part* (`eq_of_nonHub_eq`).

The plan `collapsePlan σ z` has `r + 1` stages.  Stage `0` keeps everything; at stage `t ≥ 1` every
set whose non-hub part `N` has exactly `r + 1 - t` vertices is moved along the box with fixed hubs
that replaces every vertex of `N` by the hub of its class.  The non-hub part of every new set is a
proper subset of `N`, so at stage `t` no current set has a larger non-hub part, `N` lies in no
other current set, and the box is valid for the values allowed by loneliness
(`routeOKR_loneBox`).

* `collapse_plan`: for every partite input, `collapsePlan σ z` is a valid plan whose final family
  is contained in `{Z}`, `Z` the set of hubs.
* `partite_strongMultiRefiner`: hence every partite `r`-graph has a strong multi-refiner (through
  `plan_strongR`) with at most one final set.  The degree budget is not controlled: all the sets are
  routed through the same hubs.  Controlling it (the budget `C · max(D, n^{1-1/r} log n)` of
  `RPlans`) requires spreading the routes over many hubs, which is not done here.
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid RefinedAbsorption.Placement

variable {n K r : ℕ} (σ : Fin n → Fin r) (z : Fin r → Fin n)

/-- A set with one vertex in each class. -/
def Partite (e : Finset (Fin n)) : Prop := e.card = r ∧ Set.InjOn σ e

/-- The vertices of `e` that are not the hub of their class. -/
def nonHub (e : Finset (Fin n)) : Finset (Fin n) := e.filter fun v => z (σ v) ≠ v

/-- The stage collapsing the sets with exactly `k` non-hub vertices. -/
noncomputable def collapseSpec (k : ℕ) : SpecR n K := fun _ e =>
  if (nonHub σ z e).card = k then boxRoute e (e \ nonHub σ z e) (fun v => z (σ v))
  else stayRoute e

/-- The collapsing plan: a stage that keeps everything, then the stages `k = r, r - 1, …, 1`. -/
noncomputable def collapsePlan : List (SpecR n K) :=
  (List.range (r + 1)).map fun t => collapseSpec σ z (r + 1 - t)

/-- The set of hubs. -/
def hubSet : Finset (Fin n) := univ.image z

variable {σ z}

lemma nonHub_subset (e : Finset (Fin n)) : nonHub σ z e ⊆ e := filter_subset _ _

lemma partite_surj {e : Finset (Fin n)} (he : Partite σ e) (i : Fin r) : ∃ u ∈ e, σ u = i := by
  have h1 : (e.image σ).card = r := by rw [card_image_of_injOn he.2, he.1]
  have h2 : e.image σ = univ := eq_univ_of_card _ (by rw [h1, Fintype.card_fin])
  have : i ∈ e.image σ := h2 ▸ mem_univ i
  simpa using this

/-- **A partite set is determined by its non-hub part.** -/
lemma eq_of_nonHub_eq {e f : Finset (Fin n)} (he : Partite σ e)
    (hf : Partite σ f) (h : nonHub σ z e = nonHub σ z f) : e = f := by
  symm
  apply eq_of_subset_of_card_le _ (by rw [he.1, hf.1])
  intro v hv
  by_cases hvh : z (σ v) = v
  · obtain ⟨u, hu, hσ⟩ := partite_surj he (σ v)
    by_cases huh : z (σ u) = u
    · have : v = u := by rw [← hvh, ← hσ, huh]
      exact this ▸ hu
    · have hu' : u ∈ nonHub σ z f := h ▸ mem_filter.2 ⟨hu, huh⟩
      have huf := nonHub_subset f hu'
      have : u = v := hf.2 huf hv hσ
      subst this; exact absurd hvh huh
  · have : v ∈ nonHub σ z e := h ▸ mem_filter.2 ⟨hv, hvh⟩
    exact nonHub_subset e this

lemma boxOK_collapse (hz : ∀ i, σ (z i) = i) {e : Finset (Fin n)} (he : Partite σ e) :
    BoxOK e (e \ nonHub σ z e) (fun v => z (σ v)) where
  sub := sdiff_subset
  inj x hx y hy hxy := by
    have hx' := (mem_sdiff.1 (mem_coe.1 hx)).1
    have hy' := (mem_sdiff.1 (mem_coe.1 hy)).1
    apply he.2 hx' hy'
    have := congrArg σ hxy
    simpa [hz] using this
  out x hx hzx := by
    have hxe := (mem_sdiff.1 hx).1
    have hxN : x ∈ nonHub σ z e := by
      by_contra hc; exact (mem_sdiff.1 hx).2 (mem_sdiff.2 ⟨hxe, hc⟩)
    have : z (σ x) = x := he.2 hzx hxe (by simp [hz])
    exact (mem_filter.1 hxN).2 this

lemma sdiff_sdiff_nonHub (e : Finset (Fin n)) : e \ (e \ nonHub σ z e) = nonHub σ z e :=
  Finset.sdiff_sdiff_eq_self (nonHub_subset e)

/-- The transversals of a collapsing box are partite, with non-hub part `N ∩ J`. -/
lemma bt_collapse (hz : ∀ i, σ (z i) = i) {e : Finset (Fin n)} (he : Partite σ e) {J : Finset (Fin n)}
    (hJ : J ∈ bJs e (e \ nonHub σ z e)) :
    Partite σ (bt e (fun v => z (σ v)) J) ∧
      nonHub σ z (bt e (fun v => z (σ v)) J) = nonHub σ z e ∩ J := by
  have hbox := boxOK_collapse hz he
  have hJe : J ⊆ e := mem_powerset.1 (mem_filter.1 hJ).1
  refine ⟨⟨(card_bt hbox hJ).trans he.1, ?_⟩, ?_⟩
  · intro a ha b hb hab
    simp only [bt, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe, mem_sdiff] at ha hb
    rcases ha with ha | ⟨x, ⟨hx, hxJ⟩, rfl⟩ <;> rcases hb with hb | ⟨y, ⟨hy, hyJ⟩, rfl⟩
    · exact he.2 (hJe ha) (hJe hb) hab
    · simp only [hz] at hab
      exact absurd (he.2 (hJe ha) hy hab ▸ ha) hyJ
    · simp only [hz] at hab
      exact absurd ((he.2 hx (hJe hb) hab) ▸ hb) hxJ
    · simp only [hz] at hab
      rw [he.2 hx hy hab]
  · ext v
    simp only [nonHub, bt, mem_filter, mem_union, mem_image, mem_sdiff, mem_inter]
    constructor
    · rintro ⟨hv | ⟨x, -, rfl⟩, hvh⟩
      · exact ⟨⟨hJe hv, hvh⟩, hv⟩
      · exact absurd (by simp [hz]) hvh
    · rintro ⟨⟨-, hvh⟩, hv⟩
      exact ⟨Or.inl hv, hvh⟩

variable [NeZero K]

omit [NeZero K] in
lemma getD_collapsePlan {t : ℕ} (ht : t < r + 1) :
    (collapsePlan (K := K) σ z).getD t idSpecR = collapseSpec σ z (r + 1 - t) := by
  unfold collapsePlan
  rw [List.getD_eq_getElem _ _ (by simpa using ht)]
  simp

omit [NeZero K] in
lemma length_collapsePlan : (collapsePlan (K := K) σ z).length = r + 1 := by
  simp [collapsePlan]

omit [NeZero K] in
lemma rtR_collapse {X : Finset (Finset (Fin n))} {t : ℕ} (ht : t < r + 1) (e : Finset (Fin n)) :
    rtR (collapsePlan (K := K) σ z) X t e =
      if (nonHub σ z e).card = r + 1 - t then boxRoute e (e \ nonHub σ z e) (fun v => z (σ v))
      else stayRoute e := by
  unfold rtR
  rw [getD_collapsePlan ht]
  rfl

/-- The invariant of the collapsing plan. -/
lemma collapse_inv (hz : ∀ i, σ (z i) = i) {X : Finset (Finset (Fin n))}
    (hX : ∀ e ∈ X, Partite σ e) {t : ℕ} (ht : t ≤ r + 1) :
    ∀ f ∈ prunR (collapsePlan (K := K) σ z) X t, Partite σ f ∧ (nonHub σ z f).card + t ≤ r + 1 := by
  induction t with
  | zero =>
    intro f hf
    refine ⟨hX f hf, ?_⟩
    have := card_le_card (nonHub_subset (σ := σ) (z := z) f)
    rw [(hX f hf).1] at this
    omega
  | succ t ih =>
    intro f hf
    rw [prunR_succ] at hf
    obtain ⟨e, he, hfe⟩ := mem_biUnion.1 hf
    obtain ⟨hpe, hce⟩ := ih (by omega) e he
    rw [rtR_collapse (by omega)] at hfe
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hfe)
    split_ifs at hp with hk
    · obtain ⟨J, hJ, hJne, hpJ⟩ := mem_boxRoute hp
      obtain ⟨hpart, hN⟩ := bt_collapse hz hpe hJ
      rw [hpJ]
      refine ⟨hpart, ?_⟩
      rw [hN]
      have hJe : J ⊆ e := mem_powerset.1 (mem_filter.1 hJ).1
      have hFJ : e \ nonHub σ z e ⊆ J := (mem_filter.1 hJ).2
      obtain ⟨x, hxe, hxJ⟩ : ∃ x ∈ e, x ∉ J := by
        by_contra hc; push_neg at hc
        exact hJne (subset_antisymm hJe hc)
      have hxN : x ∈ nonHub σ z e := by
        by_contra hc; exact hxJ (hFJ (mem_sdiff.2 ⟨hxe, hc⟩))
      have hlt : (nonHub σ z e ∩ J).card < (nonHub σ z e).card :=
        card_lt_card ⟨inter_subset_left, fun h => hxJ (mem_inter.1 (h hxN)).2⟩
      omega
    · simp only [stayRoute, List.mem_singleton] at hp
      subst hp
      refine ⟨hpe, ?_⟩
      show (nonHub σ z e).card + (t + 1) ≤ r + 1
      omega

/-- **The collapsing plan is valid, and its final family has at most one set.** -/
theorem collapse_plan {q : ℕ} (hK : ModsOK q r K) (hz : ∀ i, σ (z i) = i)
    {X : Finset (Finset (Fin n))} (hX : ∀ e ∈ X, Partite σ e) :
    PlanOKR q r (2 ^ r) (collapsePlan (K := K) σ z) X ∧
      (collapsePlan (K := K) σ z).length = r + 1 ∧
      (prunR (collapsePlan (K := K) σ z) X (r + 1)).card ≤ 1 := by
  refine ⟨⟨fun e he => (hX e he).1, ?_, ?_⟩, length_collapsePlan, ?_⟩
  · intro t ht e he
    rw [length_collapsePlan] at ht
    obtain ⟨hpe, hce⟩ := collapse_inv hz hX ht.le e he
    rw [rtR_collapse ht]
    split_ifs with hk
    · have ht1 : t ≠ 0 := by
        intro h0; subst h0
        have := card_le_card (nonHub_subset (σ := σ) (z := z) e)
        rw [hpe.1] at this; omega
      unfold wts
      rw [if_neg ht1]
      refine routeOKR_loneBox hK hpe.1 (boxOK_collapse hz hpe) ?_
      rw [sdiff_sdiff_nonHub]
      intro f hf hsub
      obtain ⟨hpf, hcf⟩ := collapse_inv hz hX ht.le f hf
      have hsubN : nonHub σ z e ⊆ nonHub σ z f := by
        intro v hv
        exact mem_filter.2 ⟨hsub hv, (mem_filter.1 hv).2⟩
      have heq : nonHub σ z e = nonHub σ z f :=
        eq_of_subset_of_card_le hsubN (by omega)
      exact (eq_of_nonHub_eq hpe hpf heq).symm
    · exact routeOKR_stay hpe.1 _
  · intro t ht e he
    rw [length_collapsePlan] at ht
    obtain ⟨hpe, -⟩ := collapse_inv hz hX ht.le e he
    rw [rtR_collapse ht]
    split_ifs
    · exact (length_boxRoute _ _ _).trans (by rw [hpe.1])
    · simp only [stayRoute, List.length_singleton]
      exact Nat.one_le_two_pow
  · have hZ : Partite σ (hubSet z) := by
      have hinj : Function.Injective z := fun i j h => by
        have := congrArg σ h; simpa [hz] using this
      refine ⟨by rw [hubSet, card_image_of_injective _ hinj, card_univ, Fintype.card_fin], ?_⟩
      intro a ha b hb hab
      simp only [hubSet, coe_image, coe_univ, Set.image_univ, Set.mem_range] at ha hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      simp only [hz] at hab
      rw [hab]
    have hNZ : nonHub σ z (hubSet z) = ∅ := by
      ext v
      simp only [nonHub, hubSet, mem_filter, mem_image, mem_univ, true_and, notMem_empty,
        iff_false, not_and, not_not]
      rintro ⟨i, rfl⟩
      simp [hz]
    apply card_le_one.2
    have key : ∀ f ∈ prunR (collapsePlan (K := K) σ z) X (r + 1), f = hubSet z := by
      intro f hf
      obtain ⟨hpf, hcf⟩ := collapse_inv hz hX le_rfl f hf
      have : nonHub σ z f = ∅ := card_eq_zero.1 (by omega)
      exact eq_of_nonHub_eq hpf hZ (by rw [this, hNZ])
    intro a ha b hb
    rw [key a ha, key b hb]

/-- **Every partite `r`-graph has a strong multi-refiner with at most one final set** (with an
uncontrolled degree budget `B`). -/
theorem partite_strongMultiRefiner {q : ℕ} (hK : ModsOK q r K) (hK1 : 1 < K)
    (hz : ∀ i, σ (z i) = i) {X : Finset (Finset (Fin n))} (hX : ∀ e ∈ X, Partite σ e) :
    ∃ B : ℕ, 1 ≤ B ∧
      (liftS (wsg (pwR (collapsePlan σ z) X)) (inpR (collapsePlan σ z) X (K := K) q r 0)).image
        (cpEnds (wsg (pwR (collapsePlan σ z) X))) = X ∧
      IsStrongMultiRefiner q r (CplR K 1 (2 ^ r)) (cpEnds (wsg (pwR (K := K) (collapsePlan σ z) X)))
        (liftS (wsg (pwR (collapsePlan σ z) X)) (inpR (collapsePlan σ z) X q r 0))
        (liftS (wsg (pwR (collapsePlan σ z) X)) (inpR (collapsePlan σ z) X q r 0))
        (liftS (wsg (pwR (collapsePlan σ z) X)) (RallR (collapsePlan σ z) X q r (r + 1)))
        ((WallR (collapsePlan σ z) X q r (r + 1) ∪ WbaseR (collapsePlan σ z) X q r).image
          (liftS (wsg (pwR (collapsePlan σ z) X)))) B := by
  obtain ⟨hok, hlen, hM⟩ := collapse_plan (K := K) hK hz hX
  set B := X.card + ∑ t ∈ range (r + 1), (prunR (collapsePlan (K := K) σ z) X t).card + 1
  have hP : ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ t ∈ range (collapsePlan (K := K) σ z).length, passR (collapsePlan (K := K) σ z) X t S ≤ B := by
    intro S _
    rw [hlen]
    refine (sum_le_sum fun t _ => card_filter_le _ _).trans ?_
    omega
  have hXB : ∀ S : Finset (Fin n), S.card = r - 1 → (X.filter (S ⊆ ·)).card ≤ B := by
    intro S _
    have := card_filter_le X (S ⊆ ·)
    omega
  have := plan_strongR (M := 1) hK hK1 hok (by simp [hlen]) (by rw [hlen]; exact hM)
    (by omega : 1 ≤ B) hXB hP
  rw [hlen] at this
  exact ⟨B, by omega, this⟩

end RefinedAbsorption.HyperPlan
