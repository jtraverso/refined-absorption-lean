module
public import RefinedAbsorption.OddGrid.PlanMult

/-!
# Loads of a plan

`pass sp X t v` is the number of pairs of stage `t` whose route touches the vertex `v`.  For a
valid plan, the number of labels of stage `t` whose pair contains `v` is at most
`13 K² · pass sp X t v` (`stR_load`), and the labels of the whole plan containing `v` number at
most `14 K² · Σ_{t < T} pass sp X t v` (`plan_load`).
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner

variable {n K : ℕ}

/-- The number of pairs of stage `t` whose route touches `v`. -/
def pass (sp : List (Spec n)) (X : Finset (Finset (Fin n))) (t : ℕ) (v : Fin n) : ℕ :=
  ((prun sp X t).filter (fun e => v ∈ (rt sp X t e).visit e)).card

lemma wpairs_subset {l : List (Fin n)} {f : Finset (Fin n)} (hf : f ∈ wpairs l) :
    f ⊆ l.toFinset := by
  induction l with
  | nil => simp [wpairs] at hf
  | cons p tl ih =>
    cases tl with
    | nil => simp [wpairs] at hf
    | cons q rest =>
      simp only [wpairs, List.mem_cons] at hf
      rcases hf with rfl | hf
      · intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> simp
      · exact (ih hf).trans (by intro x hx; simp only [List.mem_toFinset] at hx ⊢; simp [hx])

lemma rest_subset_visit (r : Route n) (w : ZMod K) (e : Finset (Fin n)) {s}
    (hs : s ∈ r.rest w) : s.1 ⊆ r.visit e := by
  cases r with
  | walk l =>
    have : s.1 ∈ (walkL l w).map Prod.fst := List.mem_map_of_mem hs
    rw [map_fst_walkL] at this
    exact wpairs_subset this
  | move f =>
    simp only [Route.rest, List.mem_singleton] at hs
    subst hs; exact subset_union_right

lemma pair_subset_visit {e : Finset (Fin n)} {r : Route n} (h : RouteOK e r) : e ⊆ r.visit e := by
  cases r with
  | walk l =>
    obtain ⟨p, tl, rfl, -, -, -, rfl, -⟩ := h
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    simp only [Route.visit, List.mem_toFinset]
    rcases hx with rfl | rfl
    · simp
    · exact List.getLast_mem _
  | move f => exact subset_union_left

lemma length_rest_le {e : Finset (Fin n)} {r : Route n} (h : RouteOK e r) (w : ZMod K) :
    (r.rest w).length ≤ 3 := by
  cases r with
  | walk l =>
    obtain ⟨p, tl, rfl, -, -, hl, -⟩ := h
    simp only [Route.rest, length_walkL, List.length_cons]; omega
  | move f => simp [Route.rest]

variable [NeZero K] {q : ℕ} {sp : List (Spec n)} {X : Finset (Finset (Fin n))}

/-- At most `K` inputs lie on a pair. -/
lemma inp_fiber_le (t : ℕ) (e : Finset (Fin n)) :
    ((inp sp X (K := K) q t).filter (fun ℓ => (plab ℓ).1 = e)).card ≤ K := by
  cases t with
  | zero =>
    refine (card_le_one.2 ?_).trans (Nat.one_le_iff_ne_zero.2 (NeZero.ne K))
    intro a ha b hb
    obtain ⟨ha, hae⟩ := mem_filter.1 ha
    obtain ⟨hb, hbe⟩ := mem_filter.1 hb
    obtain ⟨e₁, -, rfl⟩ := mem_inp_zero.1 ha
    obtain ⟨e₂, -, rfl⟩ := mem_inp_zero.1 hb
    simp only [plab] at hae hbe
    rw [hae, hbe]
  | succ t =>
    have hsub : (inp sp X (K := K) q (t + 1)).filter (fun ℓ => (plab ℓ).1 = e) ⊆
        (univ : Finset (ZMod K)).image
          (Lab.cp t e (slen t (inp sp X (K := K) q t) (restFP sp X t) e)) := by
      intro ℓ hℓ
      obtain ⟨hℓ, he⟩ := mem_filter.1 hℓ
      obtain ⟨e', -, s, -, rfl⟩ := mem_inp_succ.1 hℓ
      simp only [plab] at he
      subst he
      exact mem_image.2 ⟨s, mem_univ _, rfl⟩
    exact (card_le_card hsub).trans (card_image_le.trans (by simp))

/-- Inputs touching a set of pairs. -/
lemma inp_touch_le (t : ℕ) (Q : Finset (Fin n) → Prop) [DecidablePred Q] :
    ((inp sp X (K := K) q t).filter (fun ℓ => Q (plab ℓ).1)).card ≤
      K * ((prun sp X t).filter Q).card := by
  apply card_le_mul_card_image_of_maps_to (f := fun ℓ => (plab ℓ).1)
  · intro ℓ hℓ
    obtain ⟨hℓ, hQ⟩ := mem_filter.1 hℓ
    exact mem_filter.2 ⟨(inp_pair hℓ).1, hQ⟩
  · intro e _
    refine (card_le_card ?_).trans (inp_fiber_le (q := q) (sp := sp) (X := X) t e)
    intro ℓ hℓ
    simp only [mem_filter] at hℓ ⊢
    exact ⟨hℓ.1.1, hℓ.2⟩

lemma card_chR_le (t : ℕ) (e : Finset (Fin n)) (m : ℕ) :
    (chR (Lab.cp (K := K) t e) (Lab.cn t e) m).card ≤ 1 + 2 * K * m := by
  unfold chR
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right ((card_union_le _ _).trans
    (Nat.add_le_add_left card_image_le _)) _).trans ?_
  refine (Nat.add_le_add_left card_image_le _).trans ?_
  simp only [card_singleton, card_product, Nat.card_Icc, card_univ, ZMod.card,
    Nat.add_sub_cancel]
  nlinarith

/-- The rests touching `v`. -/
lemma rests_load (hok : PlanOK sp X) {t : ℕ} (ht : t < sp.length) (v : Fin n) :
    ((restSet t (inp sp X (K := K) q t) (restFP sp X t)).filter
      (fun r => v ∈ restPair (restFP sp X t) r)).card ≤ 3 * K * pass sp X t v := by
  rw [restSet, filter_biUnion]
  refine card_biUnion_le.trans ?_
  have hterm : ∀ ℓ ∈ inp sp X (K := K) q t,
      ((rests t (restFP sp X t) ℓ).filter (fun r => v ∈ restPair (restFP sp X t) r)).card ≤
        3 * (if v ∈ (rt sp X t (plab ℓ).1).visit (plab ℓ).1 then 1 else 0) := by
    intro ℓ hℓ
    have hok' := hok.route t ht _ (inp_pair hℓ).1
    split_ifs with hv
    · refine (card_filter_le _ _).trans ?_
      rw [rests, card_image_of_injective _ (fun a b h => by simpa using h), card_range]
      have := length_rest_le hok' (plab ℓ).2
      rw [mul_one]; exact this
    · suffices h : (rests t (restFP sp X t) ℓ).filter
          (fun r => v ∈ restPair (restFP sp X t) r) = ∅ by rw [h]; simp
      rw [filter_eq_empty_iff]
      intro r hr hvr
      obtain ⟨k, hk, rfl⟩ := mem_rests.1 hr
      apply hv
      have hs : (restFP sp X t ℓ).getD k (∅, 0) ∈ restFP sp X t ℓ := by
        rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
      exact rest_subset_visit _ _ _ hs hvr
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum, sum_boole, mul_assoc]
  refine Nat.mul_le_mul_left _ ?_
  simp only [Nat.cast_id]
  exact inp_touch_le (q := q) t (fun e => v ∈ (rt sp X t e).visit e)

/-- **Load of a stage.** -/
lemma stR_load (hok : PlanOK sp X) {t : ℕ} (ht : t < sp.length) (v : Fin n) :
    ((stR t (inp sp X (K := K) q t) (restFP sp X t)).filter
      (fun x => v ∈ (pwP sp X x).1)).card ≤ 13 * K ^ 2 * pass sp X t v := by
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (NeZero.ne K)
  have hR := rests_load (K := K) (q := q) hok ht v
  set I := inp sp X (K := K) q t
  set rF := restFP sp X t
  -- anti labels
  have hA : ((I.image (Lab.anti t)).filter (fun x => v ∈ (pwP sp X x).1)).card ≤
      K * pass sp X t v := by
    have hsub : (I.image (Lab.anti t)).filter (fun x => v ∈ (pwP sp X x).1) ⊆
        (I.filter (fun ℓ => v ∈ (plab ℓ).1)).image (Lab.anti t) := by
      intro x hx
      obtain ⟨hx, hv⟩ := mem_filter.1 hx
      obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hx
      refine mem_image.2 ⟨ℓ, mem_filter.2 ⟨hℓ, ?_⟩, rfl⟩
      simp only [pwP] at hv
      rwa [(inp_pair hℓ).2] at hv
    refine (card_le_card hsub).trans (card_image_le.trans ?_)
    refine (inp_touch_le (q := q) t (fun e => v ∈ e)).trans (Nat.mul_le_mul_left _ ?_)
    refine card_le_card fun e he => ?_
    obtain ⟨he, hv⟩ := mem_filter.1 he
    exact mem_filter.2 ⟨he, pair_subset_visit (hok.route t ht e he) hv⟩
  -- rest labels
  have hB : ((restSet t I rF).filter (fun x => v ∈ (pwP sp X x).1)).card ≤
      3 * K * pass sp X t v := by
    refine le_trans (card_le_card fun x hx => ?_) hR
    obtain ⟨hx, hv⟩ := mem_filter.1 hx
    refine mem_filter.2 ⟨hx, ?_⟩
    obtain ⟨ℓ, -, k, -, rfl⟩ := mem_restSet.1 hx
    exact hv
  -- chain labels
  have hC : (((outs t I rF).biUnion fun e => chR (Lab.cp (K := K) t e) (Lab.cn t e) (slen t I rF e)).filter
      (fun x => v ∈ (pwP sp X x).1)).card ≤ (1 + 2 * K) * (3 * K * pass sp X t v) := by
    have hsub : ((outs t I rF).biUnion fun e => chR (Lab.cp (K := K) t e) (Lab.cn t e)
        (slen t I rF e)).filter (fun x => v ∈ (pwP sp X x).1) ⊆
        ((outs t I rF).filter (v ∈ ·)).biUnion fun e =>
          chR (Lab.cp (K := K) t e) (Lab.cn t e) (slen t I rF e) := by
      intro x hx
      obtain ⟨hx, hv⟩ := mem_filter.1 hx
      obtain ⟨e, he, hxe⟩ := mem_biUnion.1 hx
      refine mem_biUnion.2 ⟨e, mem_filter.2 ⟨he, ?_⟩, hxe⟩
      rcases mem_chR hxe with ⟨k, s, rfl⟩ | ⟨k, s, rfl⟩ <;> exact hv
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    have h1 : ∀ e ∈ (outs t I rF).filter (v ∈ ·),
        (chR (Lab.cp (K := K) t e) (Lab.cn t e) (slen t I rF e)).card ≤
          (1 + 2 * K) * slen t I rF e := by
      intro e he
      have hpos := slen_pos (mem_filter.1 he).1
      refine (card_chR_le t e _).trans ?_
      nlinarith
    refine (sum_le_sum h1).trans ?_
    rw [← mul_sum]
    refine Nat.mul_le_mul_left _ (le_trans (le_of_eq ?_) hR)
    -- the chains on pairs through `v` carry exactly the rests through `v`
    rw [card_eq_sum_card_fiberwise (f := restPair rF) (t := (outs t I rF).filter (v ∈ ·))]
    · refine sum_congr rfl fun e he => ?_
      unfold slen onPair
      congr 1
      ext r
      simp only [mem_filter]
      constructor
      · rintro ⟨hr, rfl⟩; exact ⟨⟨hr, (mem_filter.1 he).2⟩, rfl⟩
      · rintro ⟨⟨hr, -⟩, rfl⟩; exact ⟨hr, rfl⟩
    · intro r hr
      obtain ⟨hr, hv⟩ := mem_filter.1 hr
      exact mem_filter.2 ⟨mem_image_of_mem _ hr, hv⟩
  unfold stR
  rw [filter_union, filter_union]
  refine (card_union_le _ _).trans ?_
  have hu := card_union_le ((I.image (Lab.anti t)).filter (fun x => v ∈ (pwP sp X x).1))
    ((restSet t I rF).filter (fun x => v ∈ (pwP sp X x).1))
  have : K * pass sp X t v + 3 * K * pass sp X t v + (1 + 2 * K) * (3 * K * pass sp X t v) ≤
      13 * K ^ 2 * pass sp X t v := by
    have : K ≤ K ^ 2 := by nlinarith
    nlinarith
  omega

/-- **Load of a plan.** -/
theorem plan_load (hok : PlanOK sp X) (hT : 1 ≤ sp.length) (v : Fin n) :
    ((inp sp X (K := K) q 0 ∪ Rall sp X q sp.length).filter
      (fun x => v ∈ (pwP sp X x).1)).card ≤
      14 * K ^ 2 * ∑ t ∈ range sp.length, pass sp X t v := by
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (NeZero.ne K)
  rw [filter_union]
  refine (card_union_le _ _).trans ?_
  have h0 : ((inp sp X (K := K) q 0).filter (fun x => v ∈ (pwP sp X x).1)).card ≤
      K * pass sp X 0 v := by
    refine le_trans (card_le_card fun x hx => ?_) ((inp_touch_le (q := q) 0
      (fun e => v ∈ (rt sp X 0 e).visit e)).trans le_rfl)
    obtain ⟨hx, hv⟩ := mem_filter.1 hx
    refine mem_filter.2 ⟨hx, ?_⟩
    rw [(inp_pair hx).2] at hv
    exact pair_subset_visit (hok.route 0 hT _ (inp_pair hx).1) hv
  have h1 : ((Rall sp X (K := K) q sp.length).filter (fun x => v ∈ (pwP sp X x).1)).card ≤
      13 * K ^ 2 * ∑ t ∈ range sp.length, pass sp X t v := by
    rw [Rall, filter_biUnion, mul_sum]
    refine card_biUnion_le.trans (sum_le_sum fun t ht => stR_load hok (mem_range.1 ht) v)
  have h2 : pass sp X 0 v ≤ ∑ t ∈ range sp.length, pass sp X t v :=
    single_le_sum (f := fun t => pass sp X t v) (fun _ _ => Nat.zero_le _)
      (mem_range.2 (by omega))
  have h3 : K * pass sp X 0 v ≤ K ^ 2 * ∑ t ∈ range sp.length, pass sp X t v := by
    have : K ≤ K ^ 2 := by nlinarith
    exact Nat.mul_le_mul this h2
  nlinarith

end RefinedAbsorption.OddGrid
