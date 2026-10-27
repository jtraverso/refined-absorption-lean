module
public import RefinedAbsorption.HyperPlan.Plan
public import RefinedAbsorption.OddGrid.PlanLoad

/-!
# Loads of a plan, uniformity `r`

The *visit set* of a current set `e` is `e` together with all sets of its route.  `passR sp X t S`
is the number of current sets of stage `t` whose visit set contains the vertex set `S`.

* `stR_loadR`: the labels of stage `t` lying on a set containing `S` number at most
  `4 (L + 1) K² · passR sp X t S`;
* `stW_loadR`: the pieces of stage `t` whose vertex set contains `S` number at most
  `4 (L + 1) K² · passR sp X t S`.

Here `L` bounds the lengths of the routes.  For `r = 2` and `S = {v}` this is the vertex load of
`OddGrid.PlanLoad`; for general `r` the relevant sets are the `(r - 1)`-sets `S`.
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid

variable {n K : ℕ} [NeZero K]

/-- The vertices visited by the route `ro` of `e`. -/
def visitR (e : Finset (Fin n)) (ro : List (Finset (Fin n) × ZMod K)) : Finset (Fin n) :=
  e ∪ (ro.map Prod.fst).toFinset.sup id

omit [NeZero K] in
lemma subset_visitR (e : Finset (Fin n)) (ro : List (Finset (Fin n) × ZMod K)) :
    e ⊆ visitR e ro := subset_union_left

omit [NeZero K] in
lemma route_subset_visitR (e : Finset (Fin n)) {ro : List (Finset (Fin n) × ZMod K)}
    {p : Finset (Fin n) × ZMod K} (hp : p ∈ ro) : p.1 ⊆ visitR e ro := by
  unfold visitR
  have hm : p.1 ∈ (ro.map Prod.fst).toFinset := List.mem_toFinset.2 (List.mem_map_of_mem hp)
  have : p.1 ⊆ (ro.map Prod.fst).toFinset.sup id := le_sup (f := id) hm
  exact this.trans subset_union_right

/-- The number of current sets of stage `t` whose route visits all of `S`. -/
def passR (sp : List (SpecR n K)) (X : Finset (Finset (Fin n))) (t : ℕ) (S : Finset (Fin n)) :
    ℕ :=
  ((prunR sp X t).filter (fun e => S ⊆ visitR e (rtR sp X t e))).card

variable {q r L : ℕ} {sp : List (SpecR n K)} {X : Finset (Finset (Fin n))}

/-- At most `K` inputs lie on a set. -/
lemma inpR_fiber_le (t : ℕ) (e : Finset (Fin n)) :
    ((inpR sp X (K := K) q r t).filter (fun ℓ => (plab ℓ).1 = e)).card ≤ K := by
  cases t with
  | zero =>
    refine (card_le_one.2 ?_).trans (Nat.one_le_iff_ne_zero.2 (NeZero.ne K))
    intro a ha b hb
    obtain ⟨ha, hae⟩ := mem_filter.1 ha
    obtain ⟨hb, hbe⟩ := mem_filter.1 hb
    obtain ⟨e₁, -, rfl⟩ := mem_inpR_zero.1 ha
    obtain ⟨e₂, -, rfl⟩ := mem_inpR_zero.1 hb
    simp only [plab] at hae hbe
    rw [hae, hbe]
  | succ t =>
    have hsub : (inpR sp X (K := K) q r (t + 1)).filter (fun ℓ => (plab ℓ).1 = e) ⊆
        (univ : Finset (ZMod K)).image
          (Lab.cp t e (slen t (inpR sp X (K := K) q r t) (restFR sp X t) e)) := by
      intro ℓ hℓ
      obtain ⟨hℓ, he⟩ := mem_filter.1 hℓ
      obtain ⟨e', -, s, -, rfl⟩ := mem_inpR_succ.1 hℓ
      simp only [plab] at he
      subst he
      exact mem_image.2 ⟨s, mem_univ _, rfl⟩
    exact (card_le_card hsub).trans (card_image_le.trans (by simp))

/-- Inputs on sets with a given property. -/
lemma inpR_touch_le (t : ℕ) (Q : Finset (Fin n) → Prop) [DecidablePred Q] :
    ((inpR sp X (K := K) q r t).filter (fun ℓ => Q (plab ℓ).1)).card ≤
      K * ((prunR sp X t).filter Q).card := by
  apply card_le_mul_card_image_of_maps_to (f := fun ℓ => (plab ℓ).1)
  · intro ℓ hℓ
    obtain ⟨hℓ, hQ⟩ := mem_filter.1 hℓ
    exact mem_filter.2 ⟨(inpR_pair hℓ).1, hQ⟩
  · intro e _
    refine (card_le_card ?_).trans (inpR_fiber_le (q := q) (r := r) (sp := sp) (X := X) t e)
    intro ℓ hℓ
    simp only [mem_filter] at hℓ ⊢
    exact ⟨hℓ.1.1, hℓ.2⟩

lemma card_chR_le' (t : ℕ) (e : Finset (Fin n)) (m : ℕ) :
    (OddGrid.chR (Lab.cp (K := K) t e) (Lab.cn t e) m).card ≤ 1 + 2 * K * m :=
  card_chR_le t e m

/-- The inputs whose route visits `S`. -/
lemma inp_visit_le (t : ℕ) (S : Finset (Fin n)) :
    ((inpR sp X (K := K) q r t).filter
      (fun ℓ => S ⊆ visitR (plab ℓ).1 (rtR sp X t (plab ℓ).1))).card ≤ K * passR sp X t S :=
  inpR_touch_le (q := q) (r := r) t (fun e => S ⊆ visitR e (rtR sp X t e))

/-- The rests lying on a set containing `S`. -/
lemma rests_loadR (hok : PlanOKR q r L sp X) {t : ℕ} (ht : t < sp.length) (S : Finset (Fin n)) :
    ((restSet t (inpR sp X (K := K) q r t) (restFR sp X t)).filter
      (fun x => S ⊆ restPair (restFR sp X t) x)).card ≤ L * K * passR sp X t S := by
  rw [restSet, filter_biUnion]
  refine card_biUnion_le.trans ?_
  have hterm : ∀ ℓ ∈ inpR sp X (K := K) q r t,
      ((rests t (restFR sp X t) ℓ).filter (fun x => S ⊆ restPair (restFR sp X t) x)).card ≤
        L * (if S ⊆ visitR (plab ℓ).1 (rtR sp X t (plab ℓ).1) then 1 else 0) := by
    intro ℓ hℓ
    have hlen := hok.len t ht _ (inpR_pair hℓ).1
    split_ifs with hv
    · refine (card_filter_le _ _).trans ?_
      rw [rests, card_image_of_injective _ (fun a b h => by simpa using h), card_range]
      rw [mul_one]
      change (wroute _ _).length ≤ L
      simpa [wroute] using hlen
    · suffices h : (rests t (restFR sp X t) ℓ).filter
          (fun x => S ⊆ restPair (restFR sp X t) x) = ∅ by rw [h]; simp
      rw [filter_eq_empty_iff]
      intro x hx hvx
      obtain ⟨k, hk, rfl⟩ := mem_rests.1 hx
      apply hv
      have hs : (restFR sp X t ℓ).getD k (∅, 0) ∈ restFR sp X t ℓ := by
        rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
      have hs' : ((restFR sp X t ℓ).getD k (∅, 0)).1 ∈
          (rtR sp X t (plab ℓ).1).map Prod.fst := by
        have : ((restFR sp X t ℓ).getD k (∅, 0)).1 ∈ (restFR sp X t ℓ).map Prod.fst :=
          List.mem_map_of_mem hs
        rwa [restFR, map_fst_wroute] at this
      obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hs'
      refine hvx.trans ?_
      change ((restFR sp X t ℓ).getD k (∅, 0)).1 ⊆ _
      rw [← hpe]
      exact route_subset_visitR _ hp
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum, sum_boole, mul_assoc]
  refine Nat.mul_le_mul_left _ ?_
  simp only [Nat.cast_id]
  exact inp_visit_le t S

omit [NeZero K] in
/-- The rests on a set containing `S` are in bijection with the chain items on such sets. -/
lemma sum_slen_eq (t : ℕ) (I : Finset (Lab n K)) (restF : RestF n K) (S : Finset (Fin n)) :
    ∑ e ∈ (outs t I restF).filter (S ⊆ ·), slen t I restF e =
      ((restSet t I restF).filter (fun x => S ⊆ restPair restF x)).card := by
  symm
  rw [card_eq_sum_card_fiberwise (f := restPair restF) (t := (outs t I restF).filter (S ⊆ ·))]
  · refine sum_congr rfl fun e he => ?_
    unfold slen onPair
    congr 1
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hx, -⟩, rfl⟩; exact ⟨hx, rfl⟩
    · rintro ⟨hx, rfl⟩; exact ⟨⟨hx, (mem_filter.1 he).2⟩, rfl⟩
  · intro x hx
    obtain ⟨hx, hv⟩ := mem_filter.1 hx
    exact mem_filter.2 ⟨mem_image_of_mem _ hx, hv⟩

/-- **Label load of a stage.** -/
lemma stR_loadR (hok : PlanOKR q r L sp X) {t : ℕ} (ht : t < sp.length) (S : Finset (Fin n)) :
    ((stR t (inpR sp X (K := K) q r t) (restFR sp X t)).filter
      (fun x => S ⊆ (pwR sp X x).1)).card ≤ 4 * (L + 1) * K ^ 2 * passR sp X t S := by
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (NeZero.ne K)
  have hR := rests_loadR (K := K) hok ht S
  set I := inpR sp X (K := K) q r t
  set rF := restFR sp X t
  have hA : ((I.image (Lab.anti t)).filter (fun x => S ⊆ (pwR sp X x).1)).card ≤
      K * passR sp X t S := by
    have hsub : (I.image (Lab.anti t)).filter (fun x => S ⊆ (pwR sp X x).1) ⊆
        (I.filter (fun ℓ => S ⊆ visitR (plab ℓ).1 (rtR sp X t (plab ℓ).1))).image
          (Lab.anti t) := by
      intro x hx
      obtain ⟨hx, hv⟩ := mem_filter.1 hx
      obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hx
      refine mem_image.2 ⟨ℓ, mem_filter.2 ⟨hℓ, ?_⟩, rfl⟩
      simp only [pwR] at hv
      rw [(inpR_pair hℓ).2] at hv
      exact hv.trans (subset_visitR _ _)
    exact (card_le_card hsub).trans (card_image_le.trans (inp_visit_le t S))
  have hB : ((restSet t I rF).filter (fun x => S ⊆ (pwR sp X x).1)).card ≤
      L * K * passR sp X t S := by
    refine le_trans (card_le_card fun x hx => ?_) hR
    obtain ⟨hx, hv⟩ := mem_filter.1 hx
    refine mem_filter.2 ⟨hx, ?_⟩
    obtain ⟨ℓ, -, k, -, rfl⟩ := mem_restSet.1 hx
    exact hv
  have hC : (((outs t I rF).biUnion fun e => OddGrid.chR (Lab.cp (K := K) t e) (Lab.cn t e)
      (slen t I rF e)).filter (fun x => S ⊆ (pwR sp X x).1)).card ≤
      (1 + 2 * K) * (L * K * passR sp X t S) := by
    have hsub : ((outs t I rF).biUnion fun e => OddGrid.chR (Lab.cp (K := K) t e) (Lab.cn t e)
        (slen t I rF e)).filter (fun x => S ⊆ (pwR sp X x).1) ⊆
        ((outs t I rF).filter (S ⊆ ·)).biUnion fun e =>
          OddGrid.chR (Lab.cp (K := K) t e) (Lab.cn t e) (slen t I rF e) := by
      intro x hx
      obtain ⟨hx, hv⟩ := mem_filter.1 hx
      obtain ⟨e, he, hxe⟩ := mem_biUnion.1 hx
      refine mem_biUnion.2 ⟨e, mem_filter.2 ⟨he, ?_⟩, hxe⟩
      rcases mem_chR hxe with ⟨k, s, rfl⟩ | ⟨k, s, rfl⟩ <;> exact hv
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    have h1 : ∀ e ∈ (outs t I rF).filter (S ⊆ ·),
        (OddGrid.chR (Lab.cp (K := K) t e) (Lab.cn t e) (slen t I rF e)).card ≤
          (1 + 2 * K) * slen t I rF e := by
      intro e he
      have hpos := slen_pos (mem_filter.1 he).1
      refine (card_chR_le t e _).trans ?_
      nlinarith
    refine (sum_le_sum h1).trans ?_
    rw [← mul_sum, sum_slen_eq]
    exact Nat.mul_le_mul_left _ hR
  unfold stR
  rw [filter_union, filter_union]
  refine (card_union_le _ _).trans ?_
  have hu := card_union_le ((I.image (Lab.anti t)).filter (fun x => S ⊆ (pwR sp X x).1))
    ((restSet t I rF).filter (fun x => S ⊆ (pwR sp X x).1))
  have : K * passR sp X t S + L * K * passR sp X t S +
      (1 + 2 * K) * (L * K * passR sp X t S) ≤ 4 * (L + 1) * K ^ 2 * passR sp X t S := by
    have : K ≤ K ^ 2 := by nlinarith
    have hp := Nat.zero_le (passR sp X t S)
    nlinarith
  omega

/-- The label-level vertex set of a set of labels. -/
def lverts (pw : Lab n K → Finset (Fin n) × ZMod K) (P : Finset (Lab n K)) : Finset (Fin n) :=
  P.sup fun x => (pw x).1

omit [NeZero K] in
lemma lverts_insert (pw : Lab n K → Finset (Fin n) × ZMod K) (x : Lab n K)
    (P : Finset (Lab n K)) : lverts pw (insert x P) = (pw x).1 ∪ lverts pw P := by
  simp [lverts, sup_insert]

omit [NeZero K] in
lemma lverts_subset {pw : Lab n K → Finset (Fin n) × ZMod K} {P : Finset (Lab n K)}
    {T : Finset (Fin n)} (h : ∀ x ∈ P, (pw x).1 ⊆ T) : lverts pw P ⊆ T := by
  unfold lverts; exact Finset.sup_le (f := fun x => (pw x).1) (a := T) h

/-- The number of chain pieces on a set. -/
lemma card_chW_le {Λ : Type} [DecidableEq Λ] (cp cn : ℕ → ZMod K → Λ) (item : ℕ → Λ)
    (w : ℕ → ZMod K) (m : ℕ) : (chW cp cn item w m).card ≤ 3 * K * m := by
  unfold chW
  refine (card_union_le _ _).trans ?_
  have h1 := card_biUnion_le_card_mul
    ((Icc 1 m ×ˢ (univ : Finset (ZMod K))).filter (fun p => p.1 = 1 → p.2 = 0))
    (fun p => ({chT cp cn item w p.1 p.2 true, chT cp cn item w p.1 p.2 false} :
      Finset (Finset Λ))) 2 (fun _ _ => card_le_two)
  have h2 := card_filter_le (Icc 1 m ×ˢ (univ : Finset (ZMod K))) (fun p => p.1 = 1 → p.2 = 0)
  have h3 := card_image_le (s := Icc 1 m ×ˢ (univ : Finset (ZMod K)))
    (f := fun p => chQ cp cn p.1 p.2)
  simp only [card_product, Nat.card_Icc, card_univ, ZMod.card, Nat.add_sub_cancel] at h2 h3
  nlinarith

/-- **Piece load of a stage.** -/
lemma stW_loadR (hok : PlanOKR q r L sp X) {t : ℕ} (ht : t < sp.length) (S : Finset (Fin n)) :
    ((stW t (inpR sp X (K := K) q r t) (restFR sp X t)).filter
      (fun P => S ⊆ lverts (pwR sp X) P)).card ≤ 4 * (L + 1) * K ^ 2 * passR sp X t S := by
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (NeZero.ne K)
  have hR := rests_loadR (K := K) hok ht S
  set I := inpR sp X (K := K) q r t
  set rF := restFR sp X t
  have hvis : ∀ ℓ ∈ I, lverts (pwR sp X) (P0 t rF ℓ) ⊆
      visitR (plab ℓ).1 (rtR sp X t (plab ℓ).1) := by
    intro ℓ hℓ
    rw [P0, lverts_insert]
    refine union_subset ?_ ?_
    · simp only [pwR]; rw [(inpR_pair hℓ).2]; exact subset_visitR _ _
    · refine lverts_subset fun x hx => ?_
      obtain ⟨k, hk, rfl⟩ := mem_rests.1 hx
      have hs : (restFR sp X t ℓ).getD k (∅, 0) ∈ restFR sp X t ℓ := by
        rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
      have hs' : ((restFR sp X t ℓ).getD k (∅, 0)).1 ∈
          (rtR sp X t (plab ℓ).1).map Prod.fst := by
        have : ((restFR sp X t ℓ).getD k (∅, 0)).1 ∈ (restFR sp X t ℓ).map Prod.fst :=
          List.mem_map_of_mem hs
        rwa [restFR, map_fst_wroute] at this
      obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hs'
      change ((restFR sp X t ℓ).getD k (∅, 0)).1 ⊆ _
      rw [← hpe]
      exact route_subset_visitR _ hp
  have hvis1 : ∀ ℓ ∈ I, lverts (pwR sp X) (P1 t ℓ) ⊆
      visitR (plab ℓ).1 (rtR sp X t (plab ℓ).1) := by
    intro ℓ hℓ
    rw [P1, lverts_insert]
    simp only [lverts, sup_singleton, pwR]
    rw [(inpR_pair hℓ).2, union_self]
    exact subset_visitR _ _
  have hA : ((I.image (P1 t)).filter (fun P => S ⊆ lverts (pwR sp X) P)).card ≤
      K * passR sp X t S := by
    have hsub : (I.image (P1 t)).filter (fun P => S ⊆ lverts (pwR sp X) P) ⊆
        (I.filter (fun ℓ => S ⊆ visitR (plab ℓ).1 (rtR sp X t (plab ℓ).1))).image (P1 t) := by
      intro P hP
      obtain ⟨hP, hv⟩ := mem_filter.1 hP
      obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hP
      exact mem_image.2 ⟨ℓ, mem_filter.2 ⟨hℓ, hv.trans (hvis1 ℓ hℓ)⟩, rfl⟩
    exact (card_le_card hsub).trans (card_image_le.trans (inp_visit_le t S))
  have hB : ((I.image (P0 t rF)).filter (fun P => S ⊆ lverts (pwR sp X) P)).card ≤
      K * passR sp X t S := by
    have hsub : (I.image (P0 t rF)).filter (fun P => S ⊆ lverts (pwR sp X) P) ⊆
        (I.filter (fun ℓ => S ⊆ visitR (plab ℓ).1 (rtR sp X t (plab ℓ).1))).image (P0 t rF) := by
      intro P hP
      obtain ⟨hP, hv⟩ := mem_filter.1 hP
      obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hP
      exact mem_image.2 ⟨ℓ, mem_filter.2 ⟨hℓ, hv.trans (hvis ℓ hℓ)⟩, rfl⟩
    exact (card_le_card hsub).trans (card_image_le.trans (inp_visit_le t S))
  have hC : (((outs t I rF).biUnion fun e => chW (Lab.cp t e) (Lab.cn t e) (item t I rF e)
      (iw t I rF e) (slen t I rF e)).filter (fun P => S ⊆ lverts (pwR sp X) P)).card ≤
      3 * K * (L * K * passR sp X t S) := by
    have hsub : ((outs t I rF).biUnion fun e => chW (Lab.cp t e) (Lab.cn t e) (item t I rF e)
        (iw t I rF e) (slen t I rF e)).filter (fun P => S ⊆ lverts (pwR sp X) P) ⊆
        ((outs t I rF).filter (S ⊆ ·)).biUnion fun e => chW (Lab.cp t e) (Lab.cn t e)
          (item t I rF e) (iw t I rF e) (slen t I rF e) := by
      intro P hP
      obtain ⟨hP, hv⟩ := mem_filter.1 hP
      obtain ⟨e, he, hPe⟩ := mem_biUnion.1 hP
      refine mem_biUnion.2 ⟨e, mem_filter.2 ⟨he, hv.trans ?_⟩, hPe⟩
      refine lverts_subset fun x hx => ?_
      rcases mem_of_mem_chW hPe hx with ⟨k, s, rfl⟩ | ⟨k, s, rfl⟩ | ⟨k, hk, rfl⟩
      · simp [pwR]
      · simp [pwR]
      · rw [pw_item (stagePWR sp X t) hk]
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    refine (sum_le_sum fun e _ => card_chW_le _ _ _ _ _).trans ?_
    rw [← mul_sum, sum_slen_eq]
    exact Nat.mul_le_mul_left _ hR
  unfold stW
  rw [filter_union, filter_union]
  refine (card_union_le _ _).trans ?_
  have hu := card_union_le ((I.image (P1 t)).filter (fun P => S ⊆ lverts (pwR sp X) P))
    ((I.image (P0 t rF)).filter (fun P => S ⊆ lverts (pwR sp X) P))
  have : K * passR sp X t S + K * passR sp X t S + 3 * K * (L * K * passR sp X t S) ≤
      4 * (L + 1) * K ^ 2 * passR sp X t S := by
    have : K ≤ K ^ 2 := by nlinarith
    have hp := Nat.zero_le (passR sp X t S)
    nlinarith
  omega

end RefinedAbsorption.HyperPlan
