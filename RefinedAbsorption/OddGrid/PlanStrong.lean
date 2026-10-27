module
public import RefinedAbsorption.OddGrid.PlanLoad
public import RefinedAbsorption.Placement.Interface

/-!
# A valid plan gives a strong multi-refiner

`plan_strong`: for a valid plan `sp` on the input graph `X` (at least one stage, at most `M`
final pairs), whose input degrees and total route loads are at most `B` at every vertex, the
lifted labels form a strong `C`-refined multi-refiner with budget `B`, where `C = Cpl K M` depends
only on `K` and `M`.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.Placement

variable {n K : ℕ}

lemma wpairs_card {l : List (Fin n)} (hl : l.IsChain (· ≠ ·)) {f : Finset (Fin n)}
    (hf : f ∈ wpairs l) : f.card = 2 := by
  induction l with
  | nil => simp [wpairs] at hf
  | cons p tl ih =>
    cases tl with
    | nil => simp [wpairs] at hf
    | cons q rest =>
      simp only [wpairs, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact card_pair (List.isChain_cons_cons.1 hl).1
      · exact ih (List.isChain_cons_cons.1 hl).2 hf

lemma route_pairs_card {e : Finset (Fin n)} {r : Route n} (h : RouteOK e r) {f : Finset (Fin n)}
    (hf : f ∈ r.pairs) : f.card = 2 := by
  cases r with
  | walk l =>
    obtain ⟨p, tl, rfl, hch, -⟩ := h
    exact wpairs_card hch (List.mem_toFinset.1 hf)
  | move f' =>
    simp only [Route.pairs, mem_singleton] at hf
    subst hf; exact h

/-- All pairs of a valid plan are `2`-sets. -/
lemma prun_card {sp : List (Spec n)} {X : Finset (Finset (Fin n))} (hok : PlanOK sp X) :
    ∀ t ≤ sp.length, ∀ e ∈ prun sp X t, e.card = 2 := by
  intro t
  induction t with
  | zero => intro _ e he; exact hok.rg e he
  | succ t ih =>
    intro ht e he
    rw [prun_succ, mem_biUnion] at he
    obtain ⟨e', he', hf⟩ := he
    exact route_pairs_card (hok.route t (by omega) e' he') hf

variable [NeZero K] {q : ℕ} {sp : List (Spec n)} {X : Finset (Finset (Fin n))}

/-- Pairs of the labels of a stage. -/
lemma stR_pair {t : ℕ} {x : Lab n K} (hx : x ∈ stR t (inp sp X (K := K) q t) (restFP sp X t)) :
    (pwP sp X x).1 ∈ prun sp X t ∨ (pwP sp X x).1 ∈ prun sp X (t + 1) := by
  simp only [stR, mem_union, mem_image, mem_biUnion] at hx
  rcases hx with (⟨ℓ, hℓ, rfl⟩ | hx) | ⟨e, he, hx⟩
  · left; simp only [pwP]; rw [(inp_pair hℓ).2]; exact (inp_pair hℓ).1
  · obtain ⟨ℓ, hℓ, k, hk, rfl⟩ := mem_restSet.1 hx
    right
    rw [prun_succ, mem_biUnion]
    refine ⟨_, (inp_pair hℓ).1, ?_⟩
    rw [← Route.rest_pairs _ (plab ℓ).2, List.mem_toFinset, List.mem_map]
    refine ⟨(restFP sp X t ℓ).getD k (∅, 0), ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
  · right
    rw [← outs_inp (K := K) q t]
    rcases mem_chR hx with ⟨k, s, rfl⟩ | ⟨k, s, rfl⟩ <;> exact he

/-- All labels of a valid plan lie on `2`-sets. -/
lemma label_card (hok : PlanOK sp X) {x : Lab n K}
    (hx : x ∈ inp sp X (K := K) q 0 ∪ Rall sp X q sp.length) : (pwP sp X x).1.card = 2 := by
  rcases mem_union.1 hx with h | h
  · obtain ⟨e, he, rfl⟩ := mem_inp_zero.1 h; exact hok.rg e he
  · obtain ⟨t, ht, hx⟩ := mem_biUnion.1 h
    have ht := mem_range.1 ht
    rcases stR_pair hx with h1 | h1
    · exact prun_card hok t (by omega) _ h1
    · exact prun_card hok (t + 1) (by omega) _ h1

lemma disjoint_inp_Rall (T : ℕ) : Disjoint (inp sp X (K := K) q 0) (Rall sp X q T) := by
  rw [disjoint_left]
  intro x h1 h2
  obtain ⟨i, -, hi⟩ := stIdx_Rall h2
  rw [stIdx_inp_zero h1] at hi
  exact absurd hi (by simp)

lemma card_inp_succ_le (t : ℕ) :
    (inp sp X (K := K) q (t + 1)).card ≤ K * (prun sp X (t + 1)).card := by
  rw [inp]
  refine card_biUnion_le.trans ?_
  calc _ ≤ ∑ _e ∈ prun sp X (t + 1), K := sum_le_sum fun e _ =>
        card_image_le.trans ((card_le_univ _).trans (by simp))
    _ = _ := by rw [sum_const, smul_eq_mul, mul_comm]

variable (hd : q - 1 ∣ K) (hN : q.choose 2 ∣ K)

include hd hN in
lemma ldiv_Rall (hok : PlanOK sp X) {T : ℕ} (hT : T ≤ sp.length) :
    LDiv q (pwP (K := K) sp X) (Rall sp X q T) := by
  induction T with
  | zero => simp only [Rall, range_zero, biUnion_empty]; exact ldiv_empty
  | succ T ih =>
    have hR : Rall (K := K) sp X q (T + 1) =
        Rall sp X q T ∪ stR T (inp sp X q T) (restFP sp X T) := by
      simp [Rall, range_add_one, biUnion_insert, union_comm]
    rw [hR]
    refine ldiv_union ?_ (ih (by omega)) (ldiv_stR hd hN (stagePW sp X T)
      (fun _ h => notStage_inp h) (fun _ h => plan_P0 hd hN hok (by omega) h))
    rw [disjoint_left]
    intro x h1 h2
    obtain ⟨i, hi, h3⟩ := stIdx_Rall h1
    rw [stIdx_of_stR h2] at h3
    simp only [Option.some.injEq] at h3; omega

include hd hN in
lemma ldiv_pieces (hok : PlanOK sp X) {P : Finset (Lab n K)}
    (hP : P ∈ Wall sp X q sp.length ∪ Wbase sp X q) : LDiv q (pwP sp X) P := by
  classical
  rcases mem_union.1 hP with h | h
  · obtain ⟨t, ht, hP⟩ := mem_biUnion.1 h
    exact ldiv_stW hd hN (stagePW sp X t)
      (fun _ h => plan_P0 hd hN hok (mem_range.1 ht) h) hP
  · unfold Wbase at h
    exact (mem_filter.1 h).2

lemma pieces_subset {P : Finset (Lab n K)} (hP : P ∈ Wall sp X q sp.length ∪ Wbase sp X q) :
    P ⊆ inp sp X q 0 ∪ Rall sp X q sp.length := by
  rcases mem_union.1 hP with h | h
  · exact Wall_subset h
  · exact (mem_powerset.1 (Wbase_subset_powerset h)).trans (inp_subset_Rall le_rfl)

/-- Pieces of a valid plan have at most `4` labels, or are base pieces. -/
lemma card_pieces_le (hok : PlanOK sp X) {P : Finset (Lab n K)}
    (hP : P ∈ Wall sp X q sp.length ∪ Wbase sp X q) :
    P.card ≤ 4 + (inp sp X (K := K) q sp.length).card := by
  rcases mem_union.1 hP with h | h
  · obtain ⟨t, ht, hP⟩ := mem_biUnion.1 h
    have ht := mem_range.1 ht
    simp only [stW, mem_union, mem_image, mem_biUnion] at hP
    rcases hP with (⟨ℓ, -, rfl⟩ | ⟨ℓ, hℓ, rfl⟩) | ⟨e, -, hP⟩
    · exact (card_insert_le _ _).trans (by rw [card_singleton]; omega)
    · refine (card_insert_le _ _).trans ?_
      rw [rests, card_image_of_injective _ (fun a b h => by simpa using h), card_range]
      have := length_rest_le (hok.route t ht _ (inp_pair hℓ).1) (plab ℓ).2
      change ((rt sp X t (plab ℓ).1).rest (plab ℓ).2).length + 1 ≤ _
      omega
    · simp only [chW, mem_union, mem_biUnion, mem_filter, mem_product, mem_univ, and_true,
        mem_insert, mem_singleton, mem_image] at hP
      rcases hP with ⟨⟨k, s⟩, -, rfl | rfl⟩ | ⟨⟨k, s⟩, -, rfl⟩
      · simp only [chT, if_true]
        refine (card_insert_le _ _).trans ?_
        have := card_insert_le (item t (inp sp X q t) (restFP sp X t) e k)
          {Lab.cn t e k (s + iw t (inp sp X q t) (restFP sp X t) e k)}
        rw [card_singleton] at this
        omega
      · simp only [chT, Bool.false_eq_true, if_false]
        exact (card_insert_le _ _).trans (by rw [card_singleton]; omega)
      · exact (card_insert_le _ _).trans (by rw [card_singleton]; omega)
  · exact (card_le_card (mem_powerset.1 (Wbase_subset_powerset h))).trans (by omega)

/-- The constant of a plan. -/
def Cpl (K M : ℕ) : ℕ := 14 * K ^ 3 * (K * M + 4 + (2 * (K + 10) + 2 ^ (K * M)))

lemma Cpl_ge (K M : ℕ) (hK : 1 ≤ K) :
    K * (K * M + 4) ≤ Cpl K M ∧ 2 * (K + 10) + 2 ^ (K * M) ≤ Cpl K M ∧
      K * (14 * K ^ 2) ≤ Cpl K M ∧ 14 * K ^ 2 * (2 * (K + 10) + 2 ^ (K * M)) ≤ Cpl K M := by
  have h1 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ hK
  have hK3 : K ≤ K ^ 3 := by nlinarith [Nat.pow_le_pow_right hK (show 1 ≤ 3 by norm_num)]
  have hK2 : K ^ 2 ≤ K ^ 3 := Nat.pow_le_pow_right hK (by norm_num)
  set A := K * M + 4
  set Cm := 2 * (K + 10) + 2 ^ (K * M)
  set S := A + Cm
  have hS : 1 ≤ S := (show 1 ≤ A by simp only [A]; omega).trans (Nat.le_add_right A Cm)
  have hKS : K ^ 3 * S ≤ 14 * K ^ 3 * S := by
    rw [mul_assoc 14]; exact Nat.le_mul_of_pos_left _ (by norm_num)
  unfold Cpl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Nat.mul_le_mul hK3 (Nat.le_add_right A Cm)).trans hKS
  · exact (Nat.le_add_left Cm A).trans ((Nat.le_mul_of_pos_left S h1).trans hKS)
  · calc K * (14 * K ^ 2) = 14 * K ^ 3 * 1 := by ring
      _ ≤ 14 * K ^ 3 * S := Nat.mul_le_mul_left _ hS
  · calc 14 * K ^ 2 * Cm ≤ 14 * K ^ 3 * S :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 14 hK2) (Nat.le_add_left _ _)

variable (hK1 : 1 < K)

include hd hN hK1 in
/-- **A valid plan gives a strong multi-refiner.** -/
theorem plan_strong (hok : PlanOK sp X) (hT : 1 ≤ sp.length) {M B : ℕ}
    (hM : (prun sp X sp.length).card ≤ M)
    (hX : ∀ v, (X.filter (v ∈ ·)).card ≤ B)
    (hP : ∀ v, ∑ t ∈ range sp.length, pass sp X t v ≤ B) :
    (liftS (wsg (pwP sp X)) (inp sp X (K := K) q 0)).image (cpEnds (wsg (pwP sp X))) = X ∧
    IsStrongMultiRefiner q 2 (Cpl K M) (cpEnds (wsg (pwP (K := K) sp X)))
      (liftS (wsg (pwP sp X)) (inp sp X q 0)) (liftS (wsg (pwP sp X)) (inp sp X q 0))
      (liftS (wsg (pwP sp X)) (Rall sp X q sp.length))
      ((Wall sp X q sp.length ∪ Wbase sp X q).image (liftS (wsg (pwP sp X)))) B := by
  haveI : Fact (1 < K) := ⟨hK1⟩
  have hK : 1 ≤ K := hK1.le
  obtain ⟨hC1, hC2, hC3, hC4⟩ := Cpl_ge K M hK
  set pw := pwP (K := K) sp X with hpw
  set sg := wsg pw with hsg
  set I0 := inp sp X (K := K) q 0 with hI0def
  set R := Rall sp X (K := K) q sp.length with hRdef
  set Wl := Wall sp X (K := K) q sp.length ∪ Wbase sp X q with hWl
  have hInp : (inp sp X (K := K) q sp.length).card ≤ K * M := by
    obtain ⟨T', hT'⟩ : ∃ T', sp.length = T' + 1 := ⟨sp.length - 1, by omega⟩
    rw [hT'] at hM ⊢
    exact (card_inp_succ_le T').trans (Nat.mul_le_mul_left _ hM)
  set Cm := 2 * (K + 10) + 2 ^ (K * M) with hCm
  have hmult : ∀ x, (Wl.filter (x ∈ ·)).card ≤ Cm := fun x =>
    (plan_mult x).trans (Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) hInp) _)
  have hval : ∀ ℓ, wdeg sg ℓ ∅ ≤ K := by
    intro ℓ; rw [wdeg_wsg, if_pos (empty_subset _)]; exact (ZMod.val_lt _).le
  have htouch : ∀ v ℓ, touch sg v ℓ = true ↔ v ∈ (pw ℓ).1 := by
    intro v ℓ; simp [touch, sg, wsg]
  have hI0 : ∀ ℓ ∈ I0, sg ℓ = [((pw ℓ).1, 1)] := by
    intro ℓ hℓ
    obtain ⟨e, -, rfl⟩ := mem_inp_zero.1 hℓ
    simp [sg, wsg, pw, pwP, ZMod.val_one]
  have hends : ∀ c ∈ liftS sg (I0 ∪ R), cpEnds sg c = (pw c.1).1 := by
    intro c hc
    have h1 := (mem_liftS.1 hc).2.1
    simp only [sg, wsg, List.length_singleton, Nat.lt_one_iff] at h1
    simp [cpEnds, segAt, sg, wsg, h1]
  have hload : ∀ v, ((I0 ∪ R).filter (fun x => v ∈ (pw x).1)).card ≤ 14 * K ^ 2 * B := fun v =>
    (plan_load hok hT v).trans (Nat.mul_le_mul_left _ (hP v))
  -- the refiner
  have href : IsMultiRefiner q 2 (Cpl K M) (cpEnds sg) (liftS sg I0) (liftS sg R)
      (Wl.image (liftS sg)) := by
    have h := lift_residual (q := q) (C := Cpl K M) sg (fun ℓ => (pw ℓ).1) (I := I0) (Rl := R)
      (Yl := ∅) (Wl := Wl) hI0 ?_ (disjoint_inp_Rall _) (fun P hP => ldiv_pieces hd hN hok hP)
      (fun P hP => pieces_subset hP) ?_ (fun ℓ => (hmult ℓ).trans hC2)
      (ldiv_Rall hd hN hok le_rfl) ?_
    · rwa [liftS_empty] at h
    · intro ℓ hℓ s hs
      simp only [sg, wsg, List.mem_singleton] at hs
      subst hs
      exact label_card hok hℓ
    · intro P hP
      rw [card_liftS]
      calc ∑ ℓ ∈ P, wdeg sg ℓ ∅ ≤ ∑ _ℓ ∈ P, K := sum_le_sum fun ℓ _ => hval ℓ
        _ = P.card * K := by rw [sum_const, smul_eq_mul]
        _ ≤ (K * M + 4) * K := Nat.mul_le_mul_right _
            ((card_pieces_le hok hP).trans (by omega))
        _ ≤ Cpl K M := by rw [mul_comm]; exact hC1
    · intro Ls hLs hdiv
      obtain ⟨𝒰, h𝒰, Res, hRes, -, hpd, hdj, heq⟩ := plan_ldecomp hd hN hok Ls hLs hdiv
      exact ⟨𝒰, h𝒰, Res, hRes, hpd, hdj, heq⟩
  have hcopy : ∀ c, c ∈ liftS sg I0 ↔ c.1 ∈ I0 ∧ c.2.1 = 0 ∧ c.2.2 = 0 := fun c =>
    liftS_single hI0
  refine ⟨?_, href, subset_refl _, ?_, ?_, ?_, ?_, ?_⟩
  · -- the kept copies cover `X`
    ext e
    simp only [mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [hends c (liftS_mono subset_union_left hc)]
      obtain ⟨h1, -, -⟩ := (hcopy c).1 hc
      obtain ⟨e', he', h⟩ := mem_inp_zero.1 h1
      rw [h]; exact he'
    · intro he
      refine ⟨(Lab.x e, 0, 0), (hcopy _).2 ⟨mem_inp_zero.2 ⟨e, he, rfl⟩, rfl, rfl⟩, ?_⟩
      rw [hends _ (liftS_mono subset_union_left
        ((hcopy _).2 ⟨mem_inp_zero.2 ⟨e, he, rfl⟩, rfl, rfl⟩))]
      rfl
  · -- injectivity on the kept copies
    intro a ha b hb hab
    have ha' := (hcopy a).1 ha
    have hb' := (hcopy b).1 hb
    rw [hends a (liftS_mono subset_union_left ha), hends b (liftS_mono subset_union_left hb)]
      at hab
    obtain ⟨e, -, he⟩ := mem_inp_zero.1 ha'.1
    obtain ⟨e', -, he'⟩ := mem_inp_zero.1 hb'.1
    obtain ⟨a1, a2, a3⟩ := a
    obtain ⟨b1, b2, b3⟩ := b
    simp only at ha' hb' he he' hab ⊢
    subst he he'
    simp only [pw, pwP] at hab
    rw [ha'.2.1, ha'.2.2, hb'.2.1, hb'.2.2, hab]
  · -- each piece contains at most one kept copy
    intro W hW
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    have hPx : ∀ a ∈ P, a ∈ I0 → ∀ b ∈ P, b ∈ I0 → a = b := by
      intro a ha haI b hb hbI
      obtain ⟨e, -, rfl⟩ := mem_inp_zero.1 haI
      obtain ⟨e', -, rfl⟩ := mem_inp_zero.1 hbI
      rcases mem_union.1 hP with h | h
      · obtain ⟨t, -, hPt⟩ := mem_biUnion.1 h
        simp only [stW, mem_union, mem_image, mem_biUnion] at hPt
        rcases hPt with (⟨ℓ, -, rfl⟩ | ⟨ℓ, -, rfl⟩) | ⟨f, -, hPf⟩
        · simp only [P1, mem_insert, mem_singleton] at ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · rw [ha, hb]
          · exact absurd hb (by simp)
          · exact absurd ha (by simp)
          · exact absurd ha (by simp)
        · simp only [P0, mem_insert] at ha
          rcases ha with ha | ha
          · exact absurd ha (by simp)
          · obtain ⟨k, -, hk⟩ := mem_rests.1 ha; exact absurd hk (by simp)
        · rcases mem_of_mem_chW hPf ha with ⟨k, s, hk⟩ | ⟨k, s, hk⟩ | ⟨k, hk, hk'⟩
          · exact absurd hk (by simp)
          · exact absurd hk (by simp)
          · obtain ⟨ℓ, -, j, -, hj⟩ := item_isRest hk
            rw [hj] at hk'; exact absurd hk' (by simp)
      · have := pieces_subset hP
        have h1 := mem_powerset.1 (Wbase_subset_powerset h) ha
        obtain ⟨T', hT'⟩ : ∃ T', sp.length = T' + 1 := ⟨sp.length - 1, by omega⟩
        rw [hT'] at h1
        obtain ⟨f, -, s, -, hf⟩ := mem_inp_succ.1 h1
        exact absurd hf (by simp)
    refine card_le_one.2 fun a ha b hb => ?_
    obtain ⟨ha1, ha2⟩ := mem_filter.1 ha
    obtain ⟨hb1, hb2⟩ := mem_filter.1 hb
    have ha' := (hcopy a).1 ha2
    have hb' := (hcopy b).1 hb2
    have := hPx _ (mem_liftS.1 ha1).1 ha'.1 _ (mem_liftS.1 hb1).1 hb'.1
    obtain ⟨a1, a2, a3⟩ := a
    obtain ⟨b1, b2, b3⟩ := b
    simp only at ha' hb' this
    rw [ha'.2.1, ha'.2.2, hb'.2.1, hb'.2.2, this]
  · -- degree of `X`
    intro S hS
    obtain ⟨v, rfl⟩ := card_eq_one.1 (by simpa using hS)
    refine (mdeg_liftS_le I0 v 1 ?_).trans ?_
    · intro ℓ hℓ
      obtain ⟨e, -, rfl⟩ := mem_inp_zero.1 hℓ
      rw [wdeg_wsg, if_pos (empty_subset _)]
      simp [pw, pwP, ZMod.val_one]
    · rw [one_mul]
      refine le_trans ?_ (hX v)
      have hsub : I0.filter (touch sg v ·) ⊆ (X.filter (v ∈ ·)).image Lab.x := by
        intro ℓ hℓ
        obtain ⟨hℓ, ht⟩ := mem_filter.1 hℓ
        obtain ⟨e, he, rfl⟩ := mem_inp_zero.1 hℓ
        rw [htouch] at ht
        exact mem_image.2 ⟨e, mem_filter.2 ⟨he, ht⟩, rfl⟩
      exact (card_le_card hsub).trans card_image_le
  · -- degree of the reservoir
    intro S hS
    obtain ⟨v, rfl⟩ := card_eq_one.1 (by simpa using hS)
    refine (mdeg_liftS_le R v K fun ℓ _ => hval ℓ).trans ?_
    have h1 : (R.filter (touch sg v ·)).card ≤ 14 * K ^ 2 * B := by
      refine le_trans (card_le_card fun x hx => ?_) (hload v)
      obtain ⟨hx, ht⟩ := mem_filter.1 hx
      exact mem_filter.2 ⟨mem_union_right _ hx, (htouch v x).1 ht⟩
    calc K * (R.filter (touch sg v ·)).card ≤ K * (14 * K ^ 2 * B) := Nat.mul_le_mul_left _ h1
      _ = K * (14 * K ^ 2) * B := by ring
      _ ≤ Cpl K M * B := Nat.mul_le_mul_right _ hC3
  · -- pieces through a vertex
    intro S hS
    obtain ⟨v, rfl⟩ := card_eq_one.1 (by simpa using hS)
    set L := (I0 ∪ R).filter (fun x => v ∈ (pw x).1)
    have hsub : (Wl.image (liftS sg)).filter (fun W => {v} ⊆ W.biUnion (cpEnds sg)) ⊆
        (L.biUnion fun x => Wl.filter (x ∈ ·)).image (liftS sg) := by
      intro W hW
      obtain ⟨hW, hv⟩ := mem_filter.1 hW
      obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
      rw [singleton_subset_iff, mem_biUnion] at hv
      obtain ⟨c, hc, hvc⟩ := hv
      have hc1 := (mem_liftS.1 hc).1
      have hcR : c ∈ liftS sg (I0 ∪ R) := liftS_mono (pieces_subset hP) hc
      rw [hends c hcR] at hvc
      refine mem_image.2 ⟨P, mem_biUnion.2 ⟨c.1, mem_filter.2 ⟨pieces_subset hP hc1, hvc⟩,
        mem_filter.2 ⟨hP, hc1⟩⟩, rfl⟩
    refine (card_le_card hsub).trans (card_image_le.trans (card_biUnion_le.trans ?_))
    calc ∑ x ∈ L, (Wl.filter (x ∈ ·)).card ≤ ∑ _x ∈ L, Cm := sum_le_sum fun x _ => hmult x
      _ = L.card * Cm := by rw [sum_const, smul_eq_mul]
      _ ≤ (14 * K ^ 2 * B) * Cm := Nat.mul_le_mul_right _ (hload v)
      _ = 14 * K ^ 2 * Cm * B := by ring
      _ ≤ Cpl K M * B := Nat.mul_le_mul_right _ hC4

end RefinedAbsorption.OddGrid
