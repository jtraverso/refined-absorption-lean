module
public import RequestProject.HyperPlan.Load
public import RequestProject.HyperPlan.Lift
public import RequestProject.OddGrid.PlanStrong

/-!
# A valid plan gives a strong multi-refiner, uniformity `r`

`plan_strongR`: for a valid plan `sp` on the `r`-graph `X` (at least one stage, at most `M` final
sets, routes of length at most `L`), whose input `(r-1)`-degrees and total route loads
`Σ_t passR sp X t S` are at most `B` at every `(r - 1)`-set `S` (with `1 ≤ B`), the lifted labels
form a strong `C`-refined multi-refiner with budget `B`, where `C = CplR K M L` depends only on
`K`, `M` and `L`.

This is the `r`-uniform version of `OddGrid.plan_strong`; the vertex loads of `r = 2` are
replaced by loads at `(r - 1)`-sets, and the piece loads are counted through the vertex sets of
the pieces (`stW_loadR`).
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid RefinedAbsorption.Placement

variable {n K : ℕ} [NeZero K] {q r L : ℕ} {sp : List (SpecR n K)} {X : Finset (Finset (Fin n))}

/-- All sets of a valid plan are `r`-sets. -/
lemma prunR_card (hok : PlanOKR q r L sp X) :
    ∀ t ≤ sp.length, ∀ e ∈ prunR sp X t, e.card = r := by
  intro t
  induction t with
  | zero => intro _ e he; exact hok.rg e he
  | succ t ih =>
    intro ht e he
    rw [prunR_succ, mem_biUnion] at he
    obtain ⟨e', he', hf⟩ := he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hf)
    exact (hok.route t (by omega) e' he').1 p hp

/-- Sets of the labels of a stage. -/
lemma stR_pairR {t : ℕ} {x : Lab n K}
    (hx : x ∈ stR t (inpR sp X (K := K) q r t) (restFR sp X t)) :
    (pwR sp X x).1 ∈ prunR sp X t ∨ (pwR sp X x).1 ∈ prunR sp X (t + 1) := by
  simp only [stR, mem_union, mem_image, mem_biUnion] at hx
  rcases hx with (⟨ℓ, hℓ, rfl⟩ | hx) | ⟨e, he, hx⟩
  · left; simp only [pwR]; rw [(inpR_pair hℓ).2]; exact (inpR_pair hℓ).1
  · obtain ⟨ℓ, hℓ, k, hk, rfl⟩ := mem_restSet.1 hx
    right
    rw [prunR_succ, mem_biUnion]
    refine ⟨_, (inpR_pair hℓ).1, ?_⟩
    rw [List.mem_toFinset, ← map_fst_wroute _ (plab ℓ).2, List.mem_map]
    refine ⟨(restFR sp X t ℓ).getD k (∅, 0), ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
  · right
    rw [← outs_inpR (K := K) q r t]
    rcases mem_chR hx with ⟨k, s, rfl⟩ | ⟨k, s, rfl⟩ <;> exact he

/-- All labels of a valid plan lie on `r`-sets. -/
lemma label_cardR (hok : PlanOKR q r L sp X) {x : Lab n K}
    (hx : x ∈ inpR sp X (K := K) q r 0 ∪ RallR sp X q r sp.length) :
    (pwR sp X x).1.card = r := by
  rcases mem_union.1 hx with h | h
  · obtain ⟨e, he, rfl⟩ := mem_inpR_zero.1 h; exact hok.rg e he
  · obtain ⟨t, ht, hx⟩ := mem_biUnion.1 h
    have ht := mem_range.1 ht
    rcases stR_pairR hx with h1 | h1
    · exact prunR_card hok t (by omega) _ h1
    · exact prunR_card hok (t + 1) (by omega) _ h1

lemma disjoint_inpR_RallR (T : ℕ) : Disjoint (inpR sp X (K := K) q r 0) (RallR sp X q r T) := by
  rw [disjoint_left]
  intro x h1 h2
  obtain ⟨i, -, hi⟩ := stIdx_RallR h2
  rw [stIdx_inpR_zero h1] at hi
  exact absurd hi (by simp)

lemma card_inpR_succ_le (t : ℕ) :
    (inpR sp X (K := K) q r (t + 1)).card ≤ K * (prunR sp X (t + 1)).card := by
  rw [inpR]
  refine card_biUnion_le.trans ?_
  calc _ ≤ ∑ _e ∈ prunR sp X (t + 1), K := sum_le_sum fun e _ =>
        card_image_le.trans ((card_le_univ _).trans (by simp))
    _ = _ := by rw [sum_const, smul_eq_mul, mul_comm]

variable (hK : ModsOK q r K)

include hK in
lemma ldivR_RallR (hok : PlanOKR q r L sp X) {T : ℕ} (hT : T ≤ sp.length) :
    LDivR q r (pwR (K := K) sp X) (RallR sp X q r T) := by
  induction T with
  | zero => simp only [RallR, range_zero, biUnion_empty]; exact ldivR_empty
  | succ T ih =>
    have hR : RallR (K := K) sp X q r (T + 1) =
        RallR sp X q r T ∪ stR T (inpR sp X q r T) (restFR sp X T) := by
      simp [RallR, range_add_one, biUnion_insert, union_comm]
    rw [hR]
    refine ldivR_union ?_ (ih (by omega)) (ldivR_stR hK (stagePWR sp X T)
      (fun _ h => notStage_inpR h) (fun _ h => plan_P0R hK hok (by omega) h))
    rw [disjoint_left]
    intro x h1 h2
    obtain ⟨i, hi, h3⟩ := stIdx_RallR h1
    rw [stIdx_of_stR h2] at h3
    simp only [Option.some.injEq] at h3; omega

include hK in
lemma ldivR_pieces (hok : PlanOKR q r L sp X) {P : Finset (Lab n K)}
    (hP : P ∈ WallR sp X q r sp.length ∪ WbaseR sp X q r) : LDivR q r (pwR sp X) P := by
  classical
  rcases mem_union.1 hP with h | h
  · obtain ⟨t, ht, hP⟩ := mem_biUnion.1 h
    exact ldivR_stW hK (stagePWR sp X t)
      (fun _ h => plan_P0R hK hok (mem_range.1 ht) h) hP
  · unfold WbaseR at h
    exact (mem_filter.1 h).2

open Classical in
lemma WbaseR_subset_powerset : WbaseR (K := K) sp X q r ⊆ (inpR sp X q r sp.length).powerset :=
  filter_subset _ _

lemma pieces_subsetR {P : Finset (Lab n K)}
    (hP : P ∈ WallR sp X q r sp.length ∪ WbaseR sp X q r) :
    P ⊆ inpR sp X q r 0 ∪ RallR sp X q r sp.length := by
  rcases mem_union.1 hP with h | h
  · exact WallR_subset h
  · exact (mem_powerset.1 (WbaseR_subset_powerset h)).trans (inpR_subset_RallR le_rfl)

/-- Pieces of a valid plan have at most `L + 3` labels, or are base pieces. -/
lemma card_pieces_leR (hok : PlanOKR q r L sp X) {P : Finset (Lab n K)}
    (hP : P ∈ WallR sp X q r sp.length ∪ WbaseR sp X q r) :
    P.card ≤ L + 3 + (inpR sp X (K := K) q r sp.length).card := by
  rcases mem_union.1 hP with h | h
  · obtain ⟨t, ht, hP⟩ := mem_biUnion.1 h
    have ht := mem_range.1 ht
    simp only [stW, mem_union, mem_image, mem_biUnion] at hP
    rcases hP with (⟨ℓ, -, rfl⟩ | ⟨ℓ, hℓ, rfl⟩) | ⟨e, -, hP⟩
    · exact (card_insert_le _ _).trans (by rw [card_singleton]; omega)
    · refine (card_insert_le _ _).trans ?_
      rw [rests, card_image_of_injective _ (fun a b h => by simpa using h), card_range]
      have := hok.len t ht _ (inpR_pair hℓ).1
      change (wroute _ _).length + 1 ≤ _
      simp only [wroute, List.length_map]
      omega
    · simp only [chW, mem_union, mem_biUnion, mem_filter, mem_product, mem_univ, and_true,
        mem_insert, mem_singleton, mem_image] at hP
      rcases hP with ⟨⟨k, s⟩, -, rfl | rfl⟩ | ⟨⟨k, s⟩, -, rfl⟩
      · simp only [chT, if_true]
        refine (card_insert_le _ _).trans ?_
        have := card_insert_le (item t (inpR sp X q r t) (restFR sp X t) e k)
          {Lab.cn t e k (s + iw t (inpR sp X q r t) (restFR sp X t) e k)}
        rw [card_singleton] at this
        omega
      · simp only [chT, Bool.false_eq_true, if_false]
        exact (card_insert_le _ _).trans (by rw [card_singleton]; omega)
      · exact (card_insert_le _ _).trans (by rw [card_singleton]; omega)
  · exact (card_le_card (mem_powerset.1 (WbaseR_subset_powerset h))).trans (by omega)

lemma stage_of_mem_stWR {i : ℕ} {P : Finset (Lab n K)}
    (hP : P ∈ stW i (inpR sp X (K := K) q r i) (restFR sp X i)) {x : Lab n K} (hx : x ∈ P) :
    i ∈ stCand (stIdx x) := by
  rcases mem_union.1 (stW_subset hP hx) with h | h
  · cases i with
    | zero => rw [stIdx_inpR_zero h]; simp [stCand]
    | succ j => obtain ⟨e, -, s, -, rfl⟩ := mem_inpR_succ.1 h; simp [stIdx, stCand]
  · rw [stIdx_of_stR h]; simp [stCand]

/-- **Multiplicity in a plan with its base pieces.** -/
lemma plan_multR (x : Lab n K) :
    ((WallR sp X q r sp.length ∪ WbaseR sp X q r).filter (x ∈ ·)).card ≤
      2 * (K + 10) + 2 ^ (inpR sp X (K := K) q r sp.length).card := by
  rw [filter_union]
  refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · have hsub : (WallR sp X q r sp.length).filter (x ∈ ·) ⊆ (stCand (stIdx x)).biUnion
        (fun i => (stW i (inpR sp X q r i) (restFR sp X i)).filter (x ∈ ·)) := by
      intro P hP
      obtain ⟨hP, hx⟩ := mem_filter.1 hP
      obtain ⟨i, -, hP⟩ := mem_biUnion.1 hP
      exact mem_biUnion.2 ⟨i, stage_of_mem_stWR hP hx, mem_filter.2 ⟨hP, hx⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc _ ≤ ∑ _i ∈ stCand (stIdx x), (K + 10) := sum_le_sum fun i _ => stW_mult _ _ _ _
      _ = (stCand (stIdx x)).card * (K + 10) := by rw [sum_const, smul_eq_mul]
      _ ≤ 2 * (K + 10) := Nat.mul_le_mul_right _ (card_stCand_le _)
  · refine (card_le_card (filter_subset _ _)).trans ?_
    exact (card_le_card WbaseR_subset_powerset).trans (card_powerset _).le

/-- **Label load of a plan.** -/
lemma plan_loadR (hok : PlanOKR q r L sp X) (S : Finset (Fin n)) :
    ((RallR sp X (K := K) q r sp.length).filter (fun x => S ⊆ (pwR sp X x).1)).card ≤
      4 * (L + 1) * K ^ 2 * ∑ t ∈ range sp.length, passR sp X t S := by
  rw [RallR, filter_biUnion, mul_sum]
  exact card_biUnion_le.trans (sum_le_sum fun t ht => stR_loadR hok (mem_range.1 ht) S)

/-- **Piece load of a plan.** -/
lemma plan_pieceLoadR (hok : PlanOKR q r L sp X) (S : Finset (Fin n)) :
    ((WallR sp X (K := K) q r sp.length ∪ WbaseR sp X q r).filter
      (fun P => S ⊆ lverts (pwR sp X) P)).card ≤
      4 * (L + 1) * K ^ 2 * (∑ t ∈ range sp.length, passR sp X t S) +
        2 ^ (inpR sp X (K := K) q r sp.length).card := by
  rw [filter_union]
  refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · rw [WallR, filter_biUnion, mul_sum]
    exact card_biUnion_le.trans (sum_le_sum fun t ht => stW_loadR hok (mem_range.1 ht) S)
  · exact (card_le_card (filter_subset _ _)).trans
      ((card_le_card WbaseR_subset_powerset).trans (card_powerset _).le)

/-- The constant of an `r`-uniform plan. -/
def CplR (K M L : ℕ) : ℕ := 4 * (L + 1) * K ^ 3 + K * (L + 3 + K * M) + 2 * (K + 10) + 2 ^ (K * M)

variable (hK1 : 1 < K)

include hK hK1 in
/-- **A valid `r`-uniform plan gives a strong multi-refiner.** -/
theorem plan_strongR (hok : PlanOKR q r L sp X) (hT : 1 ≤ sp.length) {M B : ℕ}
    (hM : (prunR sp X sp.length).card ≤ M) (hB : 1 ≤ B)
    (hX : ∀ S : Finset (Fin n), S.card = r - 1 → (X.filter (S ⊆ ·)).card ≤ B)
    (hP : ∀ S : Finset (Fin n), S.card = r - 1 → ∑ t ∈ range sp.length, passR sp X t S ≤ B) :
    (liftS (wsg (pwR sp X)) (inpR sp X (K := K) q r 0)).image (cpEnds (wsg (pwR sp X))) = X ∧
    IsStrongMultiRefiner q r (CplR K M L) (cpEnds (wsg (pwR (K := K) sp X)))
      (liftS (wsg (pwR sp X)) (inpR sp X q r 0)) (liftS (wsg (pwR sp X)) (inpR sp X q r 0))
      (liftS (wsg (pwR sp X)) (RallR sp X q r sp.length))
      ((WallR sp X q r sp.length ∪ WbaseR sp X q r).image (liftS (wsg (pwR sp X)))) B := by
  haveI : Fact (1 < K) := ⟨hK1⟩
  have hK' : 1 ≤ K := hK1.le
  set pw := pwR (K := K) sp X with hpw
  set sg := wsg pw with hsg
  set I0 := inpR sp X (K := K) q r 0 with hI0def
  set R := RallR sp X (K := K) q r sp.length with hRdef
  set Wl := WallR sp X (K := K) q r sp.length ∪ WbaseR sp X q r with hWl
  have hInp : (inpR sp X (K := K) q r sp.length).card ≤ K * M := by
    obtain ⟨T', hT'⟩ : ∃ T', sp.length = T' + 1 := ⟨sp.length - 1, by omega⟩
    rw [hT'] at hM ⊢
    exact (card_inpR_succ_le T').trans (Nat.mul_le_mul_left _ hM)
  have h2pow : 2 ^ (inpR sp X (K := K) q r sp.length).card ≤ 2 ^ (K * M) :=
    Nat.pow_le_pow_right (by norm_num) hInp
  have hmult : ∀ x, (Wl.filter (x ∈ ·)).card ≤ 2 * (K + 10) + 2 ^ (K * M) := fun x =>
    (plan_multR x).trans (Nat.add_le_add_left h2pow _)
  have hval : ∀ ℓ, wdeg sg ℓ ∅ ≤ K := by
    intro ℓ; rw [wdeg_wsg, if_pos (empty_subset _)]; exact (ZMod.val_lt _).le
  have hI0 : ∀ ℓ ∈ I0, sg ℓ = [((pw ℓ).1, 1)] := by
    intro ℓ hℓ
    obtain ⟨e, -, rfl⟩ := mem_inpR_zero.1 hℓ
    simp [sg, wsg, pw, pwR, ZMod.val_one]
  have hends : ∀ c ∈ liftS sg (I0 ∪ R), cpEnds sg c = (pw c.1).1 := by
    intro c hc
    have h1 := (mem_liftS.1 hc).2.1
    simp only [sg, wsg, List.length_singleton, Nat.lt_one_iff] at h1
    simp [cpEnds, segAt, sg, wsg, h1]
  have hCdef : CplR K M L = 4 * (L + 1) * K ^ 3 + K * (L + 3 + K * M) + 2 * (K + 10) +
      2 ^ (K * M) := rfl
  -- the refiner
  have href : IsMultiRefiner q r (CplR K M L) (cpEnds sg) (liftS sg I0) (liftS sg R)
      (Wl.image (liftS sg)) := by
    have h := lift_residualR (q := q) (r := r) (C := CplR K M L) sg (fun ℓ => (pw ℓ).1)
      (I := I0) (Rl := R) (Yl := ∅) (Wl := Wl) hI0 ?_ (disjoint_inpR_RallR _)
      (fun P hP => ldivR_pieces hK hok hP) (fun P hP => pieces_subsetR hP) ?_
      (fun ℓ => (hmult ℓ).trans (by rw [hCdef]; omega))
      (ldivR_RallR hK hok le_rfl) ?_
    · rwa [liftS_empty] at h
    · intro ℓ hℓ s hs
      simp only [sg, wsg, List.mem_singleton] at hs
      subst hs
      exact label_cardR hok hℓ
    · intro P hP
      rw [card_liftS]
      calc ∑ ℓ ∈ P, wdeg sg ℓ ∅ ≤ ∑ _ℓ ∈ P, K := sum_le_sum fun ℓ _ => hval ℓ
        _ = P.card * K := by rw [sum_const, smul_eq_mul]
        _ ≤ (L + 3 + K * M) * K := Nat.mul_le_mul_right _
            ((card_pieces_leR hok hP).trans (by omega))
        _ ≤ CplR K M L := by
            unfold CplR; nlinarith [Nat.zero_le (4 * (L + 1) * K ^ 3), Nat.zero_le (2 ^ (K * M))]
    · intro Ls hLs hdiv
      obtain ⟨𝒰, h𝒰, Res, hRes, -, hpd, hdj, heq⟩ := plan_ldecompR hK hok Ls hLs hdiv
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
      obtain ⟨e', he', h⟩ := mem_inpR_zero.1 h1
      rw [h]; exact he'
    · intro he
      refine ⟨(Lab.x e, 0, 0), (hcopy _).2 ⟨mem_inpR_zero.2 ⟨e, he, rfl⟩, rfl, rfl⟩, ?_⟩
      rw [hends _ (liftS_mono subset_union_left
        ((hcopy _).2 ⟨mem_inpR_zero.2 ⟨e, he, rfl⟩, rfl, rfl⟩))]
      rfl
  · -- injectivity on the kept copies
    intro a ha b hb hab
    have ha' := (hcopy a).1 ha
    have hb' := (hcopy b).1 hb
    rw [hends a (liftS_mono subset_union_left ha), hends b (liftS_mono subset_union_left hb)]
      at hab
    obtain ⟨e, -, he⟩ := mem_inpR_zero.1 ha'.1
    obtain ⟨e', -, he'⟩ := mem_inpR_zero.1 hb'.1
    obtain ⟨a1, a2, a3⟩ := a
    obtain ⟨b1, b2, b3⟩ := b
    simp only at ha' hb' he he' hab ⊢
    subst he he'
    simp only [pw, pwR] at hab
    rw [ha'.2.1, ha'.2.2, hb'.2.1, hb'.2.2, hab]
  · -- each piece contains at most one kept copy
    intro W hW
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    have hPx : ∀ a ∈ P, a ∈ I0 → ∀ b ∈ P, b ∈ I0 → a = b := by
      intro a ha haI b hb hbI
      obtain ⟨e, -, rfl⟩ := mem_inpR_zero.1 haI
      obtain ⟨e', -, rfl⟩ := mem_inpR_zero.1 hbI
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
      · have h1 := mem_powerset.1 (WbaseR_subset_powerset h) ha
        obtain ⟨T', hT'⟩ : ∃ T', sp.length = T' + 1 := ⟨sp.length - 1, by omega⟩
        rw [hT'] at h1
        obtain ⟨f, -, s, -, hf⟩ := mem_inpR_succ.1 h1
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
    rw [mdeg_liftS]
    calc ∑ ℓ ∈ I0, wdeg sg ℓ S = ∑ ℓ ∈ I0.filter (fun ℓ => S ⊆ (pw ℓ).1), 1 := by
          rw [sum_filter]
          refine sum_congr rfl fun ℓ hℓ => ?_
          obtain ⟨e, -, rfl⟩ := mem_inpR_zero.1 hℓ
          rw [wdeg_wsg]
          simp [pw, pwR, ZMod.val_one]
      _ = (I0.filter (fun ℓ => S ⊆ (pw ℓ).1)).card := by rw [card_eq_sum_ones]
      _ ≤ (X.filter (S ⊆ ·)).card := by
          have hsub : I0.filter (fun ℓ => S ⊆ (pw ℓ).1) ⊆ (X.filter (S ⊆ ·)).image Lab.x := by
            intro ℓ hℓ
            obtain ⟨hℓ, ht⟩ := mem_filter.1 hℓ
            obtain ⟨e, he, rfl⟩ := mem_inpR_zero.1 hℓ
            exact mem_image.2 ⟨e, mem_filter.2 ⟨he, ht⟩, rfl⟩
          exact (card_le_card hsub).trans card_image_le
      _ ≤ B := hX S hS
  · -- degree of the reservoir
    intro S hS
    rw [mdeg_liftS]
    calc ∑ ℓ ∈ R, wdeg sg ℓ S ≤ ∑ ℓ ∈ R.filter (fun ℓ => S ⊆ (pw ℓ).1), K := by
          rw [sum_filter]
          refine sum_le_sum fun ℓ _ => ?_
          rw [wdeg_wsg]
          split_ifs with h
          · exact (ZMod.val_lt _).le
          · exact le_rfl
      _ = (R.filter (fun ℓ => S ⊆ (pw ℓ).1)).card * K := by rw [sum_const, smul_eq_mul]
      _ ≤ (4 * (L + 1) * K ^ 2 * B) * K := Nat.mul_le_mul_right _
          ((plan_loadR hok S).trans (Nat.mul_le_mul_left _ (hP S hS)))
      _ = 4 * (L + 1) * K ^ 3 * B := by ring
      _ ≤ CplR K M L * B := Nat.mul_le_mul_right _ (by
          unfold CplR; nlinarith [Nat.zero_le (K * (L + 3 + K * M)), Nat.zero_le (2 ^ (K * M))])
  · -- pieces through an `(r - 1)`-set
    intro S hS
    have hsub : (Wl.image (liftS sg)).filter (fun W => S ⊆ W.biUnion (cpEnds sg)) ⊆
        (Wl.filter (fun P => S ⊆ lverts pw P)).image (liftS sg) := by
      intro W hW
      obtain ⟨hW, hv⟩ := mem_filter.1 hW
      obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
      refine mem_image.2 ⟨P, mem_filter.2 ⟨hP, hv.trans ?_⟩, rfl⟩
      intro v hv'
      obtain ⟨c, hc, hvc⟩ := mem_biUnion.1 hv'
      have hc1 := (mem_liftS.1 hc).1
      have hcR : c ∈ liftS sg (I0 ∪ R) := liftS_mono (pieces_subsetR hP) hc
      rw [hends c hcR] at hvc
      exact (le_sup (f := fun x => (pw x).1) hc1) hvc
    refine (card_le_card hsub).trans (card_image_le.trans ((plan_pieceLoadR hok S).trans ?_))
    have h1 := Nat.mul_le_mul_left (4 * (L + 1) * K ^ 2) (hP S hS)
    have h3 : 2 ^ (K * M) ≤ 2 ^ (K * M) * B := Nat.le_mul_of_pos_right _ hB
    have h4 : 4 * (L + 1) * K ^ 2 ≤ 4 * (L + 1) * K ^ 3 := by
      have : K ^ 2 ≤ K ^ 3 := Nat.pow_le_pow_right hK' (by norm_num)
      exact Nat.mul_le_mul_left _ this
    calc 4 * (L + 1) * K ^ 2 * (∑ t ∈ range sp.length, passR sp X t S) +
          2 ^ (inpR sp X (K := K) q r sp.length).card
        ≤ 4 * (L + 1) * K ^ 3 * B + 2 ^ (K * M) * B := by
          have := Nat.mul_le_mul_right B h4
          nlinarith
      _ = (4 * (L + 1) * K ^ 3 + 2 ^ (K * M)) * B := by ring
      _ ≤ CplR K M L * B := Nat.mul_le_mul_right _ (by
          unfold CplR; nlinarith [Nat.zero_le (K * (L + 3 + K * M))])

end RefinedAbsorption.HyperPlan
