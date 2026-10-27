module
public import RequestProject.OddGrid.PlanDecomp

/-!
# Multiplicities in a plan

Every label of a plan lies in a bounded number of pieces:

* `chW_mult`: at most `K + 6` pieces of one accumulator chain;
* `stW_mult`: at most `K + 10` pieces of one stage;
* `plan_mult`: at most `2 (K + 10) + 2 ^ |final carries|` pieces of the plan with its base.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner

section ChainMult

variable {Λ : Type} [DecidableEq Λ] {K : ℕ} [NeZero K]
  {cp cn : ℕ → ZMod K → Λ} {item : ℕ → Λ} {w : ℕ → ZMod K}

lemma card_le_one_of_eq {α : Type*} {s : Finset α} (h : ∀ a ∈ s, ∀ b ∈ s, a = b) : s.card ≤ 1 :=
  card_le_one.2 h

/-- **Multiplicity in an accumulator chain.** -/
lemma chW_mult (t : ℕ) (hcp : ∀ k s k' s', cp k s = cp k' s' ↔ k = k' ∧ s = s')
    (hcn : ∀ k s k' s', cn k s = cn k' s' ↔ k = k' ∧ s = s')
    (hit : ∀ k ∈ Icc 1 t, ∀ k' ∈ Icc 1 t, item k = item k' → k = k') (x : Λ) :
    ((chW cp cn item w t).filter (x ∈ ·)).card ≤ K + 6 := by
  unfold chW
  rw [filter_union]
  refine (card_union_le _ _).trans ?_
  set S := (Icc 1 t) ×ˢ (univ : Finset (ZMod K)) with hS
  set S' := S.filter (fun p => p.1 = 1 → p.2 = 0)
  -- the transition pieces
  have hA : ((S'.biUnion fun p => ({chT cp cn item w p.1 p.2 true,
      chT cp cn item w p.1 p.2 false} : Finset (Finset Λ))).filter (x ∈ ·)).card ≤ K + 4 := by
    have hsub : (S'.biUnion fun p => ({chT cp cn item w p.1 p.2 true,
        chT cp cn item w p.1 p.2 false} : Finset (Finset Λ))).filter (x ∈ ·) ⊆
        (S.filter (fun p => x ∈ chT cp cn item w p.1 p.2 true)).image
          (fun p => chT cp cn item w p.1 p.2 true) ∪
        (S.filter (fun p => x ∈ chT cp cn item w p.1 p.2 false)).image
          (fun p => chT cp cn item w p.1 p.2 false) := by
      intro P hP
      simp only [mem_filter, mem_biUnion, mem_insert, mem_singleton] at hP
      obtain ⟨⟨p, hp, rfl | rfl⟩, hx⟩ := hP
      · exact mem_union_left _ (mem_image.2 ⟨p, mem_filter.2 ⟨(mem_filter.1 hp).1, hx⟩, rfl⟩)
      · exact mem_union_right _ (mem_image.2 ⟨p, mem_filter.2 ⟨(mem_filter.1 hp).1, hx⟩, rfl⟩)
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    refine (Nat.add_le_add card_image_le card_image_le).trans ?_
    -- present-item transitions
    have h1 : (S.filter (fun p => x ∈ chT cp cn item w p.1 p.2 true)).card ≤ K + 2 := by
      have hsub1 : S.filter (fun p => x ∈ chT cp cn item w p.1 p.2 true) ⊆
          (S.filter (fun p => x = cp (p.1 - 1) p.2) ∪ S.filter (fun p => x = item p.1)) ∪
            S.filter (fun p => x = cn p.1 (p.2 + w p.1)) := by
        intro p hp
        simp only [mem_filter, chT, if_true, mem_insert, mem_singleton] at hp
        obtain ⟨hp, h | h | h⟩ := hp
        · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hp, h⟩))
        · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hp, h⟩))
        · exact mem_union_right _ (mem_filter.2 ⟨hp, h⟩)
      refine (card_le_card hsub1).trans ((card_union_le _ _).trans ?_)
      have ha : (S.filter (fun p => x = cp (p.1 - 1) p.2)).card ≤ 1 := by
        apply card_le_one_of_eq
        intro a ha b hb
        simp only [hS, mem_filter, mem_product, mem_Icc] at ha hb
        have := (hcp _ _ _ _).1 (ha.2.symm.trans hb.2)
        exact Prod.ext (by omega) this.2
      have hb : (S.filter (fun p => x = item p.1)).card ≤ K := by
        by_cases hne : (S.filter (fun p => x = item p.1)).Nonempty
        · obtain ⟨a, ha⟩ := hne
          have hsub2 : S.filter (fun p => x = item p.1) ⊆ {a.1} ×ˢ (univ : Finset (ZMod K)) := by
            intro b hb
            rw [mem_filter] at ha hb
            rw [mem_product, mem_singleton]
            exact ⟨hit _ (mem_product.1 hb.1).1 _ (mem_product.1 ha.1).1 (hb.2.symm.trans ha.2),
              mem_univ _⟩
          refine (card_le_card hsub2).trans ?_
          simp
        · rw [not_nonempty_iff_eq_empty.1 hne]; simp
      have hc : (S.filter (fun p => x = cn p.1 (p.2 + w p.1))).card ≤ 1 := by
        apply card_le_one_of_eq
        intro a ha b hb
        simp only [mem_filter] at ha hb
        have := (hcn _ _ _ _).1 (ha.2.symm.trans hb.2)
        obtain ⟨h1, h2⟩ := this
        refine Prod.ext h1 ?_
        rw [h1] at h2; exact add_right_cancel h2
      have hab := card_union_le (S.filter (fun p => x = cp (p.1 - 1) p.2))
        (S.filter (fun p => x = item p.1))
      omega
    -- absent-item transitions
    have h0 : (S.filter (fun p => x ∈ chT cp cn item w p.1 p.2 false)).card ≤ 2 := by
      have hsub0 : S.filter (fun p => x ∈ chT cp cn item w p.1 p.2 false) ⊆
          S.filter (fun p => x = cp (p.1 - 1) p.2) ∪ S.filter (fun p => x = cn p.1 p.2) := by
        intro p hp
        simp only [mem_filter, chT, Bool.false_eq_true, if_false, mem_insert,
          mem_singleton] at hp
        obtain ⟨hp, h | h⟩ := hp
        · exact mem_union_left _ (mem_filter.2 ⟨hp, h⟩)
        · exact mem_union_right _ (mem_filter.2 ⟨hp, h⟩)
      refine (card_le_card hsub0).trans ((card_union_le _ _).trans ?_)
      have ha : (S.filter (fun p => x = cp (p.1 - 1) p.2)).card ≤ 1 := by
        apply card_le_one_of_eq
        intro a ha b hb
        simp only [hS, mem_filter, mem_product, mem_Icc] at ha hb
        have := (hcp _ _ _ _).1 (ha.2.symm.trans hb.2)
        exact Prod.ext (by omega) this.2
      have hc : (S.filter (fun p => x = cn p.1 p.2)).card ≤ 1 := by
        apply card_le_one_of_eq
        intro a ha b hb
        simp only [mem_filter] at ha hb
        exact Prod.ext ((hcn _ _ _ _).1 (ha.2.symm.trans hb.2)).1
          ((hcn _ _ _ _).1 (ha.2.symm.trans hb.2)).2
      omega
    omega
  -- the pairing pieces
  have hB : ((S.image fun p => chQ cp cn p.1 p.2).filter (x ∈ ·)).card ≤ 2 := by
    have hsub : (S.image fun p => chQ cp cn p.1 p.2).filter (x ∈ ·) ⊆
        (S.filter (fun p => x = cn p.1 p.2) ∪ S.filter (fun p => x = cp p.1 p.2)).image
          (fun p => chQ cp cn p.1 p.2) := by
      intro P hP
      simp only [mem_filter, mem_image] at hP
      obtain ⟨⟨p, hp, rfl⟩, hx⟩ := hP
      refine mem_image.2 ⟨p, ?_, rfl⟩
      simp only [chQ, mem_insert, mem_singleton] at hx
      rcases hx with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨hp, h⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hp, h⟩)
    refine (card_le_card hsub).trans (card_image_le.trans ((card_union_le _ _).trans ?_))
    have ha : (S.filter (fun p => x = cn p.1 p.2)).card ≤ 1 := by
      apply card_le_one_of_eq
      intro a ha b hb
      simp only [mem_filter] at ha hb
      exact Prod.ext ((hcn _ _ _ _).1 (ha.2.symm.trans hb.2)).1
        ((hcn _ _ _ _).1 (ha.2.symm.trans hb.2)).2
    have hc : (S.filter (fun p => x = cp p.1 p.2)).card ≤ 1 := by
      apply card_le_one_of_eq
      intro a ha b hb
      simp only [mem_filter] at ha hb
      exact Prod.ext ((hcp _ _ _ _).1 (ha.2.symm.trans hb.2)).1
        ((hcp _ _ _ _).1 (ha.2.symm.trans hb.2)).2
    omega
  omega

/-- Elements of the pieces of a chain. -/
lemma mem_of_mem_chW {t : ℕ} {P : Finset Λ} (hP : P ∈ chW cp cn item w t) {x : Λ}
    (hx : x ∈ P) : (∃ k s, x = cp k s) ∨ (∃ k s, x = cn k s) ∨ (∃ k ∈ Icc 1 t, x = item k) := by
  simp only [chW, mem_union, mem_biUnion, mem_filter, mem_product, mem_univ, and_true,
    mem_insert, mem_singleton, mem_image] at hP
  rcases hP with ⟨⟨k, s⟩, ⟨hk, -⟩, rfl | rfl⟩ | ⟨⟨k, s⟩, hk, rfl⟩
  · simp only [chT, if_true, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr (Or.inr ⟨k, hk, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  · simp only [chT, Bool.false_eq_true, if_false, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  · simp only [chQ, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl ⟨_, _, rfl⟩)
    · exact Or.inl ⟨_, _, rfl⟩

end ChainMult

section StageMult

variable {n K : ℕ} [NeZero K]

/-- The pair of the chain a label can belong to. -/
def chainPair (restF : RestF n K) : Lab n K → Finset (Fin n)
  | .cp _ e _ _ => e
  | .cn _ e _ _ => e
  | x => restPair restF x

/-- **Multiplicity in a stage.** -/
lemma stW_mult (t : ℕ) (I : Finset (Lab n K)) (restF : RestF n K) (x : Lab n K) :
    ((stW t I restF).filter (x ∈ ·)).card ≤ K + 10 := by
  unfold stW
  rw [filter_union, filter_union]
  refine (card_union_le _ _).trans ?_
  have hu := card_union_le ((I.image (P1 t)).filter (x ∈ ·))
    ((I.image (P0 t restF)).filter (x ∈ ·))
  -- switch pieces
  have h1 : ((I.image (P1 t)).filter (x ∈ ·)).card ≤ 2 := by
    have hsub : (I.image (P1 t)).filter (x ∈ ·) ⊆
        (I.filter (fun ℓ => ℓ = x) ∪ I.filter (fun ℓ => x = .anti t ℓ)).image (P1 t) := by
      intro P hP
      simp only [mem_filter, mem_image] at hP
      obtain ⟨⟨ℓ, hℓ, rfl⟩, hx⟩ := hP
      refine mem_image.2 ⟨ℓ, ?_, rfl⟩
      simp only [P1, mem_insert, mem_singleton] at hx
      rcases hx with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨hℓ, h.symm⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hℓ, h⟩)
    refine (card_le_card hsub).trans (card_image_le.trans ((card_union_le _ _).trans ?_))
    have ha : (I.filter (fun ℓ => ℓ = x)).card ≤ 1 :=
      card_le_one.2 fun a ha b hb => (mem_filter.1 ha).2.trans (mem_filter.1 hb).2.symm
    have hb : (I.filter (fun ℓ => x = .anti t ℓ)).card ≤ 1 := by
      refine card_le_one.2 fun a ha b hb => ?_
      have := (mem_filter.1 ha).2.symm.trans (mem_filter.1 hb).2
      simp only [Lab.anti.injEq, true_and] at this
      exact this
    omega
  have h0 : ((I.image (P0 t restF)).filter (x ∈ ·)).card ≤ 2 := by
    have hsub : (I.image (P0 t restF)).filter (x ∈ ·) ⊆
        (I.filter (fun ℓ => x = .anti t ℓ) ∪ I.filter (fun ℓ => src x = ℓ)).image (P0 t restF) := by
      intro P hP
      simp only [mem_filter, mem_image] at hP
      obtain ⟨⟨ℓ, hℓ, rfl⟩, hx⟩ := hP
      refine mem_image.2 ⟨ℓ, ?_, rfl⟩
      simp only [P0, mem_insert] at hx
      rcases hx with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨hℓ, h⟩)
      · obtain ⟨k, -, rfl⟩ := mem_rests.1 h
        exact mem_union_right _ (mem_filter.2 ⟨hℓ, rfl⟩)
    refine (card_le_card hsub).trans (card_image_le.trans ((card_union_le _ _).trans ?_))
    have ha : (I.filter (fun ℓ => x = .anti t ℓ)).card ≤ 1 := by
      refine card_le_one.2 fun a ha b hb => ?_
      have := (mem_filter.1 ha).2.symm.trans (mem_filter.1 hb).2
      simp only [Lab.anti.injEq, true_and] at this
      exact this
    have hb : (I.filter (fun ℓ => src x = ℓ)).card ≤ 1 :=
      card_le_one.2 fun a ha b hb => (mem_filter.1 ha).2.symm.trans (mem_filter.1 hb).2
    omega
  -- chain pieces
  have hc : (((outs t I restF).biUnion fun e => chW (Lab.cp t e) (Lab.cn t e) (item t I restF e)
      (iw t I restF e) (slen t I restF e)).filter (x ∈ ·)).card ≤ K + 6 := by
    set e₀ := chainPair restF x
    have hsub : ((outs t I restF).biUnion fun e => chW (Lab.cp t e) (Lab.cn t e)
        (item t I restF e) (iw t I restF e) (slen t I restF e)).filter (x ∈ ·) ⊆
        (chW (Lab.cp t e₀) (Lab.cn t e₀) (item t I restF e₀) (iw t I restF e₀)
          (slen t I restF e₀)).filter (x ∈ ·) := by
      intro P hP
      simp only [mem_filter, mem_biUnion] at hP
      obtain ⟨⟨e, -, hPe⟩, hx⟩ := hP
      have he : e = e₀ := by
        rcases mem_of_mem_chW hPe hx with ⟨k, s, rfl⟩ | ⟨k, s, rfl⟩ | ⟨k, hk, rfl⟩
        · rfl
        · rfl
        · have hon := mem_onPair.1 (item_mem hk)
          obtain ⟨ℓ, -, j, -, hj⟩ := item_isRest hk
          simp only [e₀]
          rw [hj] at hon ⊢
          exact hon.2.symm
      subst he
      exact mem_filter.2 ⟨hPe, hx⟩
    refine (card_le_card hsub).trans (chW_mult _ ?_ ?_ ?_ x)
    · intro k s k' s'; simp
    · intro k s k' s'; simp
    · intro k hk k' hk' h; exact item_inj hk hk' h
  omega

end StageMult



section PlanMult

variable {n K : ℕ} [NeZero K] {q : ℕ} {sp : List (Spec n)} {X : Finset (Finset (Fin n))}

/-- The stages whose pieces can contain a label of stage index `o`. -/
def stCand : Option ℕ → Finset ℕ
  | none => {0}
  | some j => {j, j + 1}

lemma card_stCand_le (o : Option ℕ) : (stCand o).card ≤ 2 := by
  cases o with
  | none => simp [stCand]
  | some j => exact (card_insert_le _ _).trans (by simp)

lemma stage_of_mem_stW {i : ℕ} {P : Finset (Lab n K)}
    (hP : P ∈ stW i (inp sp X (K := K) q i) (restFP sp X i)) {x : Lab n K} (hx : x ∈ P) :
    i ∈ stCand (stIdx x) := by
  rcases mem_union.1 (stW_subset hP hx) with h | h
  · cases i with
    | zero => rw [stIdx_inp_zero h]; simp [stCand]
    | succ j => obtain ⟨e, -, s, -, rfl⟩ := mem_inp_succ.1 h; simp [stIdx, stCand]
  · rw [stIdx_of_stR h]; simp [stCand]

open Classical in
lemma Wbase_subset_powerset : Wbase (K := K) sp X q ⊆ (inp sp X q sp.length).powerset :=
  filter_subset _ _

/-- **Multiplicity in a plan with its base pieces.** -/
lemma plan_mult (x : Lab n K) :
    ((Wall sp X q sp.length ∪ Wbase sp X q).filter (x ∈ ·)).card ≤
      2 * (K + 10) + 2 ^ (inp sp X (K := K) q sp.length).card := by
  rw [filter_union]
  refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · have hsub : (Wall sp X q sp.length).filter (x ∈ ·) ⊆ (stCand (stIdx x)).biUnion
        (fun i => (stW i (inp sp X q i) (restFP sp X i)).filter (x ∈ ·)) := by
      intro P hP
      obtain ⟨hP, hx⟩ := mem_filter.1 hP
      obtain ⟨i, -, hP⟩ := mem_biUnion.1 hP
      exact mem_biUnion.2 ⟨i, stage_of_mem_stW hP hx, mem_filter.2 ⟨hP, hx⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc _ ≤ ∑ _i ∈ stCand (stIdx x), (K + 10) := sum_le_sum fun i _ => stW_mult _ _ _ _
      _ = (stCand (stIdx x)).card * (K + 10) := by rw [sum_const, smul_eq_mul]
      _ ≤ 2 * (K + 10) := Nat.mul_le_mul_right _ (card_stCand_le _)
  · refine (card_le_card (filter_subset _ _)).trans ?_
    exact (card_le_card Wbase_subset_powerset).trans (card_powerset _).le

end PlanMult

end RefinedAbsorption.OddGrid
