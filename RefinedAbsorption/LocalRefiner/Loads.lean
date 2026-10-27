module
public import RefinedAbsorption.LocalRefiner.Refiner

/-!
# Loads of the local refiner

Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

If every vertex lies in at most `Dn` edges of `X`, then every vertex is touched by at most
`4 q^2 (Dn + 1)` labels (`touch_card_le`): the labels of the edges at the vertex, the tokens and
chain reservoirs of the vertex and of its two predecessors (each vertex has its own reserve
`{u, u+1, u+2}`, so every reserve vertex serves three vertices), and the global blocks placed on
the edges at the vertex.  Hence the refiner has degree `O(Dn + 1)` (`degR_le`) and every vertex
lies in `O(Dn + 1)` pieces (`pieceDeg_le`).
-/

@[expose] public section

namespace RefinedAbsorption.LocalRefiner

open Finset RefinedAbsorption.ChainRefiner RefinedAbsorption.MultiRefiner

variable {n : ℕ} [NeZero n] {k : ℕ} {X : Finset (Finset (Fin n))}

lemma touch_tok {u x : Fin n} {ℓ : Lb n} (hℓ : segs k (gE X) ℓ = tokSegs k u)
    (h : touch (sgX k X) x ℓ = true) : u = x ∨ u = x - 1 ∨ u = x - 2 := by
  rw [touch_iff] at h
  obtain ⟨p, hp, hx⟩ := h
  rw [show sgX k X ℓ = _ from hℓ] at hp
  simp only [tokSegs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp only [mem_insert, mem_singleton] at hx
  · rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (by simp))
  · rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (by simp))
  · rcases hx with rfl | rfl
    · exact Or.inr (Or.inl (by simp))
    · exact Or.inr (Or.inr (by simp))

lemma touch_single {x : Fin n} {ℓ : Lb n} {p : Finset (Fin n)} {c : ℕ}
    (hℓ : segs k (gE X) ℓ = [(p, c)]) (h : touch (sgX k X) x ℓ = true) : x ∈ p := by
  rw [touch_iff] at h
  obtain ⟨p', hp, hx⟩ := h
  rw [show sgX k X ℓ = _ from hℓ] at hp
  simp only [List.mem_singleton] at hp
  subst hp; exact hx

omit [NeZero n] in
lemma mU_eq (u : Fin n) : mU X u = (X.filter (u ∈ ·)).card := Finset.length_toList _

lemma card_three (x : Fin n) : ({x, x - 1, x - 2} : Finset (Fin n)).card ≤ 3 :=
  (card_insert_le _ _).trans (by have := card_insert_le (x - 1) {x - 2}; simp at this ⊢; omega)

lemma gE_count {Dn : ℕ} (hD : ∀ y : Fin n, (X.filter (y ∈ ·)).card ≤ Dn) (x : Fin n) :
    ((range (mG X () + 2)).filter (fun i => x ∈ gE X i)).card ≤ Dn + 2 := by
  have hsub : (range (mG X () + 2)).filter (fun i => x ∈ gE X i) ⊆
      ((range (mG X ())).filter (fun i => x ∈ enX X i)) ∪ {mG X (), mG X () + 1} := by
    intro i hi
    simp only [mem_filter, mem_range] at hi
    simp only [mem_union, mem_filter, mem_range, mem_insert, mem_singleton]
    by_cases h : i < mG X ()
    · left
      refine ⟨h, ?_⟩
      have := hi.2
      simp only [gE] at this
      rw [if_pos (show i < X.toList.length from h)] at this
      exact this
    · right; omega
  have hcnt : ((range (mG X ())).filter (fun i => x ∈ enX X i)).card ≤ Dn := by
    calc _ ≤ (X.filter (x ∈ ·)).card := by
          apply card_le_card_of_injOn (fun i => enX X i)
          · intro i hi
            simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi
            simp only [coe_filter, Set.mem_setOf_eq]
            exact ⟨enX_mem hi.1, hi.2⟩
          · intro i hi j hj h
            simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi hj
            exact enX_inj hi.1 hj.1 h
      _ ≤ Dn := hD x
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ + _ := card_union_le _ _
    _ ≤ Dn + 2 := Nat.add_le_add hcnt (card_le_two)

/-- The labels touching a vertex. -/
noncomputable def touchSet (k : ℕ) (X : Finset (Finset (Fin n))) (x : Fin n) : Finset (Lb n) :=
  (X.image Lb.xe ∪ RL k X).filter (touch (sgX k X) x ·)

/-- **Few labels touch a vertex.** -/
theorem touch_card_le {Dn : ℕ} (hD : ∀ y : Fin n, (X.filter (y ∈ ·)).card ≤ Dn) (x : Fin n) :
    (touchSet k X x).card ≤ 4 * (2 * k + 4) ^ 2 * (Dn + 1) := by
  set E1 := X.filter (x ∈ ·)
  set T3 : Finset (Fin n) := {x, x - 1, x - 2}
  set A₁ := E1.image Lb.xe
  set A₂ := E1.image Lb.ae
  set A₃ := E1.image Lb.ke
  set A₄ := T3.biUnion fun u => (X.filter (u ∈ ·)).image fun e => Lb.tk e u
  set A₅ := T3.biUnion fun u => (Rlab (2 * k + 3) (mU X u)).image (φU X u)
  set A₆ := (((range (mG X () + 2)).filter (fun i => x ∈ gE X i)) ×ˢ
    range ((k + 2) * (2 * k + 3))).image fun p => (Lb.gb p.1 p.2 : Lb n)
  have hsub : touchSet k X x ⊆ A₁ ∪ A₂ ∪ A₃ ∪ A₄ ∪ A₅ ∪ A₆ := by
    intro g hg
    rw [touchSet, mem_filter] at hg
    obtain ⟨hg, ht⟩ := hg
    simp only [mem_union]
    rcases mem_union.1 hg with h | h
    · obtain ⟨e, he, rfl⟩ := mem_image.1 h
      have := touch_single (k := k) (X := X) rfl ht
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (mem_image_of_mem _ (mem_filter.2 ⟨he, this⟩))))))
    · rcases RL_cases h with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, he, u, hu, rfl⟩ | ⟨u, i, j, rfl⟩ |
          ⟨i, j, rfl⟩
      · have := touch_single (k := k) (X := X) rfl ht
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mem_image_of_mem _ (mem_filter.2 ⟨he, this⟩))))))
      · have := touch_single (k := k) (X := X) rfl ht
        exact Or.inl (Or.inl (Or.inl (Or.inr (mem_image_of_mem _ (mem_filter.2 ⟨he, this⟩)))))
      · have hT : u ∈ T3 := by
          rcases touch_tok (k := k) (X := X) rfl ht with h | h | h <;> simp [T3, h]
        refine Or.inl (Or.inl (Or.inr ?_))
        simp only [A₄, mem_biUnion, mem_image, mem_filter]
        exact ⟨u, hT, e, ⟨he, hu⟩, rfl⟩
      · have hT : u ∈ T3 := by
          rcases touch_tok (k := k) (X := X) rfl ht with h | h | h <;> simp [T3, h]
        refine Or.inl (Or.inr ?_)
        simp only [A₅, mem_biUnion, mem_image]
        refine ⟨u, hT, zl i j, ?_, rfl⟩
        have h' : (Lb.vb u i j : Lb n) ∈ chR (2 * k + 3) (mU X) (φU X) := by
          rcases mem_RL.1 h with h | h | h | h | h
          · simp at h
          · simp at h
          · simp [TL] at h
          · exact h
          · obtain ⟨_, _, h⟩ := chR_G_cases h; cases h
        simp only [chR, mem_biUnion, mem_univ, true_and, mem_image] at h'
        obtain ⟨u', a, ha, he⟩ := h'
        rcases lab_cases a with ⟨i', rfl⟩ | ⟨i', j', rfl⟩
        · simp [φU, xl] at he
        · simp only [φU, zl, Lb.vb.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          exact ha
      · refine Or.inr ?_
        have hx := touch_single (k := k) (X := X) rfl ht
        have h' : (Lb.gb i j : Lb n) ∈ chR ((k + 2) * (2 * k + 3)) (mG X) (φG X) := by
          rcases mem_RL.1 h with h | h | h | h | h
          · simp at h
          · simp at h
          · simp [TL] at h
          · obtain ⟨_, _, _, h⟩ := chR_U_cases h; cases h
          · exact h
        obtain ⟨a, ha, he⟩ : ∃ a ∈ Rlab ((k + 2) * (2 * k + 3)) (mG X ()),
            φG X () a = Lb.gb i j := by
          simp only [chR, mem_biUnion, mem_univ, true_and, mem_image] at h'
          obtain ⟨o, a, ha, he⟩ := h'
          exact ⟨a, ha, he⟩
        rcases lab_cases a with ⟨i', rfl⟩ | ⟨i', j', rfl⟩
        · simp [φG, xl] at he
        · simp only [φG, zl, Lb.gb.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          rw [mem_Rlab_zl] at ha
          have hpad : (k + 2) * (2 * k + 3) - finT ((k + 2) * (2 * k + 3)) (mG X ()) ≤
              (k + 2) * (2 * k + 3) := Nat.sub_le _ _
          have hmod := Nat.mod_le ((k + 2) * (2 * k + 3) -
            finT ((k + 2) * (2 * k + 3)) (mG X ())) ((k + 2) * (2 * k + 3))
          simp only [A₆, mem_image, mem_product, mem_filter, mem_range]
          exact ⟨(_, _), ⟨⟨by omega, hx⟩, by omega⟩, rfl⟩
  have hE1 : E1.card ≤ Dn := hD x
  have h1 : A₁.card ≤ Dn := card_image_le.trans hE1
  have h2 : A₂.card ≤ Dn := card_image_le.trans hE1
  have h3 : A₃.card ≤ Dn := card_image_le.trans hE1
  have h4 : A₄.card ≤ 3 * Dn := by
    calc _ ≤ ∑ u ∈ T3, ((X.filter (u ∈ ·)).image fun e => Lb.tk e u).card := card_biUnion_le
      _ ≤ ∑ u ∈ T3, Dn := sum_le_sum fun u _ => card_image_le.trans (hD u)
      _ = T3.card * Dn := by rw [sum_const, smul_eq_mul]
      _ ≤ 3 * Dn := Nat.mul_le_mul_right _ (card_three x)
  have h5 : A₅.card ≤ 3 * ((Dn + 2) * (2 * k + 2)) := by
    calc _ ≤ ∑ u ∈ T3, ((Rlab (2 * k + 3) (mU X u)).image (φU X u)).card := card_biUnion_le
      _ ≤ ∑ u ∈ T3, (Dn + 2) * (2 * k + 2) := by
          apply sum_le_sum
          intro u _
          refine card_image_le.trans ((card_Rlab_le (by omega)).trans ?_)
          rw [mU_eq, show 2 * k + 3 - 1 = 2 * k + 2 by omega]
          exact Nat.mul_le_mul_right _ (by have := hD u; omega)
      _ = T3.card * ((Dn + 2) * (2 * k + 2)) := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (card_three x)
  have h6 : A₆.card ≤ (Dn + 2) * ((k + 2) * (2 * k + 3)) := by
    refine card_image_le.trans ?_
    rw [card_product, card_range]
    exact Nat.mul_le_mul_right _ (gE_count hD x)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ A₁.card + A₂.card + A₃.card + A₄.card + A₅.card + A₆.card := by
        refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        exact card_union_le _ _
    _ ≤ Dn + Dn + Dn + 3 * Dn + 3 * ((Dn + 2) * (2 * k + 2)) +
        (Dn + 2) * ((k + 2) * (2 * k + 3)) := by omega
    _ ≤ _ := by rw [sq]; nlinarith

/-- **Degree of the refiner.** -/
theorem degR_le {Dn : ℕ} (hD : ∀ y : Fin n, (X.filter (y ∈ ·)).card ≤ Dn) (x : Fin n) :
    mdeg (endsX k X) (RX k X) {x} ≤ Cloc k * (Dn + 1) := by
  have h := mdeg_liftS_le (sg := sgX k X) (RL k X) x ((2 * k + 4) ^ 2)
    (fun ℓ _ => by rw [wdeg_empty]; exact csz_le ℓ)
  have hsub : (RL k X).filter (touch (sgX k X) x ·) ⊆ touchSet k X x :=
    filter_subset_filter _ subset_union_right
  have ht := (card_le_card hsub).trans (touch_card_le (k := k) hD x)
  obtain ⟨-, -, -, f4, -⟩ := Q_pow_facts k
  calc _ ≤ _ := h
    _ ≤ (2 * k + 4) ^ 2 * (4 * (2 * k + 4) ^ 2 * (Dn + 1)) := Nat.mul_le_mul_left _ ht
    _ = 4 * ((2 * k + 4) ^ 2 * (2 * k + 4) ^ 2) * (Dn + 1) := by ring
    _ ≤ _ := by rw [f4, Cloc]; exact Nat.mul_le_mul_right _ (by omega)

/-- **Piece degrees.** -/
theorem pieceDeg_le {Dn : ℕ} (hD : ∀ y : Fin n, (X.filter (y ∈ ·)).card ≤ Dn) (x : Fin n) :
    ((WX k X).filter fun W => ({x} : Finset (Fin n)) ⊆ W.biUnion (endsX k X)).card ≤
      Cloc k * (Dn + 1) := by
  have hsub : (WX k X).filter (fun W => ({x} : Finset (Fin n)) ⊆ W.biUnion (endsX k X)) ⊆
      ((touchSet k X x).biUnion fun ℓ => (WL k X).filter (ℓ ∈ ·)).image (liftS (sgX k X)) := by
    intro W hW
    simp only [WX, mem_filter, mem_image, singleton_subset_iff, mem_biUnion] at hW
    obtain ⟨⟨P, hP, rfl⟩, c, hc, hx⟩ := hW
    refine mem_image.2 ⟨P, mem_biUnion.2 ⟨c.1, ?_, mem_filter.2 ⟨hP, (mem_liftS.1 hc).1⟩⟩, rfl⟩
    rw [touchSet, mem_filter]
    exact ⟨WL_subset hP (mem_liftS.1 hc).1, touch_of_mem_liftS hc hx⟩
  have ht := touch_card_le (k := k) hD x
  obtain ⟨-, -, -, f4, -⟩ := Q_pow_facts k
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ ≤ ∑ ℓ ∈ touchSet k X x, ((WL k X).filter (ℓ ∈ ·)).card := card_biUnion_le
    _ ≤ ∑ ℓ ∈ touchSet k X x, 3 * (2 * k + 4) ^ 2 := sum_le_sum fun ℓ _ => label_mult_le ℓ
    _ = (touchSet k X x).card * (3 * (2 * k + 4) ^ 2) := by rw [sum_const, smul_eq_mul]
    _ ≤ 4 * (2 * k + 4) ^ 2 * (Dn + 1) * (3 * (2 * k + 4) ^ 2) := Nat.mul_le_mul_right _ ht
    _ = 12 * ((2 * k + 4) ^ 2 * (2 * k + 4) ^ 2) * (Dn + 1) := by ring
    _ ≤ _ := by rw [f4, Cloc]; exact Nat.mul_le_mul_right _ (by omega)

/-- **Degree of `X`.** -/
theorem degX_eq (x : Fin n) : mdeg (endsX k X) (XlX X) {x} = (X.filter (x ∈ ·)).card := by
  rw [mdeg, XlX, filter_image, card_image_of_injective _ (fun a b h => by simpa using h)]
  congr 1
  apply filter_congr
  intro e _
  simp [endsX, cpEnds, segAt, segs, singleton_subset_iff]

/-- **Each piece contains at most one edge of `X`.** -/
theorem oneX_le {W : Finset (Lb n × ℕ × ℕ)} (hW : W ∈ WX k X) :
    (W.filter (· ∈ XlX X)).card ≤ 1 := by
  obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
  apply card_le_one.2
  intro c hc c' hc'
  simp only [mem_filter, XlX, mem_image] at hc hc'
  obtain ⟨hcP, e, -, rfl⟩ := hc
  obtain ⟨hcP', e', -, rfl⟩ := hc'
  have h1 := (mem_liftS.1 hcP).1
  have h2 := (mem_liftS.1 hcP').1
  simp only at h1 h2
  suffices e = e' by rw [this]
  rcases WL_cases hP with ⟨f, -, rfl⟩ | ⟨f, -, rfl⟩ | h | h
  · rcases mem_P1.1 h1 with h | h <;> rcases mem_P1.1 h2 with h' | h' <;>
      simp_all
  · rcases mem_P0.1 h1 with h | h | ⟨_, _, h⟩ <;> cases h
  · obtain ⟨u, -, hall⟩ := chFam_struct hqU chInj_U h
    obtain ⟨a, -, ha⟩ := hall _ h1
    rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩ <;> simp [φU, xl, zl] at ha
  · obtain ⟨u, -, hall⟩ := chFam_struct hqG chInj_G h
    obtain ⟨a, -, ha⟩ := hall _ h1
    rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩ <;> simp [φG, xl, zl] at ha

end RefinedAbsorption.LocalRefiner
