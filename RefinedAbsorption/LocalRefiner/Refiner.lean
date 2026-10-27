module
public import RefinedAbsorption.LocalRefiner.Construction

/-!
# The local refiner is a multi-refiner

Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

We lift the labels of `Construction` to copies (`Segments`) and prove that, for a `2`-graph `X`
on `Fin n` (`n ≥ 3`) and `q = 2k + 4`, the lift of the reservoir is a `K_q^2`-multi-refiner of
`X` with empty residue (`isMultiRefiner_local`), with constant `C = 64 q^4`.
-/

@[expose] public section

namespace RefinedAbsorption.LocalRefiner

open Finset RefinedAbsorption.ChainRefiner RefinedAbsorption.MultiRefiner

variable {n : ℕ} [NeZero n]

section Defs

variable (k : ℕ) (X : Finset (Finset (Fin n)))

/-- The segments. -/
noncomputable abbrev sgX : Lb n → List (Finset (Fin n) × ℕ) := segs k (gE X)

/-- The ends of the copies. -/
noncomputable abbrev endsX : Lb n × ℕ × ℕ → Finset (Fin n) := cpEnds (sgX k X)

/-- The copies of the edges of `X`. -/
def XlX : Finset (Lb n × ℕ × ℕ) := X.image fun e => (Lb.xe e, 0, 0)

/-- The refiner. -/
noncomputable def RX : Finset (Lb n × ℕ × ℕ) := liftS (sgX k X) (RL k X)

/-- The pieces. -/
noncomputable def WX : Finset (Finset (Lb n × ℕ × ℕ)) := (WL k X).image (liftS (sgX k X))

/-- The refinement constant. -/
def Cloc : ℕ := 64 * (2 * k + 4) ^ 4

end Defs

variable {k : ℕ} {X : Finset (Finset (Fin n))}

lemma XlX_eq : XlX X = liftS (sgX k X) (X.image Lb.xe) := by
  ext ⟨ℓ, s, c⟩
  simp only [XlX, mem_image, mem_liftS]
  constructor
  · rintro ⟨e, he, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [segs, segAt, he]
  · rintro ⟨⟨e, he, rfl⟩, hs, hc⟩
    simp only [segs, List.length_singleton, Nat.lt_one_iff] at hs
    subst hs
    simp only [segs, segAt, List.getD_cons_zero, Nat.lt_one_iff] at hc
    subst hc
    exact ⟨e, he, rfl⟩

/-! ### Shapes of labels and pieces -/

omit [NeZero n] in
lemma chR_U_cases {g : Lb n} (hg : g ∈ chR (2 * k + 3) (mU X) (φU X)) :
    ∃ u i j, g = .vb u i j := by
  simp only [chR, mem_biUnion, mem_univ, true_and, mem_image] at hg
  obtain ⟨u, a, ha, rfl⟩ := hg
  rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · exact absurd ha not_mem_Rlab_xl
  · exact ⟨u, i, j, rfl⟩

omit [NeZero n] in
lemma chR_G_cases {g : Lb n} (hg : g ∈ chR ((k + 2) * (2 * k + 3)) (mG X) (φG X)) :
    ∃ i j, g = .gb i j := by
  simp only [chR, mem_biUnion, mem_univ, true_and, mem_image] at hg
  obtain ⟨u, a, ha, rfl⟩ := hg
  rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · exact absurd ha not_mem_Rlab_xl
  · exact ⟨i, j, rfl⟩

omit [NeZero n] in
lemma RL_cases {g : Lb n} (hg : g ∈ RL k X) :
    (∃ e ∈ X, g = .ae e) ∨ (∃ e ∈ X, g = .ke e) ∨ (∃ e ∈ X, ∃ u ∈ e, g = .tk e u) ∨
      (∃ u i j, g = .vb u i j) ∨ (∃ i j, g = .gb i j) := by
  rcases mem_RL.1 hg with h | h | h | h | h
  · obtain ⟨e, he, rfl⟩ := mem_image.1 h; exact Or.inl ⟨e, he, rfl⟩
  · obtain ⟨e, he, rfl⟩ := mem_image.1 h; exact Or.inr (Or.inl ⟨e, he, rfl⟩)
  · simp only [TL, mem_biUnion, mem_image] at h
    obtain ⟨e, he, u, hu, rfl⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e, he, u, hu, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (chR_U_cases h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (chR_G_cases h))))

omit [NeZero n] in
lemma xe_not_mem_RL {e : Finset (Fin n)} : (Lb.xe e : Lb n) ∉ RL k X := by
  intro h
  rcases RL_cases h with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, h⟩ <;>
    cases h

omit [NeZero n] in
lemma WL_cases {P : Finset (Lb n)} (hP : P ∈ WL k X) :
    (∃ e ∈ X, P = P1 e) ∨ (∃ e ∈ X, P = P0 e) ∨ P ∈ chFam (2 * k + 3) (mU X) (φU X) ∨
      P ∈ chFam ((k + 2) * (2 * k + 3)) (mG X) (φG X) := by
  simp only [WL, mem_union, mem_image] at hP
  rcases hP with ((⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | h) | h
  · exact Or.inl ⟨e, he, rfl⟩
  · exact Or.inr (Or.inl ⟨e, he, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

omit [NeZero n] in
lemma WL_subset {P : Finset (Lb n)} (hP : P ∈ WL k X) : P ⊆ X.image Lb.xe ∪ RL k X := by
  intro g hg
  rw [mem_union, mem_RL]
  rcases WL_cases hP with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | h | h
  · rcases mem_P1.1 hg with rfl | rfl
    · exact Or.inl (mem_image_of_mem _ he)
    · exact Or.inr (Or.inl (mem_image_of_mem _ he))
  · rcases mem_P0.1 hg with rfl | rfl | ⟨u, hu, rfl⟩
    · exact Or.inr (Or.inl (mem_image_of_mem _ he))
    · exact Or.inr (Or.inr (Or.inl (mem_image_of_mem _ he)))
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      simp only [TL, mem_biUnion, mem_image]
      exact ⟨e, he, u, hu, rfl⟩
  · rcases mem_union.1 (chFam_subset hqU h hg) with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (chX_U_subset h'))))
  · rcases mem_union.1 (chFam_subset hqG h hg) with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))
    · exact Or.inr (Or.inr (Or.inl (chX_G_subset h')))

/-! ### Edges have two ends -/

lemma zero_ne_one_fin (hn : 3 ≤ n) : (0 : Fin n) ≠ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp

lemma gE_card (hX : IsRGraph 2 X) (hn : 3 ≤ n) (i : ℕ) : (gE X i).card = 2 := by
  unfold gE
  split_ifs with h
  · exact hX _ (enX_mem h)
  · exact card_pair (zero_ne_one_fin hn)

lemma seg_card (hX : IsRGraph 2 X) (hn : 3 ≤ n) {ℓ : Lb n}
    (hℓ : ℓ ∈ X.image Lb.xe ∪ RL k X) : ∀ p ∈ sgX k X ℓ, p.1.card = 2 := by
  have htok : ∀ u : Fin n, ∀ p ∈ tokSegs k u, p.1.card = 2 := by
    intro u p hp
    simp only [tokSegs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact card_pair (tok_ne₁ hn u)
    · exact card_pair (tok_ne₂ hn u)
    · exact card_pair (tok_ne₁₂ hn u)
  rcases mem_union.1 hℓ with h | h
  · obtain ⟨e, he, rfl⟩ := mem_image.1 h
    intro p hp
    simp only [sgX, segs, List.mem_singleton] at hp
    subst hp; exact hX e he
  · rcases RL_cases h with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | ⟨e, -, u, -, rfl⟩ | ⟨u, i, j, rfl⟩ |
        ⟨i, j, rfl⟩
    · intro p hp
      simp only [sgX, segs, List.mem_singleton] at hp
      subst hp; exact hX e he
    · intro p hp
      simp only [sgX, segs, List.mem_singleton] at hp
      subst hp; exact hX e he
    · exact htok u
    · exact htok u
    · intro p hp
      simp only [sgX, segs, List.mem_singleton] at hp
      subst hp; exact gE_card hX hn i

/-! ### Divisibility of the pieces -/

lemma choose_q_two (k : ℕ) : (2 * k + 4).choose 2 = (k + 2) * (2 * k + 3) := by
  rw [Nat.choose_two_right]
  rw [show (2 * k + 4) * (2 * k + 4 - 1) = 2 * ((k + 2) * (2 * k + 3)) by
    rw [show 2 * k + 4 - 1 = 2 * k + 3 by omega]; ring]
  omega

lemma div_of_sums (hn : 3 ≤ n) (P : Finset (Lb n))
    (hdeg : ∀ x : Fin n, ∑ ℓ ∈ P, cls k x ℓ = 0)
    (hcnt : (k + 2) * (2 * k + 3) ∣ ∑ ℓ ∈ P, csz k ℓ) :
    MIsDivisible (2 * k + 4) 2 (endsX k X) (liftS (sgX k X) P) := by
  intro S hS
  rw [mdeg_liftS]
  rcases Nat.lt_succ_iff.1 hS |>.lt_or_eq with h0 | h1
  · have : S = ∅ := card_eq_zero.1 (by omega)
    subst this
    simp only [card_empty, Nat.sub_zero]
    rw [choose_q_two]
    simp only [wdeg_empty]
    exact hcnt
  · obtain ⟨x, rfl⟩ := card_eq_one.1 h1
    simp only [card_singleton, show 2 * k + 4 - 1 = 2 * k + 3 by omega,
      show 2 - 1 = 1 by rfl, Nat.choose_one_right]
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    simp only [wdeg_cls k hn]
    exact hdeg x

omit [NeZero n] in
lemma cls_U {u x : Fin n} {a : Lab} : cls k x (φU X u a) = if x = u then 1 else 0 := by
  rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩ <;> rfl

omit [NeZero n] in
lemma csz_U {u : Fin n} {a : Lab} : csz k (φU X u a) = (2 * k + 4) * (k + 2) := by
  rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩ <;> rfl

omit [NeZero n] in
lemma cls_G {x : Fin n} {o : Unit} {a : Lab} : cls k x (φG X o a) = 0 := by
  rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩ <;> rfl

omit [NeZero n] in
lemma csz_G {o : Unit} {a : Lab} : csz k (φG X o a) = (2 * k + 3) * (k + 1) := by
  rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩ <;> rfl

theorem piece_divisible (hX : IsRGraph 2 X) (hn : 3 ≤ n) {P : Finset (Lb n)}
    (hP : P ∈ WL k X) : MIsDivisible (2 * k + 4) 2 (endsX k X) (liftS (sgX k X) P) := by
  apply div_of_sums hn
  · intro x
    rcases WL_cases hP with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | h | h
    · rw [P1, sum_pair (by simp)]
      simp only [cls]; split_ifs <;> simp
    · rw [P0, sum_insert (by simp), sum_insert (by simp),
        sum_image (fun a _ b _ h => by simpa using h)]
      simp only [cls, zero_add]
      by_cases hx : x ∈ e <;> simp [hx]
    · obtain ⟨u, hc, hall⟩ := chFam_struct hqU chInj_U h
      rw [sum_congr rfl (g := fun _ => (if x = u then 1 else 0 : ZMod (2 * k + 3)))]
      · rw [sum_const]
        rcases hc with hc | hc <;> rw [hc]
        · simp
        · rw [nsmul_eq_mul]
          have : ((2 * k + 3 : ℕ) : ZMod (2 * k + 3)) = 0 := ZMod.natCast_self _
          rw [this, zero_mul]
      · intro g hg
        obtain ⟨a, -, rfl⟩ := hall g hg
        exact cls_U
    · obtain ⟨o, -, hall⟩ := chFam_struct hqG chInj_G h
      apply sum_eq_zero
      intro g hg
      obtain ⟨a, -, rfl⟩ := hall g hg
      exact cls_G
  · rcases WL_cases hP with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | h | h
    · rw [P1, sum_pair (by simp)]
      exact ⟨1, by simp only [csz]; ring⟩
    · rw [P0, sum_insert (by simp), sum_insert (by simp),
        sum_image (fun a _ b _ h => by simpa using h)]
      simp only [csz, sum_const, hX e he, smul_eq_mul]
      exact ⟨4, by ring⟩
    · obtain ⟨u, hc, hall⟩ := chFam_struct hqU chInj_U h
      rw [sum_congr rfl (g := fun _ => (2 * k + 4) * (k + 2))]
      · rw [sum_const, smul_eq_mul]
        rcases hc with hc | hc <;> rw [hc]
        · simp
        · exact ⟨2 * (k + 2), by ring⟩
      · intro g hg
        obtain ⟨a, -, rfl⟩ := hall g hg
        exact csz_U
    · obtain ⟨o, hc, hall⟩ := chFam_struct hqG chInj_G h
      rw [sum_congr rfl (g := fun _ => (2 * k + 3) * (k + 1))]
      · rw [sum_const, smul_eq_mul]
        rcases hc with hc | hc <;> rw [hc]
        · simp
        · exact Dvd.intro _ rfl
      · intro g hg
        obtain ⟨a, -, rfl⟩ := hall g hg
        exact csz_G

/-! ### Sizes and multiplicities -/

omit [NeZero n] in
lemma csz_le (ℓ : Lb n) : csz k ℓ ≤ (2 * k + 4) ^ 2 := by
  cases ℓ <;> simp only [csz] <;> rw [sq] <;> nlinarith

lemma Q_pow_facts (k : ℕ) : 1 ≤ (2 * k + 4) ^ 2 ∧ (2 * k + 4) ^ 2 ≤ (2 * k + 4) ^ 4 ∧
    (2 * k + 4) * (2 * k + 4) ^ 2 ≤ (2 * k + 4) ^ 4 ∧
    (2 * k + 4) ^ 2 * (2 * k + 4) ^ 2 = (2 * k + 4) ^ 4 ∧ 4 ≤ (2 * k + 4) := by
  refine ⟨Nat.one_le_pow _ _ (by omega), Nat.pow_le_pow_right (by omega) (by norm_num), ?_,
    by ring, by omega⟩
  rw [← pow_succ']; exact Nat.pow_le_pow_right (by omega) (by norm_num)

theorem piece_card_le {P : Finset (Lb n)} (hP : P ∈ WL k X) (hX : IsRGraph 2 X) :
    (liftS (sgX k X) P).card ≤ 4 * (2 * k + 4) ^ 4 := by
  rw [card_liftS]
  simp only [wdeg_empty]
  obtain ⟨f1, f2, f3, f4, f5⟩ := Q_pow_facts k
  rcases WL_cases hP with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ | h | h
  · calc ∑ ℓ ∈ P1 e, csz k ℓ ≤ ∑ ℓ ∈ P1 e, (2 * k + 4) ^ 2 := sum_le_sum fun ℓ _ => csz_le ℓ
      _ ≤ 2 * (2 * k + 4) ^ 2 := by
        rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ (card_le_two)
      _ ≤ _ := by omega
  · calc ∑ ℓ ∈ P0 e, csz k ℓ ≤ ∑ ℓ ∈ P0 e, (2 * k + 4) ^ 2 := sum_le_sum fun ℓ _ => csz_le ℓ
      _ ≤ 4 * (2 * k + 4) ^ 2 := by
        rw [sum_const, smul_eq_mul]
        apply Nat.mul_le_mul_right
        unfold P0
        calc _ ≤ (insert (Lb.ke e) (e.image (Lb.tk e))).card + 1 := card_insert_le _ _
          _ ≤ (e.image (Lb.tk e)).card + 1 + 1 := by
            have := card_insert_le (Lb.ke e) (e.image (Lb.tk e)); omega
          _ ≤ 4 := by have := card_image_le (s := e) (f := Lb.tk e); rw [hX e he] at this; omega
      _ ≤ _ := by omega
  · obtain ⟨u, hc, -⟩ := chFam_struct hqU chInj_U h
    calc ∑ ℓ ∈ P, csz k ℓ ≤ ∑ ℓ ∈ P, (2 * k + 4) ^ 2 := sum_le_sum fun ℓ _ => csz_le ℓ
      _ ≤ (2 * k + 4) * (2 * k + 4) ^ 2 := by
        rw [sum_const, smul_eq_mul]; apply Nat.mul_le_mul_right; omega
      _ ≤ _ := by omega
  · obtain ⟨o, hc, -⟩ := chFam_struct hqG chInj_G h
    calc ∑ ℓ ∈ P, csz k ℓ ≤ ∑ ℓ ∈ P, (2 * k + 4) ^ 2 := sum_le_sum fun ℓ _ => csz_le ℓ
      _ ≤ (2 * k + 4) ^ 2 * (2 * k + 4) ^ 2 := by
        rw [sum_const, smul_eq_mul]; apply Nat.mul_le_mul_right
        rcases hc with hc | hc <;> rw [hc]
        · omega
        · rw [sq]; nlinarith
      _ ≤ _ := by omega

omit [NeZero n] in
lemma filter_image_card_le_one {f : Finset (Fin n) → Finset (Lb n)} (g : Lb n)
    (hf : ∀ e, g ∈ f e → lbE g = e) : ((X.image f).filter (g ∈ ·)).card ≤ 1 := by
  apply card_le_one.2
  intro A hA B hB
  simp only [mem_filter, mem_image] at hA hB
  obtain ⟨⟨e, -, rfl⟩, hgA⟩ := hA
  obtain ⟨⟨e', -, rfl⟩, hgB⟩ := hB
  rw [← hf e hgA, ← hf e' hgB]

omit [NeZero n] in
/-- Every label lies in at most `3 q^2` pieces. -/
theorem label_mult_le (g : Lb n) : ((WL k X).filter (g ∈ ·)).card ≤ 3 * (2 * k + 4) ^ 2 := by
  have h1 := filter_image_card_le_one (X := X) (f := P1) g (fun e h => by
    rcases mem_P1.1 h with rfl | rfl <;> rfl)
  have h2 := filter_image_card_le_one (X := X) (f := P0) g (fun e h => by
    rcases mem_P0.1 h with rfl | rfl | ⟨u, -, rfl⟩ <;> rfl)
  have h3 := chMult (q := 2 * k + 3) (m := mU X) (φ := φU X) (hqU (k := k))
    (chInj_U (k := k) (X := X)) g
  have h4 := chMult (q := (k + 2) * (2 * k + 3)) (m := mG X) (φ := φG X) (hqG (k := k))
    (chInj_G (k := k) (X := X)) g
  unfold WL
  simp only [filter_union]
  calc _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (card_union_le _ _) _) _
    _ ≤ 1 + 1 + (4 * (2 * k + 3) + 1) + (4 * ((k + 2) * (2 * k + 3)) + 1) := by omega
    _ ≤ _ := by rw [sq]; nlinarith

theorem copy_mult_le (c : Lb n × ℕ × ℕ) :
    ((WX k X).filter (c ∈ ·)).card ≤ 3 * (2 * k + 4) ^ 2 := by
  calc _ ≤ (((WL k X).filter (c.1 ∈ ·)).image (liftS (sgX k X))).card := by
        apply card_le_card
        intro W hW
        simp only [WX, mem_filter, mem_image] at hW ⊢
        obtain ⟨⟨P, hP, rfl⟩, hc⟩ := hW
        exact ⟨P, ⟨hP, (mem_liftS.1 hc).1⟩, rfl⟩
    _ ≤ _ := card_image_le.trans (label_mult_le c.1)

/-! ### The multi-refiner -/

lemma divisible_Lset {L : Finset (Lb n × ℕ × ℕ)} (hL : L ⊆ XlX X)
    (hdiv : MIsDivisible (2 * k + 4) 2 (endsX k X) L) :
    (∀ u, 2 * k + 3 ∣ ((X.filter fun e => (Lb.xe e, 0, 0) ∈ L).filter (u ∈ ·)).card) ∧
      (k + 2) * (2 * k + 3) ∣ (X.filter fun e => (Lb.xe e, 0, 0) ∈ L).card := by
  set Ls := X.filter fun e => (Lb.xe e, 0, 0) ∈ L
  have hLeq : L = Ls.image fun e => (Lb.xe e, 0, 0) := by
    ext c
    simp only [Ls, mem_image, mem_filter]
    constructor
    · intro hc
      obtain ⟨e, he, rfl⟩ := mem_image.1 (hL hc)
      exact ⟨e, ⟨he, hc⟩, rfl⟩
    · rintro ⟨e, ⟨-, hc⟩, rfl⟩; exact hc
  have hinj : Function.Injective fun e : Finset (Fin n) => ((Lb.xe e : Lb n), (0 : ℕ), (0 : ℕ)) :=
    fun a b h => by simpa using h
  refine ⟨?_, ?_⟩
  · intro u
    have h := hdiv {u} (by simp)
    simp only [card_singleton, show 2 * k + 4 - 1 = 2 * k + 3 by omega, show 2 - 1 = 1 by rfl,
      Nat.choose_one_right] at h
    convert h using 1
    rw [mdeg, hLeq, filter_image, card_image_of_injective _ hinj]
    congr 1
    apply filter_congr
    intro e _
    simp [endsX, cpEnds, segAt, segs, singleton_subset_iff]
  · have h := hdiv ∅ (by simp)
    simp only [card_empty, Nat.sub_zero, choose_q_two] at h
    convert h using 1
    rw [mdeg, filter_true_of_mem (fun _ _ => empty_subset _), hLeq,
      card_image_of_injective _ hinj]

/-- **The local refiner is a `K_q^2`-multi-refiner** (`q = 2k + 4`). -/
theorem isMultiRefiner_local (hX : IsRGraph 2 X) (hn : 3 ≤ n) :
    IsMultiRefiner (2 * k + 4) 2 (Cloc k) (endsX k X) (XlX X) (RX k X) (WX k X) := by
  have hXl := XlX_eq (k := k) (X := X)
  have hQ : 1 ≤ 2 * k + 4 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rgraph
    intro c hc
    rw [hXl, RX, ← liftS_union] at hc
    exact seg_card hX hn (mem_liftS.1 hc).1 _ (cpEnds_mem_of_mem_liftS hc)
  · -- disjoint
    rw [hXl, RX]
    apply disjoint_liftS
    rw [Finset.disjoint_left]
    intro g hg hR
    obtain ⟨e, -, rfl⟩ := mem_image.1 hg
    exact xe_not_mem_RL hR
  · intro W hW
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    exact piece_divisible hX hn hP
  · intro W hW
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    rw [hXl, RX, ← liftS_union]
    exact liftS_mono (WL_subset hP)
  · intro W hW
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    exact (piece_card_le hP hX).trans (by unfold Cloc; omega)
  · intro c _
    obtain ⟨f1, f2, -, -, -⟩ := Q_pow_facts k
    exact (copy_mult_le c).trans (by unfold Cloc; omega)
  · intro L hL hdiv
    obtain ⟨hdU, hdG⟩ := divisible_Lset hL hdiv
    set Ls := X.filter fun e => (Lb.xe e, 0, 0) ∈ L with hLs_def
    have hLsX : Ls ⊆ X := filter_subset _ _
    have hLeq : L = liftS (sgX k X) (Ls.image Lb.xe) := by
      ext ⟨ℓ, s, c⟩
      simp only [mem_liftS, mem_image]
      constructor
      · intro hc
        obtain ⟨e, he, h⟩ := mem_image.1 (hL hc)
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨⟨e, mem_filter.2 ⟨he, hc⟩, rfl⟩, ?_, ?_⟩ <;> simp [segs, segAt]
      · rintro ⟨⟨e, he, rfl⟩, hs, hc⟩
        simp only [segs, List.length_singleton, Nat.lt_one_iff] at hs
        subst hs
        simp only [segs, segAt, List.getD_cons_zero, Nat.lt_one_iff] at hc
        subst hc
        exact (mem_filter.1 he).2
    refine ⟨((Ind X).image (pc k X Ls)).image (liftS (sgX k X)), ?_, ∅, empty_subset _,
      mIsDivisible_empty _ _ _, ?_, by simp, ?_⟩
    · apply image_subset_image
      intro P hP
      obtain ⟨α, hα, rfl⟩ := mem_image.1 hP
      exact pc_mem_WL Ls hα
    · intro W hW W' hW' hne
      simp only [coe_image, Set.mem_image, mem_coe] at hW hW'
      obtain ⟨P, ⟨α, hα, rfl⟩, rfl⟩ := hW
      obtain ⟨P', ⟨β, hβ, rfl⟩, rfl⟩ := hW'
      simp only [Function.onFun, id]
      apply disjoint_liftS
      rw [Finset.disjoint_left]
      intro g h1 h2
      apply hne
      rw [pc_unique hLsX hdU hdG hα hβ h1 h2]
    · rw [union_empty, liftS_sup, RX, hLeq, ← liftS_union]
      congr 1
      ext g
      rw [← pc_cover hLsX hdU hdG g]
      simp only [mem_sup, mem_image, id]
      constructor
      · rintro ⟨P, ⟨α, hα, rfl⟩, hg⟩; exact ⟨α, hα, hg⟩
      · rintro ⟨α, hα, hg⟩; exact ⟨_, ⟨α, hα, rfl⟩, hg⟩

end RefinedAbsorption.LocalRefiner
