module
public import RequestProject.Faithful2024.Theorem38Two
public import RequestProject.Original2024.FlatOne

/-!
# Theorem 3.8 of arXiv:2402.17855v1, faithful form, `r = 1`

For `r = 1` the edges are single vertices, `K_q^1`-divisibility of a multigraph only depends on
its number of copies, and `X` may have multiplicity up to `M(q,1) = q`.  As in the article
("splitting the multiple copies of singletons of `X` into separate vertices, applying the
construction, and then identifying the copies back"), we

1. place the `m = |X|` copies of `X` on distinct auxiliary vertices of `Fin N`, `N = 4qm + m + 1`,
   and build the chain refiner there (`Original2024.hostChainPool`);
2. move every copy back: the copy of `x ∈ X` to its vertex `ends x`, every new copy to a fixed
   vertex `y₀ ∈ Y` (`residual_one_changeEnds`: for `r = 1` the refiner properties do not depend on
   the positions of the copies);
3. relabel the copies of `X` by their original labels (`Dense.residual_relabel`).

Every new copy then lies on `y₀ ∈ Y`, i.e. it is `0`-flat to `Y`.
-/

@[expose] public section

namespace RefinedAbsorption.Faithful2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.RefineDown

section ChangeEnds

variable {V V' E : Type*} [DecidableEq V] [DecidableEq V'] [DecidableEq E]

/-- For `r = 1`, divisibility only depends on the number of copies. -/
theorem mIsDivisible_one_iff {q : ℕ} (ends : E → Finset V) (ends' : E → Finset V') (G : Finset E) :
    MIsDivisible q 1 ends G ↔ MIsDivisible q 1 ends' G := by
  have k1 : ∀ S : Finset V, S.card < 1 → mdeg ends G S = G.card := by
    intro S hS
    have : S = ∅ := card_eq_zero.1 (by omega)
    subst this
    unfold mdeg
    rw [filter_true_of_mem (fun _ _ => empty_subset _)]
  have k2 : ∀ S : Finset V', S.card < 1 → mdeg ends' G S = G.card := by
    intro S hS
    have : S = ∅ := card_eq_zero.1 (by omega)
    subst this
    unfold mdeg
    rw [filter_true_of_mem (fun _ _ => empty_subset _)]
  constructor
  · intro h S hS
    have := h ∅ (by simp)
    rw [k2 S hS]
    rw [k1 ∅ (by simp)] at this
    rw [show S.card = 0 by omega]
    simpa using this
  · intro h S hS
    have := h ∅ (by simp)
    rw [k1 S hS]
    rw [k2 ∅ (by simp)] at this
    rw [show S.card = 0 by omega]
    simpa using this

/-- **For `r = 1`, a residual multi-refiner does not depend on the positions of its copies.** -/
theorem residual_one_changeEnds {q C : ℕ} {ends : E → Finset V} {ends' : E → Finset V'}
    {X R Y : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsResidualMultiRefiner q 1 C ends X R Y 𝒲)
    (h' : ∀ c ∈ X ∪ R, (ends' c).card = 1) : IsResidualMultiRefiner q 1 C ends' X R Y 𝒲 := by
  refine ⟨h', h.disjoint, fun W hW => (mIsDivisible_one_iff ends ends' W).1 (h.divisible W hW),
    h.subset, h.card_le, h.mult_le, fun L hL hdiv => ?_⟩
  obtain ⟨𝒰, h𝒰, Res, hRes, hdivRes, h1, h2, h3⟩ :=
    h.decomp L hL ((mIsDivisible_one_iff ends ends' L).2 hdiv)
  exact ⟨𝒰, h𝒰, Res, hRes, (mIsDivisible_one_iff ends ends' Res).1 hdivRes, h1, h2, h3⟩

end ChangeEnds

theorem image_filter_mem_image {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (W X : Finset α) :
    (W.image f).filter (· ∈ X.image f) = (W.filter (· ∈ X)).image f := by
  ext c
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx'⟩⟩
    exact ⟨x, ⟨hx, (hf hxx') ▸ hx'⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hxX⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hxX, rfl⟩⟩

set_option maxHeartbeats 1000000 in
/-- **Theorem 3.8 of arXiv:2402.17855v1 (Multi-Refiner Theorem), faithful conclusion, `r = 1`.** -/
theorem theorem_3_8_conclusion_one {q : ℕ} (hq : 2 ≤ q) : Theorem_3_8_conclusion q 1 := by
  refine ⟨16 * q + 3 * q + 3, by omega, ?_⟩
  intro n E _ ends X hXr hmult hCn Y hY
  have hY3 : n ≤ 3 * Y.card := by
    have : (n : ℝ) ≤ 3 * Y.card := by linarith
    exact_mod_cast this
  obtain ⟨y₀, hy₀⟩ : Y.Nonempty := card_pos.1 (by omega)
  set m := X.card with hm
  set N := 4 * q * m + m + 1 with hN
  -- the auxiliary positions of the copies of `X`
  let σ : E → Fin N := fun x =>
    if h : x ∈ X then ⟨(X.equivFin ⟨x, h⟩).1, by have := (X.equivFin ⟨x, h⟩).2; omega⟩
    else ⟨0, by omega⟩
  have hσ : ∀ x ∈ X, ∀ y ∈ X, σ x = σ y → x = y := by
    intro x hx y hy hxy
    simp only [σ, dif_pos hx, dif_pos hy, Fin.mk.injEq] at hxy
    have := X.equivFin.injective (Fin.ext hxy)
    exact congrArg Subtype.val this
  set Xa : Finset (Finset (Fin N)) := X.image fun x => {σ x} with hXa
  have hXac : Xa.card = m := by
    rw [hXa, card_image_of_injOn]
    intro x hx y hy hxy
    exact hσ x hx y hy (singleton_injective hxy)
  set G : Finset (Finset (Fin N)) := univ.image fun v => {v} with hG
  have hGr : IsRGraph 1 G := by
    intro e he
    obtain ⟨v, -, rfl⟩ := mem_image.1 he
    exact card_singleton v
  have hXaG : Xa ⊆ G := by
    intro e he
    obtain ⟨x, -, rfl⟩ := mem_image.1 he
    exact mem_image.2 ⟨σ x, mem_univ _, rfl⟩
  have hGc : G.card = N := by
    rw [hG, card_image_of_injective _ singleton_injective, card_univ, Fintype.card_fin]
  obtain ⟨Ra, 𝒲a, hRa, -, honea, -, h𝒲c⟩ :=
    Original2024.hostChainPool hq N G Xa hGr hXaG (by rw [hXac, hGc]; omega)
  have hma : IsResidualMultiRefiner q 1 (8 * q) id Xa Ra ∅ 𝒲a :=
    Original2024.IsRefinedRefiner.toMulti hRa
  -- move the copies back
  let sel : Finset (Fin N) → Prop := fun e => ∃ x ∈ X, ({σ x} : Finset (Fin N)) = e
  let endsA : Finset (Fin N) → Finset (Fin n) := fun e =>
    @dite _ (sel e) (Classical.dec _) (fun h => ends h.choose) (fun _ => {y₀})
  have hendsA1 : ∀ e, (endsA e).card = 1 := by
    intro e
    simp only [endsA]
    split_ifs with h
    · exact hXr _ h.choose_spec.1
    · exact card_singleton _
  have hmb := residual_one_changeEnds hma (ends' := endsA) (fun c _ => hendsA1 c)
  -- relabel
  let ψ : Finset (Fin N) → E ⊕ Finset (Fin N) := fun e =>
    @dite _ (sel e) (Classical.dec _) (fun h => Sum.inl h.choose) (fun _ => Sum.inr e)
  let ends₂ : E ⊕ Finset (Fin N) → Finset (Fin n) := Sum.elim ends fun _ => {y₀}
  have hψends : ∀ e, ends₂ (ψ e) = endsA e := by
    intro e
    simp only [ψ, endsA]
    split_ifs <;> rfl
  have hψinj : Function.Injective ψ := by
    intro e e' he
    simp only [ψ] at he
    split_ifs at he with h h'
    · have h1 := h.choose_spec.2
      have h2 := h'.choose_spec.2
      rw [Sum.inl.injEq] at he
      rw [← h1, ← h2, he]
    all_goals first
      | exact absurd he Sum.inl_ne_inr
      | exact absurd he Sum.inr_ne_inl
      | exact Sum.inr_injective he
  have hψX : ∀ x ∈ X, ψ {σ x} = Sum.inl x := by
    intro x hx
    have hs : sel {σ x} := ⟨x, hx, rfl⟩
    simp only [ψ, dif_pos hs]
    congr 1
    have := hs.choose_spec
    exact hσ _ this.1 x hx (singleton_injective this.2)
  have hXimg : Xa.image ψ = X.image Sum.inl := by
    rw [hXa, image_image]
    exact image_congr fun x hx => hψX x hx
  have hmc := residual_relabel hmb ψ ends₂ (fun c _ => hψends c) hψinj.injOn
    (empty_subset _)
  rw [image_empty, hXimg] at hmc
  have hR₂ : ∀ c ∈ Ra.image ψ, ends₂ c = {y₀} := by
    intro c hc
    obtain ⟨e, he, rfl⟩ := mem_image.1 hc
    have hns : ¬ sel e := by
      rintro ⟨x, hx, rfl⟩
      exact disjoint_left.1 hRa.disjoint (mem_image.2 ⟨x, hx, rfl⟩) he
    simp only [ψ, dif_neg hns]
    rfl
  have hone : ∀ W ∈ 𝒲a.image (image ψ), (W.filter (· ∈ X.image Sum.inl)).card ≤ 1 := by
    intro W hW
    obtain ⟨W₀, hW₀, rfl⟩ := mem_image.1 hW
    rw [← hXimg, image_filter_mem_image hψinj]
    exact card_image_le.trans (honea W₀ hW₀)
  refine ⟨E ⊕ Finset (Fin N), inferInstance, Sum.inl, ends₂, Ra.image ψ, 𝒲a.image (image ψ),
    Sum.inl_injective, fun c => rfl,
    isMultiRefinerF_of_residual hmc (fun _ _ => subset_univ _) hone,
    (isCRefinedMultiFamily_of_residual hmc).mono (by omega), ?_, ?_⟩
  · -- the refinement degree: only the empty set is an `(r-1)`-set
    have hpd : ∀ S : Finset (Fin n), S.card = 1 - 1 →
        pdeg ends₂ (𝒲a.image (image ψ)) S ≤ 3 * q * m :=
      fun S _ => (card_filter_le _ _).trans (card_image_le.trans (hXac ▸ h𝒲c))
    have hmr := mrefDeg_le_of (r := 1) hpd le_rfl
    have hD : (m : ℝ) ≤ bigDelta 1 ends X := by
      refine le_trans ?_ (le_max_left _ _)
      have h0 : mdeg ends X ∅ ≤ mmaxDeg 1 ends X :=
        mdeg_le_mmaxDeg le_rfl ends X ∅ (by simp)
      have h1 : mdeg ends X ∅ = m := by
        unfold mdeg; rw [filter_true_of_mem (fun _ _ => empty_subset _)]
      rw [h1] at h0
      exact_mod_cast h0
    have hΔ0 : (0 : ℝ) ≤ bigDelta 1 ends X := le_trans (Nat.cast_nonneg _) hD
    calc (mrefDeg 1 ends₂ (𝒲a.image (image ψ)) : ℝ) ≤ ((3 * q * m : ℕ) : ℝ) := by
          exact_mod_cast hmr
      _ = (3 * q : ℝ) * m := by push_cast; ring
      _ ≤ (3 * q : ℝ) * bigDelta 1 ends X := by gcongr
      _ ≤ ((16 * q + 3 * q + 3 : ℕ) : ℝ) * bigDelta 1 ends X := by
          gcongr
          push_cast; linarith
  · intro c hc
    rw [hR₂ c hc]
    simp [hy₀]

/-- **Theorem 3.8 of arXiv:2402.17855v1**, faithful conclusion, for all `q > r ≥ 1` (proved
outright). -/
theorem theorem_3_8_conclusion : ∀ q r : ℕ, 1 ≤ r → r < q → Theorem_3_8_conclusion q r := by
  intro q r hr hrq
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    exact theorem_3_8_conclusion_one (by omega)
  · exact theorem_3_8_conclusion_two_le h hrq

/-- **Theorem 3.8 of arXiv:2402.17855v1 (Multi-Refiner Theorem)**, in the inductive form of the
article (*suppose Theorem 3.7 holds for all `r' ∈ [r-1]`*).  The hypothesis is not needed: the
conclusion is `theorem_3_8_conclusion`. -/
theorem theorem_3_8 : ∀ q r : ℕ, 1 ≤ r → r < q → Theorem_3_8_for q r :=
  fun q r hr hrq _ => theorem_3_8_conclusion q r hr hrq

end RefinedAbsorption.Faithful2024
