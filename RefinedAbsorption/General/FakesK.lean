module
public import RefinedAbsorption.General.LocalK

/-!
# Fake edges for the new copies of a local refiner, uniformity `k`

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (fake edges and the Partial Clique
Embedding Lemma 5.2 inside a reserve).  Lean formalization: Juan Pablo Traverso Gianini,
Apache-2.0.

`fakePiece_refinerK` and `fakeStageK` are `fakePiece_refiner` and `fakeStage`
(`FlatOmni/Fakes.lean`) in uniformity `k`: every new copy of a local refiner is replaced by a fake
edge whose auxiliary vertices are placed in the reserve `P`; the new edges form a simple
`k`-graph `F` all of whose edges meet `P`.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.RefineDown
  RefinedAbsorption.FlatDown RefinedAbsorption.FlatOmni

section Pieces

variable {n : ℕ} {E : Type} [DecidableEq E]

/-- **Replacing new copies by fake edges keeps a refiner.**  If every new copy `c ∈ R` is replaced
by a graph `NE c` (pairwise disjoint for distinct copies, of at most `B₀` edges, and behaving like
the edge `ends c` modulo divisibility), the fake pieces form a complete multi-refiner of `X` with
new edges `⋃_c NE c`. -/
theorem fakePiece_refinerK {q k C B₀ : ℕ} {ends : E → Finset (Fin n)} {X R : Finset E}
    {𝒲 : Finset (Finset E)} {NE : E → Finset (Finset (Fin n))}
    (h : IsMultiRefiner q k C ends X R 𝒲)
    (hNE : ∀ c ∈ R, ∀ c' ∈ R, c ≠ c' → Disjoint (NE c) (NE c'))
    (hNEr : ∀ c ∈ R, ∀ f ∈ NE c, f.card = k) (hNEc : ∀ c ∈ R, (NE c).card ≤ B₀)
    (hNEdiv : ∀ c ∈ R, ∀ S : Finset (Fin n), S.card < k →
      ((deg (NE c) S : ℕ) : ZMod ((q - S.card).choose (k - S.card))) =
        if S ⊆ ends c then 1 else 0) :
    IsMultiRefiner q k (C * (1 + B₀)) (Sum.elim ends id) (X.image Sum.inl)
      ((R.biUnion NE).image Sum.inr) (𝒲.image (fakePiece X R NE)) := by
  have hmemR : ∀ {f c}, c ∈ R → f ∈ NE c → ∀ {W : Finset E},
      Sum.inr f ∈ fakePiece X R NE W → c ∈ W := by
    intro f c hc hf W hW
    obtain ⟨c', hc'W, hc'R, hfc'⟩ := inr_mem_fakePiece.1 hW
    by_cases hcc : c = c'
    · rw [hcc]; exact hc'W
    · exact absurd hfc' (disjoint_left.1 (hNE c hc c' hc'R hcc) hf)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rcases mem_union.1 hy with hy | hy
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
      exact h.rgraph x (mem_union_left _ hx)
    · obtain ⟨f, hf, rfl⟩ := mem_image.1 hy
      obtain ⟨c, hc, hfc⟩ := mem_biUnion.1 hf
      exact hNEr c hc f hfc
  · rw [disjoint_left]
    intro y hy hy'
    obtain ⟨x, -, rfl⟩ := mem_image.1 hy
    obtain ⟨f, -, hf⟩ := mem_image.1 hy'
    exact Sum.inr_ne_inl hf
  · intro W' hW' S hS
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    rw [mdeg_fakePiece hNE ends S, ← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [sum_congr rfl fun c hc => hNEdiv c (mem_filter.1 hc).2 S hS, sum_boole]
    have h1 : ((W.filter (· ∈ R)).filter fun c => S ⊆ ends c) =
        (W.filter (· ∈ R)).filter fun c => S ⊆ ends c := rfl
    have h2 : (((W.filter (· ∈ R)).filter fun c => S ⊆ ends c).card : ℕ) =
        mdeg ends (W.filter (· ∈ R)) S := rfl
    rw [h2, ← Nat.cast_add, ← mdeg_split h.disjoint (h.subset W hW), ZMod.natCast_eq_zero_iff]
    exact h.divisible W hW S hS
  · intro W' hW' y hy
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    rcases y with x | f
    · obtain ⟨-, hx⟩ := inl_mem_fakePiece.1 hy
      exact mem_union_left _ (mem_image_of_mem _ hx)
    · obtain ⟨c, -, hcR, hfc⟩ := inr_mem_fakePiece.1 hy
      exact mem_union_right _ (mem_image_of_mem _ (mem_biUnion.2 ⟨c, hcR, hfc⟩))
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    unfold fakePiece
    refine (card_union_le _ _).trans ?_
    have h1 : ((W.filter (· ∈ X)).image (Sum.inl : E → E ⊕ Finset (Fin n))).card ≤ W.card :=
      card_image_le.trans (card_le_card (filter_subset _ _))
    have h2 : ((W.filter (· ∈ R)).biUnion fun c =>
        (NE c).image (Sum.inr : Finset (Fin n) → E ⊕ Finset (Fin n))).card ≤ W.card * B₀ := by
      refine card_biUnion_le.trans ?_
      refine (sum_le_sum fun c hc => card_image_le.trans (hNEc c (mem_filter.1 hc).2)).trans ?_
      rw [sum_const, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))
    have h3 := h.card_le W hW
    have : W.card + W.card * B₀ ≤ C * (1 + B₀) := by nlinarith
    omega
  · intro y hy
    refine le_trans ?_ (Nat.le_mul_of_pos_right _ (by omega) |>.trans' le_rfl)
    rcases mem_union.1 hy with hy | hy
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
      refine le_trans (card_le_card (t := (𝒲.filter fun W => x ∈ W).image (fakePiece X R NE))
        ?_) (card_image_le.trans (h.mult_le x (mem_union_left _ hx)))
      · intro W' hW'
        obtain ⟨hW', hxW'⟩ := mem_filter.1 hW'
        obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
        exact mem_image.2 ⟨W, mem_filter.2 ⟨hW, (inl_mem_fakePiece.1 hxW').1⟩, rfl⟩
    · obtain ⟨f, hf, rfl⟩ := mem_image.1 hy
      obtain ⟨c, hc, hfc⟩ := mem_biUnion.1 hf
      refine le_trans (card_le_card (t := (𝒲.filter fun W => c ∈ W).image (fakePiece X R NE))
        ?_) (card_image_le.trans (h.mult_le c (mem_union_right _ hc)))
      · intro W' hW'
        obtain ⟨hW', hfW'⟩ := mem_filter.1 hW'
        obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
        exact mem_image.2 ⟨W, mem_filter.2 ⟨hW, hmemR hc hfc hfW'⟩, rfl⟩
  · intro L' hL' hdiv
    set L₀ := X.filter fun x => Sum.inl x ∈ L' with hL₀
    have hL'eq : L' = L₀.image Sum.inl := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := mem_image.1 (hL' hy)
        exact mem_image_of_mem _ (mem_filter.2 ⟨hx, hy⟩)
      · intro hy
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
        exact (mem_filter.1 hx).2
    have hdiv₀ : MIsDivisible q k ends L₀ := by
      intro S hS
      have := hdiv S hS
      rw [hL'eq, mdeg_image_eq (A := L₀) (fun c _ => rfl) Sum.inl_injective.injOn subset_rfl]
        at this
      exact this
    obtain ⟨𝒰, h𝒰, Res, hRes, -, hpw, -, heq⟩ := h.decomp L₀ (filter_subset _ _) hdiv₀
    have hRes0 : Res = ∅ := subset_empty.1 hRes
    rw [hRes0, union_empty] at heq
    refine ⟨𝒰.image (fakePiece X R NE), image_subset_image h𝒰, ∅, empty_subset _,
      mIsDivisible_empty _ _ _, ?_, by simp, ?_⟩
    · intro A hA B hB hAB
      obtain ⟨W₁, hW₁, rfl⟩ := mem_image.1 (mem_coe.1 hA)
      obtain ⟨W₂, hW₂, rfl⟩ := mem_image.1 (mem_coe.1 hB)
      have hne : W₁ ≠ W₂ := fun h12 => hAB (by rw [h12])
      have hd := hpw (mem_coe.2 hW₁) (mem_coe.2 hW₂) hne
      simp only [Function.onFun, id] at hd ⊢
      rw [disjoint_left]
      intro y hy1 hy2
      rcases y with x | f
      · exact disjoint_left.1 hd (inl_mem_fakePiece.1 hy1).1 (inl_mem_fakePiece.1 hy2).1
      · obtain ⟨c, hcW, hcR, hfc⟩ := inr_mem_fakePiece.1 hy1
        exact disjoint_left.1 hd hcW (hmemR hcR hfc hy2)
    · rw [union_empty]
      ext y
      simp only [mem_sup, mem_image, id, mem_union]
      have hsup : ∀ c, c ∈ R ∪ L₀ ↔ ∃ W ∈ 𝒰, c ∈ W := by
        intro c
        rw [← heq, mem_sup]
        rfl
      rcases y with x | f
      · constructor
        · rintro ⟨_, ⟨W, hW, rfl⟩, hxW⟩
          obtain ⟨hxW, hxX⟩ := inl_mem_fakePiece.1 hxW
          have := (hsup x).2 ⟨W, hW, hxW⟩
          rcases mem_union.1 this with h1 | h1
          · exact absurd hxX (disjoint_right.1 h.disjoint h1)
          · right; rw [hL'eq]; exact mem_image_of_mem _ h1
        · rintro (⟨f, -, hf⟩ | hx)
          · exact absurd hf (by simp)
          · rw [hL'eq] at hx
            obtain ⟨x', hx', hxx'⟩ := mem_image.1 hx
            obtain rfl := Sum.inl_injective hxx'
            obtain ⟨W, hW, hxW⟩ := (hsup x').1 (mem_union_right _ hx')
            exact ⟨_, ⟨W, hW, rfl⟩, inl_mem_fakePiece.2 ⟨hxW, (mem_filter.1 hx').1⟩⟩
      · constructor
        · rintro ⟨_, ⟨W, hW, rfl⟩, hfW⟩
          obtain ⟨c, -, hcR, hfc⟩ := inr_mem_fakePiece.1 hfW
          exact Or.inl ⟨f, mem_biUnion.2 ⟨c, hcR, hfc⟩, rfl⟩
        · rintro (⟨f', hf', hff'⟩ | hf)
          · obtain rfl := Sum.inr_injective hff'
            obtain ⟨c, hcR, hfc⟩ := mem_biUnion.1 hf'
            obtain ⟨W, hW, hcW⟩ := (hsup c).1 (mem_union_left _ hcR)
            exact ⟨_, ⟨W, hW, rfl⟩, inr_mem_fakePiece.2 ⟨c, hcW, hcR, hfc⟩⟩
          · rw [hL'eq] at hf
            obtain ⟨x, -, hx⟩ := mem_image.1 hf
            exact absurd hx (by simp)

end Pieces

end RefinedAbsorption.General
