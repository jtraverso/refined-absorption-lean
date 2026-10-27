module
public import RefinedAbsorption.FlatDown.FlatProof

/-!
# Degree bookkeeping for the flat step

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

`flatStep_deg` is the flat step (`flatStep`) together with an explicit bound on the degree of
every set `S` in the new copies `R`:

  `mdeg R S ≤ ∑_T #{y ∈ RN T : S ⊆ T ∪ endsN T y} + (M + 1) · K · #{(T, W) : S ⊆ T ∪ AW(T, W)}`,

where the first sum is the degree of `S` in the lifted link refiners, `M = fakeModulus q r`,
`K = flatCompCard q r Cl` bounds the size of one completion copy, and `AW(T, W) = Z₀ T W ∪ V(W)`
is the support of the completion of the lifted piece `T * W`.  So the degree of the flat step is
controlled by the degrees of the link refiners and by how often each set lies in the vertex set
`T ∪ Z₀ T W ∪ V(W)` of a lifted piece; the latter is what the placement of the supports
(`RequestProject/Placement/PlacedFlat.lean`) controls.
-/

@[expose] public section

namespace RefinedAbsorption.FlatDown

open Finset RefinedAbsorption.MultiRefiner

section Deg

variable {V E N : Type} [DecidableEq V] [DecidableEq E] [DecidableEq N]
  {ends : E → Finset V} {Z : Finset V} {endsN : Finset V → N → Finset V}

/-- The size bound of one completion copy of a lifted piece. -/
def flatCompCard (q r Cl : ℕ) : ℕ := 2 ^ (q + r + Cl * r) * fakeModulus q r * 2 ^ q

/-- The vertex set of the lifted and completed piece `t = (T, W)`. -/
def pieceSpan (ends : E → Finset V) (Z : Finset V) (endsN : Finset V → N → Finset V)
    (Z₀ : Finset V → Finset (E ⊕ N) → Finset V) (t : Finset V × Finset (E ⊕ N)) : Finset V :=
  t.1 ∪ AW ends Z endsN (Z₀ t.1 t.2) t.1 t.2

theorem compLab_card_le' {q r i Cl M : ℕ} {X : Finset E} {RN : Finset V → Finset N}
    {𝒲 : Finset V → Finset (Finset (E ⊕ N))} {Z₀ : Finset V → Finset (E ⊕ N) → Finset V}
    (hL : LinkRefiners q r i Cl ends Z X endsN RN 𝒲) (hZ₀c : ∀ T W, (Z₀ T W).card = q + r)
    (hM : 0 < M) (hiq : i ≤ q) {t : Finset V × Finset (E ⊕ N)} (ht : t ∈ fI ends Z i X 𝒲) (k : ℕ) :
    (compLab ends Z endsN q r i M (Z₀ t.1 t.2) t.1 t.2 k).card ≤
      2 ^ (q + r + Cl * r) * M * 2 ^ q := by
  obtain ⟨hT, hW⟩ := mem_fI.1 ht
  have hp := link_piece_props hL hT hW
  have hAW : (AW ends Z endsN (Z₀ t.1 t.2) t.1 t.2).card ≤ q + r + Cl * r := by
    refine (AW_card_le (r := r) fun w hw => ?_).trans ?_
    · rw [(hp w hw).2.2]; exact Nat.sub_le _ _
    · rw [hZ₀c]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ ((hL.ref t.1 hT).card_le t.2 hW)) _
  refine (card_compLab_le hM fun Q hQ => ?_).trans ?_
  · refine (card_union_le _ _).trans ?_
    rw [(outParts_card hT).1, (mem_powersetCard.1 hQ).2]
    omega
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by norm_num) hAW))

/-- **The flat step with degree bookkeeping.**  The flat step `flatStep`, with the degree of every
set `S` in the new copies bounded by its degree in the lifted link refiners plus
`(M + 1) · flatCompCard q r Cl` times the number of lifted pieces whose span contains `S`. -/
theorem flatStep_deg {q r i Cl : ℕ} {X : Finset E} {RN : Finset V → Finset N}
    {𝒲 : Finset V → Finset (Finset (E ⊕ N))} {Z₀ : Finset V → Finset (E ⊕ N) → Finset V}
    (hir : i < r) (hrq : r < q) (hXr : MIsRGraph r ends X) (hX : IsFlat i Z ends X)
    (hL : LinkRefiners q r i Cl ends Z X endsN RN 𝒲) (hZ₀ : ∀ T W, Z₀ T W ⊆ Z)
    (hZ₀c : ∀ T W, (Z₀ T W).card = q + r) :
    ∃ R Y : Finset (E ⊕ FLab V E N), ∃ 𝒲' : Finset (Finset (E ⊕ FLab V E N)),
      IsResidualMultiRefiner q r (flatConst q r Cl) (fEnds ends endsN) (X.image Sum.inl) R Y 𝒲' ∧
      IsFlat (i - 1) Z (fEnds ends endsN) Y ∧
      (∀ x, Sum.inl x ∈ Y → x ∈ X ∧ (ends x \ Z).card < i) ∧
      Y ⊆ X.image Sum.inl ∪ R ∧ (∀ c ∈ R, ∀ x, c ≠ Sum.inl x) ∧
      (∀ c ∈ R, ∃ T ∈ outParts ends Z i X, fEnds ends endsN c ⊆ T ∪ Z) ∧
      (∀ S : Finset V, mdeg (fEnds ends endsN) R S ≤
        ∑ T ∈ outParts ends Z i X, ((RN T).filter fun y => S ⊆ T ∪ endsN T y).card +
        (fakeModulus q r + 1) * flatCompCard q r Cl *
          ((fI ends Z i X 𝒲).filter fun t => S ⊆ pieceSpan ends Z endsN Z₀ t).card) ∧
      ∀ S : Finset V, pdeg (fEnds ends endsN) 𝒲' S ≤
        2 * ((fI ends Z i X 𝒲).filter fun t => S ⊆ pieceSpan ends Z endsN Z₀ t).card := by
  obtain ⟨R, Y, 𝒲', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    flatStep_struct hir hrq hXr hX hL hZ₀ hZ₀c
  refine ⟨R, Y, 𝒲', h1, h2, h3, h4, h5, h6, fun S => ?_, h8⟩
  set M := fakeModulus q r with hMdef
  have hM : 0 < M := fakeModulus_pos hrq.le
  set U₁ : Finset (E ⊕ FLab V E N) := (outParts ends Z i X).biUnion fun T =>
    ((RN T).filter fun y => S ⊆ T ∪ endsN T y).image fun y => Sum.inr (Sum.inl (T, y))
  set P := (fI ends Z i X 𝒲).filter fun t => S ⊆ pieceSpan ends Z endsN Z₀ t
  set U₂ : Finset (E ⊕ FLab V E N) := P.biUnion fun t =>
    (range (M + 1)).biUnion fun k => compLab ends Z endsN q r i M (Z₀ t.1 t.2) t.1 t.2 k
  have hsub : R.filter (fun c => S ⊆ fEnds ends endsN c) ⊆ U₁ ∪ U₂ := by
    intro c hc
    obtain ⟨hcR, hS⟩ := mem_filter.1 hc
    rcases h7 c hcR with ⟨T, hT, y, hy, rfl⟩ | ⟨t, ht, k, hk, hck⟩
    · refine mem_union_left _ (mem_biUnion.2 ⟨T, hT, mem_image.2 ⟨y, mem_filter.2 ⟨hy, ?_⟩, rfl⟩⟩)
      exact hS
    · refine mem_union_right _ (mem_biUnion.2 ⟨t, mem_filter.2 ⟨ht, ?_⟩,
        mem_biUnion.2 ⟨k, mem_range.2 (Nat.lt_succ_of_le hk), hck⟩⟩)
      obtain ⟨Q, hQ, j, -, e, he, rfl⟩ := mem_compLab.1 hck
      refine hS.trans ?_
      show e ⊆ t.1 ∪ AW ends Z endsN (Z₀ t.1 t.2) t.1 t.2
      exact (mem_powersetCard.1 (mem_filter.1 he).1).1.trans
        (union_subset_union subset_rfl (mem_powersetCard.1 hQ).1)
  have hU₁ : U₁.card ≤ ∑ T ∈ outParts ends Z i X,
      ((RN T).filter fun y => S ⊆ T ∪ endsN T y).card :=
    card_biUnion_le.trans (sum_le_sum fun T _ => card_image_le)
  have hU₂ : U₂.card ≤ (M + 1) * flatCompCard q r Cl * P.card := by
    refine card_biUnion_le.trans ?_
    calc ∑ t ∈ P, ((range (M + 1)).biUnion fun k =>
          compLab ends Z endsN q r i M (Z₀ t.1 t.2) t.1 t.2 k).card
        ≤ ∑ _t ∈ P, (M + 1) * flatCompCard q r Cl := by
          refine sum_le_sum fun t ht => card_biUnion_le.trans ?_
          calc ∑ k ∈ range (M + 1), (compLab ends Z endsN q r i M (Z₀ t.1 t.2) t.1 t.2 k).card
              ≤ ∑ _k ∈ range (M + 1), flatCompCard q r Cl :=
                sum_le_sum fun k _ => compLab_card_le' hL hZ₀c hM (by omega) (mem_filter.1 ht).1 k
            _ = _ := by rw [sum_const, card_range, smul_eq_mul]
      _ = _ := by rw [sum_const, smul_eq_mul]; ring
  calc mdeg (fEnds ends endsN) R S ≤ (U₁ ∪ U₂).card := card_le_card hsub
    _ ≤ U₁.card + U₂.card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add hU₁ hU₂

end Deg

end RefinedAbsorption.FlatDown
