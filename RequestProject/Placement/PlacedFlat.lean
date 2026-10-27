module
public import RequestProject.FlatDown.FlatDegree
public import RequestProject.FlatDown.LinkAccounting
public import RequestProject.Placement.MultiEmbed

/-!
# The flat step in `Fin n` with placed completion supports

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, Lemma 5.2).  Lean
formalization: Juan Pablo Traverso Gianini, Apache-2.0.

The flat step (`FlatDown.flatStep`) completes every lifted link piece `T * W` with cliques on a
support `Z₀ T W ∪ V(W)`, where `Z₀ T W ⊆ Z` is a set of `q + r` reserve vertices.  Here the
supports `Z₀ T W` are **placed with the Partial Clique Embedding Lemma inside the reserve**
(`reserveCliqueEmbedding`): the pieces `(T, W)` are gadgets with roots `T ∪ V(W)`, no edges, and
`q + r` auxiliary vertices, placed inside `Z`.

`placedFlatStep`: if the root sets `T ∪ V(W)` of the lifted pieces are not too dense compared to
`Z` (every `j`-set, `j ≤ r - 1`, lies in at most `D · |Z|^(r-1-j)` of them) and `Cs · D ≤ |Z|`,
then the flat step can be carried out so that every `(r-1)`-set `S` has degree

  `mdeg R S ≤ (degree of S in the lifted link refiners) + Cs' · D`

in the new copies, with `Cs, Cs'` depending only on `q`, `r` and the link constant `Cl`.  The
remaining input is the degree control of the link refiners themselves (and the density of their
pieces), which is the induction on uniformity of the refine-down argument.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown

section

variable {n : ℕ} {E N : Type} [DecidableEq E] [DecidableEq N]

/-- The roots of the lifted piece `t = (T, W)`: the outside part `T` and the vertices of the
link copies in `W`. -/
def flatRoots (ends : E → Finset (Fin n)) (Z : Finset (Fin n))
    (endsN : Finset (Fin n) → N → Finset (Fin n)) (t : Finset (Fin n) × Finset (E ⊕ N)) :
    Finset (Fin n) :=
  t.1 ∪ t.2.biUnion (lE ends Z endsN t.1)

theorem flatRoots_card_le {q r i Cl : ℕ} {ends : E → Finset (Fin n)} {Z : Finset (Fin n)}
    {endsN : Finset (Fin n) → N → Finset (Fin n)} {X : Finset E}
    {RN : Finset (Fin n) → Finset N} {𝒲 : Finset (Fin n) → Finset (Finset (E ⊕ N))}
    (hir : i < r) (hL : LinkRefiners q r i Cl ends Z X endsN RN 𝒲)
    {t : Finset (Fin n) × Finset (E ⊕ N)} (ht : t ∈ fI ends Z i X 𝒲) :
    (flatRoots ends Z endsN t).card ≤ r + Cl * r := by
  obtain ⟨hT, hW⟩ := mem_fI.1 ht
  have hp := link_piece_props hL hT hW
  refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · rw [(outParts_card hT).1]; exact hir.le
  · refine card_biUnion_le.trans ?_
    calc ∑ w ∈ t.2, (lE ends Z endsN t.1 w).card ≤ ∑ _w ∈ t.2, r :=
          sum_le_sum fun w hw => by rw [(hp w hw).2.2]; exact Nat.sub_le _ _
      _ = t.2.card * r := by rw [sum_const, smul_eq_mul]
      _ ≤ Cl * r := Nat.mul_le_mul_right _ ((hL.ref t.1 hT).card_le t.2 hW)

theorem flatRoots_card_ge {q r i Cl : ℕ} {ends : E → Finset (Fin n)} {Z : Finset (Fin n)}
    {endsN : Finset (Fin n) → N → Finset (Fin n)} {X : Finset E}
    {RN : Finset (Fin n) → Finset N} {𝒲 : Finset (Fin n) → Finset (Finset (E ⊕ N))}
    (hir : i < r) (hL : LinkRefiners q r i Cl ends Z X endsN RN 𝒲)
    {t : Finset (Fin n) × Finset (E ⊕ N)} (ht : t ∈ fI ends Z i X 𝒲) (hne : t.2.Nonempty) :
    r ≤ (flatRoots ends Z endsN t).card := by
  obtain ⟨hT, hW⟩ := mem_fI.1 ht
  have hp := link_piece_props hL hT hW
  obtain ⟨w, hw⟩ := hne
  obtain ⟨hTc, hTZ⟩ := outParts_card hT
  have hsub : t.1 ∪ lE ends Z endsN t.1 w ⊆ flatRoots ends Z endsN t :=
    union_subset_union subset_rfl (subset_biUnion_of_mem _ hw)
  refine le_trans ?_ (card_le_card hsub)
  rw [card_union_of_disjoint (disjoint_of_subset_right (hp w hw).2.1 hTZ), hTc, (hp w hw).2.2]
  omega

/-- **The flat step in `Fin n` with placed completion supports.**  For `i < r < q` and a link
constant `Cl` there are constants `Cs, Cs'` such that: if `X` is an `i`-flat `r`-multigraph on
`Fin n` with respect to the reserve `Z` (`|Z| ≥ q + r`), the links of its outside `i`-sets have
`K_{q-i}^{r-i}`-multi-refiners with constant `Cl` inside `Z` whose pieces are nonempty, the root
sets of the lifted pieces are not too dense compared to `Z` (every `j`-set lies in at most
`D · |Z|^(r-1-j)` of them) and `Cs · D ≤ |Z|`, then `X` has a residual `K_q^r`-refiner as in
`flatStep` (residue `(i-1)`-flat and inside `X ∪ R`, new copies local) such that every
`(r-1)`-set has degree at most `(its degree in the lifted link refiners) + Cs' · D` in the new
copies. -/
theorem placedFlatStep (q r i Cl : ℕ) (hir : i < r) (hrq : r < q) :
    ∃ Cs Cs' : ℕ, 0 < Cs ∧ ∀ (n : ℕ) {E N : Type} [DecidableEq E] [DecidableEq N]
      (ends : E → Finset (Fin n)) (Z : Finset (Fin n))
      (endsN : Finset (Fin n) → N → Finset (Fin n)) (X : Finset E)
      (RN : Finset (Fin n) → Finset N) (𝒲 : Finset (Fin n) → Finset (Finset (E ⊕ N))) (D : ℕ),
      MIsRGraph r ends X → IsFlat i Z ends X → LinkRefiners q r i Cl ends Z X endsN RN 𝒲 →
      (∀ T ∈ outParts ends Z i X, ∀ W ∈ 𝒲 T, W.Nonempty) →
      q + r ≤ Z.card → Cs ≤ Z.card →
      (∀ J : Finset (Fin n), J.card ≤ r - 1 →
        ((fI ends Z i X 𝒲).filter fun t => J ⊆ flatRoots ends Z endsN t).card ≤
          D * Z.card ^ (r - 1 - J.card)) →
      ∃ R Y : Finset (E ⊕ FLab (Fin n) E N), ∃ 𝒲' : Finset (Finset (E ⊕ FLab (Fin n) E N)),
        IsResidualMultiRefiner q r (flatConst q r Cl) (fEnds ends endsN) (X.image Sum.inl)
          R Y 𝒲' ∧
        IsFlat (i - 1) Z (fEnds ends endsN) Y ∧
        (∀ x, Sum.inl x ∈ Y → x ∈ X ∧ (ends x \ Z).card < i) ∧
        Y ⊆ X.image Sum.inl ∪ R ∧ (∀ c ∈ R, ∀ x, c ≠ Sum.inl x) ∧
        (∀ c ∈ R, ∃ T ∈ outParts ends Z i X, fEnds ends endsN c ⊆ T ∪ Z) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (fEnds ends endsN) R S ≤
          ∑ T ∈ outParts ends Z i X, ((RN T).filter fun y => S ⊆ T ∪ endsN T y).card +
            Cs' * D) ∧
        ∀ S : Finset (Fin n), S.card = r - 1 → pdeg (fEnds ends endsN) 𝒲' S ≤ Cs' * D := by
  obtain ⟨C, hC, hemb⟩ := multiCliqueEmbedding r (q + r) (r + Cl * r)
  refine ⟨C, (fakeModulus q r + 1) * flatCompCard q r Cl * C + 2 * C, hC, ?_⟩
  intro n E N _ _ ends Z endsN X RN 𝒲 D hXr hX hL hne hZq hCD hroot
  set I := fI ends Z i X 𝒲 with hI
  have hwf : ∀ t ∈ I, GadgetWF r (r + Cl * r) (flatRoots ends Z endsN t)
      (∅ : Finset (Finset (Fin n ⊕ Fin (q + r)))) := by
    intro t ht
    obtain ⟨hT, hW⟩ := mem_fI.1 ht
    refine ⟨flatRoots_card_le hir hL ht,
      le_trans (Nat.sub_le r 1) (flatRoots_card_ge hir hL ht (hne t.1 hT t.2 hW)),
      by simp, by simp, by simp⟩
  obtain ⟨Φ, hval, hrange, hcount, -⟩ := hemb n I (flatRoots ends Z endsN)
    (fun _ => ∅) Z D hwf hCD hroot
  obtain ⟨Zd, hZd, hZdc⟩ := exists_subset_card_eq hZq
  classical
  set Z₀ : Finset (Fin n) → Finset (E ⊕ N) → Finset (Fin n) :=
    fun T W => if (T, W) ∈ I then auxImage (Φ (T, W)) else Zd with hZ₀def
  have hZ₀ : ∀ T W, Z₀ T W ⊆ Z := by
    intro T W
    simp only [hZ₀def]
    split_ifs with h
    · intro v hv
      obtain ⟨p, -, rfl⟩ := mem_image.1 hv
      exact hrange _ h p
    · exact hZd
  have hZ₀c : ∀ T W, (Z₀ T W).card = q + r := by
    intro T W
    simp only [hZ₀def]
    split_ifs with h
    · unfold auxImage
      rw [card_image_of_injective _ (hval _ h).1, card_univ, Fintype.card_fin]
    · exact hZdc
  obtain ⟨R, Y, 𝒲', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    flatStep_deg (Z₀ := Z₀) hir hrq hXr hX hL hZ₀ hZ₀c
  have hfilt : ∀ S : Finset (Fin n), (I.filter fun t => S ⊆ pieceSpan ends Z endsN Z₀ t) =
      I.filter fun t => S ⊆ flatRoots ends Z endsN t ∪ auxImage (Φ t) := by
    intro S
    refine filter_congr fun t ht => ?_
    have hZt : Z₀ t.1 t.2 = auxImage (Φ t) := by
      simp only [hZ₀def, Prod.mk.eta, if_pos ht]
    have : pieceSpan ends Z endsN Z₀ t = flatRoots ends Z endsN t ∪ auxImage (Φ t) := by
      unfold pieceSpan flatRoots AW
      rw [hZt]
      ext v
      simp only [mem_union]
      tauto
    rw [this]
  refine ⟨R, Y, 𝒲', h1, h2, h3, h4, h5, h6, fun S hS => (h7 S).trans ?_, fun S hS => ?_⟩
  · refine Nat.add_le_add_left ?_ _
    rw [hfilt]
    calc (fakeModulus q r + 1) * flatCompCard q r Cl *
          (I.filter fun t => S ⊆ flatRoots ends Z endsN t ∪ auxImage (Φ t)).card
        ≤ (fakeModulus q r + 1) * flatCompCard q r Cl * (C * D) :=
          Nat.mul_le_mul_left _ (hcount S hS)
      _ = (fakeModulus q r + 1) * flatCompCard q r Cl * C * D := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · refine (h8 S).trans ?_
    rw [hfilt]
    calc 2 * (I.filter fun t => S ⊆ flatRoots ends Z endsN t ∪ auxImage (Φ t)).card
        ≤ 2 * (C * D) := Nat.mul_le_mul_left _ (hcount S hS)
      _ = 2 * C * D := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- **The placed flat step, with hypotheses on the individual link refiners.**  As
`placedFlatStep`, but the pieces need not be nonempty, and the density and degree terms are
expressed through the link refiners: for every `j`-set `J` (`j ≤ r - 1`), summed over the outside
parts `T ⊇ J \ Z`, at most `D · |Z|^(r-1-j)` link pieces of `T` have a vertex set containing
`J ∩ Z`; and the degree of an `(r-1)`-set `S` in the new copies is at most the sum, over the
outside parts `T ⊇ S \ Z`, of the degree of `S ∩ Z` in the link refiner of `T`, plus `Cs' · D`. -/
theorem placedFlatStep_link (q r i Cl : ℕ) (hir : i < r) (hrq : r < q) :
    ∃ Cs Cs' : ℕ, 0 < Cs ∧ ∀ (n : ℕ) {E N : Type} [DecidableEq E] [DecidableEq N]
      (ends : E → Finset (Fin n)) (Z : Finset (Fin n))
      (endsN : Finset (Fin n) → N → Finset (Fin n)) (X : Finset E)
      (RN : Finset (Fin n) → Finset N) (𝒲 : Finset (Fin n) → Finset (Finset (E ⊕ N))) (D : ℕ),
      MIsRGraph r ends X → IsFlat i Z ends X → LinkRefiners q r i Cl ends Z X endsN RN 𝒲 →
      q + r ≤ Z.card → Cs ≤ Z.card →
      (∀ J : Finset (Fin n), J.card ≤ r - 1 →
        ∑ T ∈ (outParts ends Z i X).filter (fun T => J \ Z ⊆ T),
          ((𝒲 T).filter fun W => J ∩ Z ⊆ W.biUnion (lE ends Z endsN T)).card ≤
          D * Z.card ^ (r - 1 - J.card)) →
      ∃ R Y : Finset (E ⊕ FLab (Fin n) E N), ∃ 𝒲' : Finset (Finset (E ⊕ FLab (Fin n) E N)),
        IsResidualMultiRefiner q r (flatConst q r Cl) (fEnds ends endsN) (X.image Sum.inl)
          R Y 𝒲' ∧
        IsFlat (i - 1) Z (fEnds ends endsN) Y ∧
        (∀ x, Sum.inl x ∈ Y → x ∈ X ∧ (ends x \ Z).card < i) ∧
        Y ⊆ X.image Sum.inl ∪ R ∧ (∀ c ∈ R, ∀ x, c ≠ Sum.inl x) ∧
        (∀ c ∈ R, ∃ T ∈ outParts ends Z i X, fEnds ends endsN c ⊆ T ∪ Z) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (fEnds ends endsN) R S ≤
          ∑ T ∈ (outParts ends Z i X).filter (fun T => S \ Z ⊆ T),
            mdeg (endsN T) (RN T) (S ∩ Z) + Cs' * D) ∧
        ∀ S : Finset (Fin n), S.card = r - 1 → pdeg (fEnds ends endsN) 𝒲' S ≤ Cs' * D := by
  obtain ⟨Cs, Cs', hCs, h⟩ := placedFlatStep q r i Cl hir hrq
  refine ⟨Cs, Cs', hCs, ?_⟩
  intro n E N _ _ ends Z endsN X RN 𝒲 D hXr hX hL hZq hCD hdens
  have hL' := hL.filter_nonempty
  obtain ⟨R, Y, 𝒲', h1, h2, h3, h4, h5, h6, h7, h8⟩ := h n ends Z endsN X RN
    (fun T => (𝒲 T).filter Finset.Nonempty) D hXr hX hL'
    (fun T _ W hW => (mem_filter.1 hW).2) hZq hCD (fun J hJ => by
      refine (flatRoots_count_le hL' J).trans (le_trans ?_ (hdens J hJ))
      exact sum_le_sum fun T _ => card_le_card fun W hW => by
        simp only [mem_filter] at hW ⊢
        exact ⟨hW.1.1, hW.2⟩)
  exact ⟨R, Y, 𝒲', h1, h2, h3, h4, h5, h6, fun S hS =>
    (h7 S hS).trans (Nat.add_le_add_right (linkSum_le hL S) _), h8⟩

end

end RefinedAbsorption.Placement
