module
public import RefinedAbsorption.FlatDown.Basic

/-!
# Piece degrees

For a family `𝒲` of pieces (sets of labelled copies) the *piece degree* of a vertex set `S` is the
number of pieces whose vertex set contains `S`:

  `pdeg ends 𝒲 S = #{W ∈ 𝒲 : S ⊆ ⋃_{c ∈ W} ends c}`.

`IsStrongMultiRefiner.pieceDeg` asks for a bound on the piece degrees of `(r-1)`-sets.  This file
collects the bookkeeping used to track piece degrees through the refine-down construction:

* `pdeg_union_le`, `pdeg_image_le`: piece degrees are subadditive over unions of families and do
  not increase under relabelling;
* `pdeg_le_of_parallel`: if every piece consists of parallel copies, piece degrees are bounded by
  the refinedness constant times the ordinary degree (multiplicity reduction);
* `pairFamily_pdeg_le`: piece degrees of the family of a paired completion step are at most twice
  the number of indices whose span contains `S` (flat steps).
-/

@[expose] public section

namespace RefinedAbsorption.MultiRefiner

open Finset

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- Piece degree: the number of pieces of `𝒲` whose vertex set contains `S`. -/
def pdeg (ends : E → Finset V) (𝒲 : Finset (Finset E)) (S : Finset V) : ℕ :=
  (𝒲.filter fun W => S ⊆ W.biUnion ends).card

theorem pdeg_union_le (ends : E → Finset V) (𝒲₁ 𝒲₂ : Finset (Finset E)) (S : Finset V) :
    pdeg ends (𝒲₁ ∪ 𝒲₂) S ≤ pdeg ends 𝒲₁ S + pdeg ends 𝒲₂ S := by
  unfold pdeg; rw [filter_union]; exact card_union_le _ _

omit [DecidableEq E] in
theorem pdeg_mono (ends : E → Finset V) {𝒲₁ 𝒲₂ : Finset (Finset E)} (h : 𝒲₁ ⊆ 𝒲₂)
    (S : Finset V) : pdeg ends 𝒲₁ S ≤ pdeg ends 𝒲₂ S :=
  card_le_card (filter_subset_filter _ h)

omit [DecidableEq E] in
theorem pdeg_le_card (ends : E → Finset V) (𝒲 : Finset (Finset E)) (S : Finset V) :
    pdeg ends 𝒲 S ≤ 𝒲.card :=
  card_filter_le _ _

omit [DecidableEq E] in
/-- Relabelling the copies does not increase piece degrees. -/
theorem pdeg_image_le {E₂ : Type*} [DecidableEq E₂] {ends₁ : E → Finset V}
    {ends₂ : E₂ → Finset V} (g : E → E₂) (hends : ∀ c, ends₂ (g c) = ends₁ c)
    (𝒲 : Finset (Finset E)) (S : Finset V) :
    pdeg ends₂ (𝒲.image (image g)) S ≤ pdeg ends₁ 𝒲 S := by
  unfold pdeg
  have hspan : ∀ W : Finset E, (W.image g).biUnion ends₂ = W.biUnion ends₁ := by
    intro W
    rw [image_biUnion]
    exact biUnion_congr rfl fun c _ => hends c
  rw [filter_image]
  refine card_image_le.trans (le_of_eq ?_)
  congr 1
  exact filter_congr fun W _ => by simp only [hspan]

/-- **Parallel pieces.**  If every piece consists of parallel copies (all copies of a piece have
the same vertex set), then for nonempty `S` the piece degree of `S` is at most the refinedness
constant times the degree of `S` in `X ∪ R`. -/
theorem pdeg_le_of_parallel {q r C : ℕ} {ends : E → Finset V} {X R Y : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsResidualMultiRefiner q r C ends X R Y 𝒲)
    (hpar : ∀ W ∈ 𝒲, ∀ c ∈ W, W.biUnion ends ⊆ ends c) {S : Finset V} (hS : S.Nonempty) :
    pdeg ends 𝒲 S ≤ C * mdeg ends (X ∪ R) S := by
  classical
  obtain ⟨v, hv⟩ := hS
  have hsub : 𝒲.filter (fun W => S ⊆ W.biUnion ends) ⊆
      ((X ∪ R).filter fun c => S ⊆ ends c).biUnion fun c => 𝒲.filter fun W => c ∈ W := by
    intro W hW
    obtain ⟨hW𝒲, hSW⟩ := mem_filter.1 hW
    obtain ⟨c, hcW, -⟩ := mem_biUnion.1 (hSW hv)
    exact mem_biUnion.2 ⟨c, mem_filter.2 ⟨h.subset W hW𝒲 hcW, hSW.trans (hpar W hW𝒲 c hcW)⟩,
      mem_filter.2 ⟨hW𝒲, hcW⟩⟩
  calc pdeg ends 𝒲 S ≤ _ := card_le_card hsub
    _ ≤ ∑ c ∈ (X ∪ R).filter (fun c => S ⊆ ends c), (𝒲.filter fun W => c ∈ W).card :=
        card_biUnion_le
    _ ≤ ∑ _c ∈ (X ∪ R).filter (fun c => S ⊆ ends c), C :=
        sum_le_sum fun c hc => h.mult_le c (mem_filter.1 hc).1
    _ = C * mdeg ends (X ∪ R) S := by rw [sum_const, smul_eq_mul, mul_comm]; rfl

end RefinedAbsorption.MultiRefiner

namespace RefinedAbsorption.FlatDown

open Finset RefinedAbsorption.MultiRefiner

variable {V E : Type*} [DecidableEq V] [DecidableEq E] {ι : Type*}

/-- **Piece degrees of a paired completion step.**  If both pieces of every index `t` have vertex
sets inside a span `sp t`, then at most `2 · #{t : S ⊆ sp t}` pieces have a vertex set containing
`S`. -/
theorem pairFamily_pdeg_le {ends : E → Finset V} {I : Finset ι} {M : ℕ} {B : ι → Finset E}
    {Cc : ι → ℕ → Finset E} (sp : ι → Finset V)
    (hP : ∀ t ∈ I, (pairP B Cc t).biUnion ends ⊆ sp t)
    (hN : ∀ t ∈ I, (pairN M Cc t).biUnion ends ⊆ sp t) (S : Finset V) :
    pdeg ends (pairFamily I M B Cc) S ≤ 2 * (I.filter fun t => S ⊆ sp t).card := by
  unfold pdeg pairFamily
  rw [filter_union]
  refine (card_union_le _ _).trans ?_
  have h1 : ((I.image (pairP B Cc)).filter fun W => S ⊆ W.biUnion ends) ⊆
      (I.filter fun t => S ⊆ sp t).image (pairP B Cc) := by
    intro W hW
    obtain ⟨hW, hS⟩ := mem_filter.1 hW
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hW
    exact mem_image_of_mem _ (mem_filter.2 ⟨ht, hS.trans (hP t ht)⟩)
  have h2 : ((I.image (pairN M Cc)).filter fun W => S ⊆ W.biUnion ends) ⊆
      (I.filter fun t => S ⊆ sp t).image (pairN M Cc) := by
    intro W hW
    obtain ⟨hW, hS⟩ := mem_filter.1 hW
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hW
    exact mem_image_of_mem _ (mem_filter.2 ⟨ht, hS.trans (hN t ht)⟩)
  have := (card_le_card h1).trans card_image_le
  have := (card_le_card h2).trans card_image_le
  omega

end RefinedAbsorption.FlatDown
