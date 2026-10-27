module
public import RequestProject.RefinerReductions

/-!
# Multigraph refiners with residue

Section 3.4 of the survey builds refiners for *multi*-`r`-graphs and then removes the multiple
edges.  We model a multi-`r`-graph by *labelled copies*: a type `E` of edge labels together with a
map `ends : E → Finset V` giving the vertex set of each copy.  A multi-`r`-graph is then a
`Finset E`, and the multiplicity of an `r`-set `e` is the number of labels with `ends i = e`.
Degrees and divisibility count copies with multiplicity.

A *residual* refiner of `X` with residue in `Y` decomposes `R ∪ L`, for every divisible `L ⊆ X`,
into pairwise disjoint pieces of a fixed small family together with a divisible residue contained
in `Y`.  Residual refiners compose (`IsResidualMultiRefiner.trans`): this is how the refine-down
steps are chained.  A residual refiner with residue in `∅` is a (multi-)refiner, and for
`ends = id` it is exactly a refined refiner in the sense of `IsRefinedRefiner`
(`isRefinedRefiner_iff_multi`).

Every structure carries the data that the final embedding step needs: the pieces have at most `C`
copies, every copy lies in at most `C` pieces, and the `(r-1)`-degree budget of the refiner is
tracked separately (`MMaxDegLE`, `MMaxDegLE.union`).
-/

@[expose] public section

namespace RefinedAbsorption.MultiRefiner

open Finset

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- Degree of `S` in the labelled multigraph `G`: the number of copies containing `S`. -/
def mdeg (ends : E → Finset V) (G : Finset E) (S : Finset V) : ℕ :=
  (G.filter (fun i => S ⊆ ends i)).card

/-- Multiplicity of the `r`-set `e` in `G`. -/
def mult (ends : E → Finset V) (G : Finset E) (e : Finset V) : ℕ :=
  (G.filter (fun i => ends i = e)).card

/-- Every copy of `G` is an `r`-set. -/
def MIsRGraph (r : ℕ) (ends : E → Finset V) (G : Finset E) : Prop :=
  ∀ i ∈ G, (ends i).card = r

/-- `K_q^r`-divisibility of a labelled multigraph (degrees counted with multiplicity). -/
def MIsDivisible (q r : ℕ) (ends : E → Finset V) (G : Finset E) : Prop :=
  ∀ S : Finset V, S.card < r → (q - S.card).choose (r - S.card) ∣ mdeg ends G S

/-- `(r-1)`-degree budget: every `(r-1)`-set lies in at most `D` copies of `G`. -/
def MMaxDegLE (r : ℕ) (ends : E → Finset V) (G : Finset E) (D : ℕ) : Prop :=
  ∀ S : Finset V, S.card + 1 = r → mdeg ends G S ≤ D

/-- **Residual multi-refiner.**  `R` is a `C`-refined residual `K_q^r`-refiner of `X` with
family `𝒲` and residue in `Y`: `X ∪ R` is an `r`-multigraph, `X` and `R` share no copy, the pieces
are divisible sub-multigraphs of `X ∪ R` with at most `C` copies, every copy lies in at most `C`
pieces, and for every divisible `L ⊆ X` the multigraph `R ∪ L` is the disjoint union of some
pairwise disjoint pieces and of a divisible residue contained in `Y`. -/
structure IsResidualMultiRefiner (q r C : ℕ) (ends : E → Finset V) (X R Y : Finset E)
    (𝒲 : Finset (Finset E)) : Prop where
  rgraph : MIsRGraph r ends (X ∪ R)
  disjoint : Disjoint X R
  divisible : ∀ W ∈ 𝒲, MIsDivisible q r ends W
  subset : ∀ W ∈ 𝒲, W ⊆ X ∪ R
  card_le : ∀ W ∈ 𝒲, W.card ≤ C
  mult_le : ∀ i ∈ X ∪ R, (𝒲.filter (fun W => i ∈ W)).card ≤ C
  decomp : ∀ L ⊆ X, MIsDivisible q r ends L → ∃ 𝒰 ⊆ 𝒲, ∃ Res ⊆ Y,
    MIsDivisible q r ends Res ∧ (𝒰 : Set (Finset E)).PairwiseDisjoint id ∧
      Disjoint (𝒰.sup id) Res ∧ 𝒰.sup id ∪ Res = R ∪ L

/-- **Multi-refiner**: a residual multi-refiner with empty residue. -/
def IsMultiRefiner (q r C : ℕ) (ends : E → Finset V) (X R : Finset E)
    (𝒲 : Finset (Finset E)) : Prop :=
  IsResidualMultiRefiner q r C ends X R ∅ 𝒲

/-! ### Elementary facts -/

theorem mdeg_union_of_disjoint (ends : E → Finset V) {G H : Finset E} (h : Disjoint G H)
    (S : Finset V) : mdeg ends (G ∪ H) S = mdeg ends G S + mdeg ends H S := by
  rw [mdeg, filter_union, card_union_of_disjoint (disjoint_filter_filter h)]; rfl

omit [DecidableEq E] in
theorem mdeg_mono (ends : E → Finset V) {G H : Finset E} (h : G ⊆ H) (S : Finset V) :
    mdeg ends G S ≤ mdeg ends H S :=
  card_le_card (filter_subset_filter _ h)

theorem MIsDivisible.union {q r : ℕ} {ends : E → Finset V} {G H : Finset E} (hGH : Disjoint G H)
    (hG : MIsDivisible q r ends G) (hH : MIsDivisible q r ends H) :
    MIsDivisible q r ends (G ∪ H) := by
  intro S hS
  rw [mdeg_union_of_disjoint ends hGH]
  exact dvd_add (hG S hS) (hH S hS)

omit [DecidableEq E] in
theorem mIsDivisible_empty (q r : ℕ) (ends : E → Finset V) : MIsDivisible q r ends ∅ := by
  intro S _; simp [mdeg]

/-- The degree budget is additive over disjoint unions. -/
theorem MMaxDegLE.union {r : ℕ} {ends : E → Finset V} {G H : Finset E} {D₁ D₂ : ℕ}
    (hGH : Disjoint G H) (hG : MMaxDegLE r ends G D₁) (hH : MMaxDegLE r ends H D₂) :
    MMaxDegLE r ends (G ∪ H) (D₁ + D₂) := by
  intro S hS
  rw [mdeg_union_of_disjoint ends hGH]
  exact Nat.add_le_add (hG S hS) (hH S hS)

omit [DecidableEq E] in
theorem MMaxDegLE.mono {r : ℕ} {ends : E → Finset V} {G H : Finset E} {D D' : ℕ}
    (hGH : G ⊆ H) (hH : MMaxDegLE r ends H D) (hD : D ≤ D') : MMaxDegLE r ends G D' :=
  fun S hS => (mdeg_mono ends hGH S).trans ((hH S hS).trans hD)

theorem IsResidualMultiRefiner.mono {q r C C' : ℕ} {ends : E → Finset V} {X R Y : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsResidualMultiRefiner q r C ends X R Y 𝒲) (hC : C ≤ C') :
    IsResidualMultiRefiner q r C' ends X R Y 𝒲 :=
  { h with
    card_le := fun W hW => (h.card_le W hW).trans hC
    mult_le := fun i hi => (h.mult_le i hi).trans hC }

/-- Enlarging the residue set. -/
theorem IsResidualMultiRefiner.mono_residue {q r C : ℕ} {ends : E → Finset V} {X R Y Y' : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsResidualMultiRefiner q r C ends X R Y 𝒲) (hY : Y ⊆ Y') :
    IsResidualMultiRefiner q r C ends X R Y' 𝒲 := by
  refine { h with decomp := fun L hL hdiv => ?_ }
  obtain ⟨𝒰, h𝒰, Res, hRes, h1, h2, h3, h4⟩ := h.decomp L hL hdiv
  exact ⟨𝒰, h𝒰, Res, hRes.trans hY, h1, h2, h3, h4⟩

/-- **Trivial residual refiner** (start of the refine-down iteration): the empty refiner with
empty family; the residue of `L` is `L` itself, contained in `Y = X`. -/
theorem isResidualMultiRefiner_self {q r : ℕ} (C : ℕ) {ends : E → Finset V} {X : Finset E}
    (hX : MIsRGraph r ends X) : IsResidualMultiRefiner q r C ends X ∅ X ∅ := by
  refine ⟨by simpa using hX, disjoint_empty_right _, by simp, by simp, by simp, by simp,
    fun L hL hdiv => ⟨∅, subset_rfl, L, hL, hdiv, by simp, by simp, by simp⟩⟩

/-! ### Composition (chaining refine-down steps) -/

/-- **Composition of residual refiners.**  If `R₁` refines `X` with residue in `Y`, where
`Y ⊆ X ∪ R₁`, and `R₂` (sharing no copy with `X ∪ R₁`) refines `Y` with residue in `Z`, then
`R₁ ∪ R₂` refines `X` with residue in `Z`, family `𝒲₁ ∪ 𝒲₂` and refinedness `C₁ + C₂`. -/
theorem IsResidualMultiRefiner.trans {q r C₁ C₂ : ℕ} {ends : E → Finset V}
    {X R₁ Y R₂ Z : Finset E} {𝒲₁ 𝒲₂ : Finset (Finset E)}
    (h₁ : IsResidualMultiRefiner q r C₁ ends X R₁ Y 𝒲₁)
    (h₂ : IsResidualMultiRefiner q r C₂ ends Y R₂ Z 𝒲₂)
    (hY : Y ⊆ X ∪ R₁) (hR₂ : Disjoint R₂ (X ∪ R₁)) :
    IsResidualMultiRefiner q r (C₁ + C₂) ends X (R₁ ∪ R₂) Z (𝒲₁ ∪ 𝒲₂) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases mem_union.1 hi with hi | hi
    · exact h₁.rgraph i (mem_union_left _ hi)
    · rcases mem_union.1 hi with hi | hi
      · exact h₁.rgraph i (mem_union_right _ hi)
      · exact h₂.rgraph i (mem_union_right _ hi)
  · rw [disjoint_union_right]
    exact ⟨h₁.disjoint, (disjoint_of_subset_right subset_union_left hR₂).symm⟩
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · exact h₁.divisible W hW
    · exact h₂.divisible W hW
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · exact (h₁.subset W hW).trans (by intro i; simp only [mem_union]; tauto)
    · refine (h₂.subset W hW).trans ?_
      intro i hi
      rcases mem_union.1 hi with hi | hi
      · rcases mem_union.1 (hY hi) with h | h <;> simp [h]
      · simp [hi]
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · exact (h₁.card_le W hW).trans (Nat.le_add_right _ _)
    · exact (h₂.card_le W hW).trans (Nat.le_add_left _ _)
  · intro i _
    rw [filter_union]
    refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
    · by_cases hi : i ∈ X ∪ R₁
      · exact h₁.mult_le i hi
      · rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun W hW hiW => hi (h₁.subset W hW hiW))]
        exact Nat.zero_le _
    · by_cases hi : i ∈ Y ∪ R₂
      · exact h₂.mult_le i hi
      · rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun W hW hiW => hi (h₂.subset W hW hiW))]
        exact Nat.zero_le _
  · intro L hL hdiv
    obtain ⟨𝒰₁, h𝒰₁, Res₁, hRes₁Y, hRes₁d, hpw₁, hd₁, heq₁⟩ := h₁.decomp L hL hdiv
    obtain ⟨𝒰₂, h𝒰₂, Res₂, hRes₂Z, hRes₂d, hpw₂, hd₂, heq₂⟩ := h₂.decomp Res₁ hRes₁Y hRes₁d
    -- pieces of `𝒰₁` avoid `R₂ ∪ Res₁`
    have hU₁ : ∀ W ∈ 𝒰₁, Disjoint W (R₂ ∪ Res₁) := by
      intro W hW
      have hWsup : W ⊆ 𝒰₁.sup id := le_sup (f := id) hW
      rw [disjoint_union_right]
      exact ⟨disjoint_of_subset_left (h₁.subset W (h𝒰₁ hW)) hR₂.symm,
        disjoint_of_subset_left hWsup hd₁⟩
    have hU₂ : ∀ W ∈ 𝒰₂, W ⊆ R₂ ∪ Res₁ := by
      intro W hW
      have : W ⊆ 𝒰₂.sup id ∪ Res₂ := (le_sup (f := id) hW).trans subset_union_left
      rwa [heq₂] at this
    have hRes₂ : Res₂ ⊆ R₂ ∪ Res₁ := by
      have : Res₂ ⊆ 𝒰₂.sup id ∪ Res₂ := subset_union_right
      rwa [heq₂] at this
    refine ⟨𝒰₁ ∪ 𝒰₂, union_subset_union h𝒰₁ h𝒰₂, Res₂, hRes₂Z, hRes₂d, ?_, ?_, ?_⟩
    · intro W hW W' hW' hne
      simp only [coe_union, Set.mem_union, mem_coe] at hW hW'
      rcases hW with hW | hW <;> rcases hW' with hW' | hW'
      · exact hpw₁ hW hW' hne
      · exact disjoint_of_subset_right (hU₂ W' hW') (hU₁ W hW)
      · exact (disjoint_of_subset_right (hU₂ W hW) (hU₁ W' hW')).symm
      · exact hpw₂ hW hW' hne
    · rw [sup_union, show (𝒰₁.sup id ⊔ 𝒰₂.sup id) = 𝒰₁.sup id ∪ 𝒰₂.sup id from rfl,
        disjoint_union_left]
      refine ⟨?_, hd₂⟩
      rw [Finset.disjoint_sup_left]
      exact fun W hW => disjoint_of_subset_right hRes₂ (hU₁ W hW)
    · rw [sup_union, show (𝒰₁.sup id ⊔ 𝒰₂.sup id) = 𝒰₁.sup id ∪ 𝒰₂.sup id from rfl,
        union_assoc, heq₂]
      have : 𝒰₁.sup id ∪ (R₂ ∪ Res₁) = (𝒰₁.sup id ∪ Res₁) ∪ R₂ := by
        ext i; simp only [mem_union]; tauto
      rw [this, heq₁]
      ext i; simp only [mem_union]; tauto

/-! ### Simple refiners are multi-refiners with `ends = id` -/

theorem mdeg_id (G : Finset (Finset V)) (S : Finset V) : mdeg id G S = deg G S := rfl

/-- For `ends = id` (no multiple edges), multi-refiners are exactly refined refiners. -/
theorem isRefinedRefiner_iff_multi {q r C : ℕ} {X R : Finset (Finset V)}
    {𝒲 : Finset (Finset (Finset V))} :
    IsRefinedRefiner q r C X R 𝒲 ↔ IsMultiRefiner q r C id X R 𝒲 := by
  constructor
  · intro h
    refine ⟨h.rgraph, h.disjoint, h.divisible, h.subset, h.card_le, h.mult_le, fun L hL hdiv => ?_⟩
    obtain ⟨𝒰, h𝒰, hpw, hsup⟩ := h.decomp L hL hdiv
    exact ⟨𝒰, h𝒰, ∅, subset_rfl, mIsDivisible_empty q r id, hpw, disjoint_empty_right _,
      by rw [union_empty, hsup]⟩
  · intro h
    refine ⟨h.rgraph, h.disjoint, h.divisible, h.subset, h.card_le, h.mult_le, fun L hL hdiv => ?_⟩
    obtain ⟨𝒰, h𝒰, Res, hRes, -, hpw, -, hsup⟩ := h.decomp L hL hdiv
    rw [subset_empty.1 hRes, union_empty] at hsup
    exact ⟨𝒰, h𝒰, hpw, hsup⟩

end RefinedAbsorption.MultiRefiner
