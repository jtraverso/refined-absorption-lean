module
public import RequestProject.FlatDown.FlatStep
public import RequestProject.FlatDown.AntiEdge
public import RequestProject.MultiRefiner.PieceDeg

/-!
# Proof of the flat step

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, induction on
uniformity).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

* `fix_divisible`: one extra completion copy for every base piece used in the decomposition of
  the empty multigraph makes the whole refiner divisible.
* `flatStep`: **the step from `i`-flat to `(i-1)`-flat.**  Given multi-refiners (with empty
  residue, constant `Cl`) of the links of an `i`-flat `r`-multigraph `X` inside the reserve `Z`,
  it builds a residual `K_q^r`-refiner of `X` whose residue is `(i-1)`-flat with respect to `Z`.
  Its constant depends only on `q`, `r` and `Cl` (not on `X`, `Z` or the number of links).
-/

@[expose] public section

namespace RefinedAbsorption.FlatDown

open Finset RefinedAbsorption.MultiRefiner

section Fix

variable {V E : Type*} [DecidableEq V] [DecidableEq E] {ι : Type*} [DecidableEq ι]

/-- The blocks of the divisible decomposition of the refiner of a paired step with one extra
copy for the pieces used by the empty multigraph. -/
def fixBlock (J : Finset ι) (M : ℕ) (B : ι → Finset E) (Cc : ι → ℕ → Finset E) (t : ι) :
    Finset E :=
  if t ∈ J then (B t ∪ Cc t 0) ∪ (range M).biUnion (fun k => Cc t (k + 1))
  else (range M).biUnion (Cc t)

theorem fix_divisible {q r M : ℕ} {ends : E → Finset V} {I J : Finset ι} {B : ι → Finset E}
    {Cc : ι → ℕ → Finset E} {R₀ : Finset E}
    (hM : 1 ≤ M) (hdvd : ∀ s < r, (q - s).choose (r - s) ∣ M) (hJ : J ⊆ I)
    (hBJ : ∀ t ∈ J, ∀ t' ∈ J, t ≠ t' → Disjoint (B t) (B t'))
    (hR₀ : J.biUnion B = R₀)
    (hP : ∀ t ∈ J, MIsDivisible q r ends (B t ∪ Cc t 0))
    (hsame : ∀ t ∈ I, ∀ k, ∀ S, mdeg ends (Cc t k) S = mdeg ends (Cc t 0) S)
    (hCd : ∀ t ∈ I, ∀ k, ∀ t' ∈ I, ∀ k', (t, k) ≠ (t', k') → Disjoint (Cc t k) (Cc t' k'))
    (hBC : ∀ t ∈ I, ∀ t' ∈ I, ∀ k, Disjoint (B t) (Cc t' k)) :
    MIsDivisible q r ends (R₀ ∪ allC I M Cc ∪ J.biUnion fun t => Cc t M) := by
  have hset : R₀ ∪ allC I M Cc ∪ J.biUnion (fun t => Cc t M) =
      I.biUnion (fixBlock J M B Cc) := by
    subst hR₀
    ext c
    simp only [mem_union, mem_biUnion, mem_allC, fixBlock]
    constructor
    · rintro ((⟨t, ht, hc⟩ | ⟨t, ht, k, hk, hc⟩) | ⟨t, ht, hc⟩)
      · exact ⟨t, hJ ht, by simp [ht, hc]⟩
      · refine ⟨t, ht, ?_⟩
        split_ifs with htJ
        · rcases Nat.eq_zero_or_pos k with rfl | hk0
          · simp [hc]
          · refine mem_union_right _ (mem_biUnion.2 ⟨k - 1, mem_range.2 (by omega), ?_⟩)
            rwa [Nat.sub_add_cancel hk0]
        · exact mem_biUnion.2 ⟨k, mem_range.2 hk, hc⟩
      · refine ⟨t, hJ ht, ?_⟩
        rw [if_pos ht]
        refine mem_union_right _ (mem_biUnion.2 ⟨M - 1, mem_range.2 (by omega), ?_⟩)
        rwa [Nat.sub_add_cancel hM]
    · rintro ⟨t, ht, hc⟩
      split_ifs at hc with htJ
      · rcases mem_union.1 hc with hc | hc
        · rcases mem_union.1 hc with hc | hc
          · exact Or.inl (Or.inl ⟨t, htJ, hc⟩)
          · exact Or.inl (Or.inr ⟨t, ht, 0, hM, hc⟩)
        · obtain ⟨k, hk, hc⟩ := mem_biUnion.1 hc
          rw [mem_range] at hk
          rcases Nat.lt_or_ge (k + 1) M with hk' | hk'
          · exact Or.inl (Or.inr ⟨t, ht, k + 1, hk', hc⟩)
          · have : k + 1 = M := by omega
            exact Or.inr ⟨t, htJ, this ▸ hc⟩
      · obtain ⟨k, hk, hc⟩ := mem_biUnion.1 hc
        exact Or.inl (Or.inr ⟨t, ht, k, mem_range.1 hk, hc⟩)
  rw [hset]
  have hmem : ∀ t ∈ I, ∀ c ∈ fixBlock J M B Cc t, c ∈ B t ∨ ∃ k, c ∈ Cc t k := by
    intro t _ c hc
    unfold fixBlock at hc
    split_ifs at hc
    · rcases mem_union.1 hc with hc | hc
      · rcases mem_union.1 hc with hc | hc
        · exact Or.inl hc
        · exact Or.inr ⟨0, hc⟩
      · obtain ⟨k, -, hc⟩ := mem_biUnion.1 hc; exact Or.inr ⟨k + 1, hc⟩
    · obtain ⟨k, -, hc⟩ := mem_biUnion.1 hc; exact Or.inr ⟨k, hc⟩
  have hmemB : ∀ t ∈ I, ∀ c ∈ B t, c ∈ fixBlock J M B Cc t → t ∈ J := by
    intro t ht c hcB hc
    by_contra htJ
    unfold fixBlock at hc
    rw [if_neg htJ] at hc
    obtain ⟨k, -, hc⟩ := mem_biUnion.1 hc
    exact disjoint_left.1 (hBC t ht t ht k) hcB hc
  refine divisible_biUnion I _ ?_ ?_
  · intro t ht t' ht' hne
    rw [disjoint_left]
    intro c hc hc'
    rcases hmem t ht c hc with h1 | ⟨k, h1⟩ <;> rcases hmem t' ht' c hc' with h2 | ⟨k', h2⟩
    · exact disjoint_left.1 (hBJ t (hmemB t ht c h1 hc) t' (hmemB t' ht' c h2 hc') hne) h1 h2
    · exact disjoint_left.1 (hBC t ht t' ht' k') h1 h2
    · exact disjoint_left.1 (hBC t' ht' t ht k) h2 h1
    · exact disjoint_left.1 (hCd t ht k t' ht' k' (fun h => hne (Prod.ext_iff.1 h).1)) h1 h2
  · intro t ht
    unfold fixBlock
    split_ifs with htJ
    · refine MIsDivisible.union ?_ (hP t htJ) ?_
      · rw [disjoint_left]
        intro c hc hc'
        obtain ⟨k, -, hc'⟩ := mem_biUnion.1 hc'
        rcases mem_union.1 hc with hc | hc
        · exact disjoint_left.1 (hBC t ht t ht (k + 1)) hc hc'
        · exact disjoint_left.1 (hCd t ht 0 t ht (k + 1) (by simp)) hc hc'
      · refine divisible_copies (fun k => Cc t (k + 1)) ?_ ?_ hdvd
        · intro k _ k' _ hne
          exact hCd t ht _ t ht _ (by simpa using hne)
        · intro k _ S
          simp only [zero_add]
          rw [hsame t ht, hsame t ht 1]
    · refine divisible_copies (Cc t) ?_ ?_ hdvd
      · intro k _ k' _ hne
        exact hCd t ht _ t ht _ (by simpa using hne)
      · intro k _ S; exact hsame t ht k S

end Fix

section Flat

variable {V E N : Type} [DecidableEq V] [DecidableEq E] [DecidableEq N]
  {ends : E → Finset V} {Z : Finset V} {endsN : Finset V → N → Finset V}

/-- Multi-refiners (empty residue, constant `Cl`) of the links of the outside parts of size `i`
of `X`, with all new copies inside the reserve `Z`. -/
structure LinkRefiners (q r i Cl : ℕ) (ends : E → Finset V) (Z : Finset V) (X : Finset E)
    (endsN : Finset V → N → Finset V) (RN : Finset V → Finset N)
    (𝒲 : Finset V → Finset (Finset (E ⊕ N))) : Prop where
  ref : ∀ T ∈ outParts ends Z i X, IsMultiRefiner (q - i) (r - i) Cl (lE ends Z endsN T)
    ((lnk ends Z X T).image Sum.inl) ((RN T).image Sum.inr) (𝒲 T)
  inZ : ∀ T ∈ outParts ends Z i X, ∀ y ∈ RN T, endsN T y ⊆ Z

/-- The copies of the link of `T` together with its refiner. -/
def LV (ends : E → Finset V) (Z : Finset V) (X : Finset E) (RN : Finset V → Finset N)
    (T : Finset V) : Finset (E ⊕ N) :=
  (lnk ends Z X T).image Sum.inl ∪ (RN T).image Sum.inr

/-- Index set of the base pieces: the pieces of all link refiners. -/
def fI (ends : E → Finset V) (Z : Finset V) (i : ℕ) (X : Finset E)
    (𝒲 : Finset V → Finset (Finset (E ⊕ N))) : Finset (Finset V × Finset (E ⊕ N)) :=
  (outParts ends Z i X).biUnion fun T => (𝒲 T).image fun W => (T, W)

/-- The lifted base pieces. -/
def fB (t : Finset V × Finset (E ⊕ N)) : Finset (E ⊕ FLab V E N) := t.2.image (liftT t.1)

/-- The lifted link refiners. -/
def fR₀ (ends : E → Finset V) (Z : Finset V) (i : ℕ) (X : Finset E) (RN : Finset V → Finset N) :
    Finset (E ⊕ FLab V E N) :=
  (outParts ends Z i X).biUnion fun T => (RN T).image fun y => Sum.inr (Sum.inl (T, y))

/-- The copies of `X` with exactly `i` vertices outside the reserve. -/
def fXact (ends : E → Finset V) (Z : Finset V) (i : ℕ) (X : Finset E) : Finset (E ⊕ FLab V E N) :=
  (X.filter fun x => (ends x \ Z).card = i).image Sum.inl

theorem mem_outParts {i : ℕ} {X : Finset E} {T : Finset V} :
    T ∈ outParts ends Z i X ↔ ∃ x ∈ X, (ends x \ Z).card = i ∧ ends x \ Z = T := by
  simp [outParts, and_assoc]

theorem outParts_card {i : ℕ} {X : Finset E} {T : Finset V} (hT : T ∈ outParts ends Z i X) :
    T.card = i ∧ Disjoint T Z := by
  obtain ⟨x, -, h1, rfl⟩ := mem_outParts.1 hT
  exact ⟨h1, sdiff_disjoint⟩


theorem mem_fI {i : ℕ} {X : Finset E} {𝒲 : Finset V → Finset (Finset (E ⊕ N))}
    {t : Finset V × Finset (E ⊕ N)} :
    t ∈ fI ends Z i X 𝒲 ↔ t.1 ∈ outParts ends Z i X ∧ t.2 ∈ 𝒲 t.1 := by
  obtain ⟨T, W⟩ := t
  simp only [fI, mem_biUnion, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨T', hT', W', hW', rfl, rfl⟩; exact ⟨hT', hW'⟩
  · rintro ⟨hT, hW⟩; exact ⟨T, hT, W, hW, rfl, rfl⟩


theorem mem_LV {X : Finset E} {RN : Finset V → Finset N} {T : Finset V} {w : E ⊕ N} :
    w ∈ LV ends Z X RN T ↔ (∃ x ∈ lnk ends Z X T, w = Sum.inl x) ∨ (∃ y ∈ RN T, w = Sum.inr y) := by
  simp only [LV, mem_union, mem_image]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨y, hy, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨y, hy, rfl⟩


theorem fEnds_liftT {X : Finset E} {RN : Finset V → Finset N} {T : Finset V} {w : E ⊕ N}
    (hw : w ∈ LV ends Z X RN T) :
    fEnds ends endsN (liftT T w : E ⊕ FLab V E N) = T ∪ lE ends Z endsN T w := by
  rcases mem_LV.1 hw with ⟨x, hx, rfl⟩ | ⟨y, -, rfl⟩
  · have hxT : ends x \ Z = T := (mem_filter.1 hx).2
    show ends x = T ∪ (ends x ∩ Z)
    rw [← hxT, sdiff_union_inter]
  · rfl


theorem liftT_eq {X : Finset E} {RN : Finset V → Finset N} {T T' : Finset V} {w w' : E ⊕ N}
    (hw : w ∈ LV ends Z X RN T) (hw' : w' ∈ LV ends Z X RN T')
    (h : (liftT T w : E ⊕ FLab V E N) = liftT T' w') : T = T' ∧ w = w' := by
  rcases mem_LV.1 hw with ⟨x, hx, rfl⟩ | ⟨y, -, rfl⟩ <;>
    rcases mem_LV.1 hw' with ⟨x', hx', rfl⟩ | ⟨y', -, rfl⟩
  · simp only [liftT, Sum.elim_inl, Sum.inl.injEq] at h
    subst h
    exact ⟨(mem_filter.1 hx).2.symm.trans (mem_filter.1 hx').2, rfl⟩
  · simp [liftT] at h
  · simp [liftT] at h
  · simp only [liftT, Sum.elim_inr, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
    exact ⟨h.1, by rw [h.2]⟩

theorem AW_subset {Z₀ T : Finset V} {W : Finset (E ⊕ N)} (hZ₀ : Z₀ ⊆ Z)
    (hW : ∀ w ∈ W, lE ends Z endsN T w ⊆ Z) : AW ends Z endsN Z₀ T W ⊆ Z :=
  union_subset hZ₀ (biUnion_subset.2 hW)

theorem AW_card_le {Z₀ T : Finset V} {W : Finset (E ⊕ N)} {r : ℕ}
    (hW : ∀ w ∈ W, (lE ends Z endsN T w).card ≤ r) :
    (AW ends Z endsN Z₀ T W).card ≤ Z₀.card + W.card * r := by
  refine (card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
  refine card_biUnion_le.trans ?_
  calc ∑ w ∈ W, (lE ends Z endsN T w).card ≤ ∑ _w ∈ W, r := sum_le_sum hW
    _ = W.card * r := by rw [sum_const, smul_eq_mul]

theorem cf_spec {q r i : ℕ} {Z₀ T : Finset V} {W : Finset (E ⊕ N)}
    (h : ∃ c, GJWId ends Z endsN q r i Z₀ T W c) :
    GJWId ends Z endsN q r i Z₀ T W (cf ends Z endsN q r i Z₀ T W) := by
  unfold cf
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem compLab_ends {q r i M : ℕ} {Z₀ T : Finset V} {W : Finset (E ⊕ N)} {k : ℕ}
    (hZ₀ : Z₀ ⊆ Z) (hW : ∀ w ∈ W, lE ends Z endsN T w ⊆ Z) (hT : T.card = i)
    {c : E ⊕ FLab V E N} (hc : c ∈ compLab ends Z endsN q r i M Z₀ T W k) :
    (fEnds ends endsN c).card = r ∧ (fEnds ends endsN c \ Z).card < i := by
  obtain ⟨Q, hQ, j, -, e, he, rfl⟩ := mem_compLab.1 hc
  have hQZ : Q ⊆ Z := (mem_powersetCard.1 hQ).1.trans (AW_subset hZ₀ hW)
  simp only [compE, mem_filter, mem_powersetCard] at he
  obtain ⟨⟨heTQ, her⟩, hTe⟩ := he
  refine ⟨her, ?_⟩
  show (e \ Z).card < i
  have hsub : e \ Z ⊆ T := by
    intro v hv
    obtain ⟨hve, hvZ⟩ := mem_sdiff.1 hv
    rcases mem_union.1 (heTQ hve) with h1 | h1
    · exact h1
    · exact absurd (hQZ h1) hvZ
  have hne : e \ Z ≠ T := fun h => hTe (h ▸ sdiff_subset)
  rw [← hT]
  exact card_lt_card (ssubset_of_subset_of_ne hsub hne)

theorem compLab_disj {q r i M : ℕ} {Z₀ Z₀' T T' : Finset V} {W W' : Finset (E ⊕ N)} {k k' : ℕ}
    (hne : (T, W, k) ≠ (T', W', k')) :
    Disjoint (compLab ends Z endsN q r i M Z₀ T W k) (compLab ends Z endsN q r i M Z₀' T' W' k') := by
  rw [disjoint_left]
  intro c hc hc'
  obtain ⟨l, rfl, h1, h2, h3, -⟩ := compLab_tag hc
  obtain ⟨l', h, h1', h2', h3', -⟩ := compLab_tag hc'
  simp only [Sum.inr.injEq] at h
  subst h
  exact hne (by rw [← h1, ← h2, ← h3, ← h1', ← h2', ← h3'])

theorem mdeg_image_inl_lE (T : Finset V) (G : Finset E) (S : Finset V) :
    mdeg (lE ends Z endsN T) (G.image Sum.inl) S = mdeg (lk ends Z) G S := by
  unfold mdeg
  rw [filter_image, card_image_of_injective _ Sum.inl_injective]
  rfl

/-- **Base decomposition of the flat step**: for a divisible `L₀ ⊆ X`, the lifted link refiners
together with the copies of `L₀` with `i` outside vertices are a disjoint union of lifted pieces. -/
theorem flat_base {q r i Cl : ℕ} {X : Finset E} {RN : Finset V → Finset N}
    {𝒲 : Finset V → Finset (Finset (E ⊕ N))} (hX : IsFlat i Z ends X)
    (hL : LinkRefiners q r i Cl ends Z X endsN RN 𝒲) {L₀ : Finset E} (hL₀ : L₀ ⊆ X)
    (hdiv : MIsDivisible q r ends L₀) :
    ∃ J ⊆ fI ends Z i X 𝒲, (∀ t ∈ J, ∀ t' ∈ J, t ≠ t' → Disjoint (fB t) (fB t')) ∧
      J.biUnion fB = fR₀ ends Z i X RN ∪ (L₀.image Sum.inl ∩ fXact ends Z i X) := by
  have hex : ∀ T ∈ outParts ends Z i X, ∃ 𝒰 ⊆ 𝒲 T,
      (𝒰 : Set (Finset (E ⊕ N))).PairwiseDisjoint id ∧
      𝒰.sup id = (RN T).image Sum.inr ∪ (lnk ends Z L₀ T).image Sum.inl := by
    intro T hT
    obtain ⟨hTc, hTZ⟩ := outParts_card hT
    have hdivT : MIsDivisible (q - i) (r - i) (lE ends Z endsN T)
        ((lnk ends Z L₀ T).image Sum.inl) := by
      intro S hS
      rw [mdeg_image_inl_lE]
      exact link_divisible (hX.mono hL₀ le_rfl) hTc hTZ hdiv S hS
    have hsub : (lnk ends Z L₀ T).image (Sum.inl : E → E ⊕ N) ⊆
        (lnk ends Z X T).image Sum.inl :=
      image_subset_image (filter_subset_filter _ hL₀)
    obtain ⟨𝒰, h𝒰, Res, hRes, -, hpw, -, hU⟩ := (hL.ref T hT).decomp _ hsub hdivT
    have hRes' : Res = ∅ := subset_empty.1 hRes
    subst hRes'
    exact ⟨𝒰, h𝒰, hpw, by rw [union_empty] at hU; exact hU⟩
  choose! U hUsub hUpw hUsup using hex
  have hWLV : ∀ T ∈ outParts ends Z i X, ∀ W ∈ 𝒲 T, W ⊆ LV ends Z X RN T :=
    fun T hT W hW => (hL.ref T hT).subset W hW
  refine ⟨(outParts ends Z i X).biUnion fun T => (U T).image fun W => (T, W), ?_, ?_, ?_⟩
  · intro t ht
    simp only [mem_biUnion, mem_image] at ht
    obtain ⟨T, hT, W, hW, rfl⟩ := ht
    exact mem_fI.2 ⟨hT, hUsub T hT hW⟩
  · intro t ht t' ht' hne
    simp only [mem_biUnion, mem_image] at ht ht'
    obtain ⟨T, hT, W, hW, rfl⟩ := ht
    obtain ⟨T', hT', W', hW', rfl⟩ := ht'
    rw [disjoint_left]
    intro c hc hc'
    simp only [fB, mem_image] at hc hc'
    obtain ⟨w, hw, rfl⟩ := hc
    obtain ⟨w', hw', h⟩ := hc'
    obtain ⟨rfl, rfl⟩ := liftT_eq (hWLV T hT W (hUsub T hT hW) hw)
      (hWLV T' hT' W' (hUsub T' hT' hW') hw') h.symm
    have hWW : W ≠ W' := fun h' => hne (by rw [h'])
    exact disjoint_left.1 (hUpw T hT (mem_coe.2 hW) (mem_coe.2 hW') hWW) hw hw'
  · ext c
    simp only [mem_biUnion, mem_image, fB, fR₀, fXact, mem_union, mem_inter, mem_filter]
    constructor
    · rintro ⟨_, ⟨T, hT, W, hW, rfl⟩, w, hw, rfl⟩
      have hw' : w ∈ (U T).sup id := mem_sup.2 ⟨W, hW, hw⟩
      rw [hUsup T hT] at hw'
      rcases mem_union.1 hw' with h1 | h1
      · obtain ⟨y, hy, rfl⟩ := mem_image.1 h1
        exact Or.inl ⟨T, hT, y, hy, rfl⟩
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 h1
        obtain ⟨hxL, hxT⟩ := mem_filter.1 hx
        refine Or.inr ⟨⟨x, hxL, rfl⟩, x, ⟨hL₀ hxL, ?_⟩, rfl⟩
        rw [hxT]; exact (outParts_card hT).1
    · rintro (⟨T, hT, y, hy, rfl⟩ | ⟨⟨x, hxL, rfl⟩, x', ⟨hx'X, hx'c⟩, hxx⟩)
      · have : (Sum.inr y : E ⊕ N) ∈ (U T).sup id := by
          rw [hUsup T hT]; exact mem_union_left _ (mem_image_of_mem _ hy)
        obtain ⟨W, hW, hyW⟩ := mem_sup.1 this
        exact ⟨_, ⟨T, hT, W, hW, rfl⟩, Sum.inr y, hyW, rfl⟩
      · have hxx' : x' = x := Sum.inl_injective hxx
        subst hxx'
        have hT : ends x' \ Z ∈ outParts ends Z i X := mem_outParts.2 ⟨x', hx'X, hx'c, rfl⟩
        have : (Sum.inl x' : E ⊕ N) ∈ (U (ends x' \ Z)).sup id := by
          rw [hUsup _ hT]; exact mem_union_right _ (mem_image_of_mem _ (mem_filter.2 ⟨hxL, rfl⟩))
        obtain ⟨W, hW, hxW⟩ := mem_sup.1 this
        exact ⟨_, ⟨_, hT, W, hW, rfl⟩, Sum.inl x', hxW, rfl⟩

omit [DecidableEq V] [DecidableEq E] [DecidableEq N] in
theorem liftT_ne_comp (T : Finset V) (w : E ⊕ N) (l : CLab V E N) :
    (liftT T w : E ⊕ FLab V E N) ≠ Sum.inr (Sum.inr l) := by
  rcases w with x | y <;> simp [liftT]

theorem fB_disj_compLab {q r i M : ℕ} {Z₀ T' : Finset V} {W' : Finset (E ⊕ N)} {k : ℕ}
    (t : Finset V × Finset (E ⊕ N)) :
    Disjoint (fB t) (compLab ends Z endsN q r i M Z₀ T' W' k) := by
  rw [disjoint_left]
  intro c hc hc'
  obtain ⟨w, -, rfl⟩ := mem_image.1 hc
  obtain ⟨l, h, -⟩ := compLab_tag hc'
  exact liftT_ne_comp _ _ _ h

/-- Properties of the link copies used by a piece of a link refiner. -/
theorem link_piece_props {q r i Cl : ℕ} {X : Finset E} {RN : Finset V → Finset N}
    {𝒲 : Finset V → Finset (Finset (E ⊕ N))} (hL : LinkRefiners q r i Cl ends Z X endsN RN 𝒲)
    {T : Finset V} (hT : T ∈ outParts ends Z i X) {W : Finset (E ⊕ N)} (hW : W ∈ 𝒲 T) :
    ∀ w ∈ W, w ∈ LV ends Z X RN T ∧ lE ends Z endsN T w ⊆ Z ∧
      (lE ends Z endsN T w).card = r - i := by
  intro w hw
  have hLV : w ∈ LV ends Z X RN T := (hL.ref T hT).subset W hW hw
  refine ⟨hLV, ?_, (hL.ref T hT).rgraph w hLV⟩
  rcases mem_LV.1 hLV with ⟨x, -, rfl⟩ | ⟨y, hy, rfl⟩
  · exact inter_subset_right
  · exact hL.inZ T hT y hy

/-- The lifted and completed piece is `K_q^r`-divisible. -/
theorem flat_piece_div {q r i Cl M : ℕ} {X : Finset E} {RN : Finset V → Finset N}
    {𝒲 : Finset V → Finset (Finset (E ⊕ N))} {Z₀ : Finset V} (hir : i < r) (hrq : r < q)
    (hL : LinkRefiners q r i Cl ends Z X endsN RN 𝒲) (hZ₀ : Z₀ ⊆ Z) (hZ₀c : q + r ≤ Z₀.card)
    (hM : 0 < M) (hdvd : ∀ s < r, (q - s).choose (r - s) ∣ M)
    {t : Finset V × Finset (E ⊕ N)} (ht : t ∈ fI ends Z i X 𝒲) :
    MIsDivisible q r (fEnds ends endsN) (fB t ∪ compLab ends Z endsN q r i M Z₀ t.1 t.2 0) := by
  obtain ⟨T, W⟩ := t
  obtain ⟨hT, hW⟩ := mem_fI.1 ht
  simp only at hT hW
  have hp := link_piece_props hL hT hW
  obtain ⟨hTc, hTZ⟩ := outParts_card hT
  have hAWZ : AW ends Z endsN Z₀ T W ⊆ Z := AW_subset hZ₀ fun w hw => (hp w hw).2.1
  have hWA : ∀ w ∈ W, lE ends Z endsN T w ⊆ AW ends Z endsN Z₀ T W := fun w hw =>
    (subset_biUnion_of_mem _ hw).trans subset_union_right
  have hgjw : ∃ c, GJWId ends Z endsN q r i Z₀ T W c := by
    refine gjw_local (q := q - i) (r := r - i) (by omega) (AW ends Z endsN Z₀ T W) ?_
      (lE ends Z endsN T) W (fun w hw => ⟨hWA w hw, (hp w hw).2.2⟩)
      ((hL.ref T hT).divisible W hW)
    exact le_trans (by omega) (hZ₀c.trans (card_le_card subset_union_left))
  intro S hS
  rw [mdeg_union_of_disjoint _ (fB_disj_compLab _), mdeg_compLab]
  have hB : mdeg (fEnds ends endsN) (fB (T, W)) S =
      (W.filter fun w => S ⊆ T ∪ lE ends Z endsN T w).card := by
    unfold mdeg fB
    rw [filter_image, card_image_of_injective _ (liftT_injective T)]
    congr 1
    exact filter_congr fun w hw => by
      simp only [fEnds_liftT (hp w hw).1]
  rw [hB]
  exact completion_dvd hir.le hM hdvd (disjoint_of_subset_right hAWZ hTZ) hTc
    (lE ends Z endsN T) W hWA _ (cf_spec hgjw) hrq.le S hS

/-- The constant of the flat step. -/
def flatConst (q r Cl : ℕ) : ℕ :=
  Cl + 2 ^ (q + r + Cl * r) * fakeModulus q r * 2 ^ q * fakeModulus q r + 2

/-- **The flat step: from `i`-flat to `(i-1)`-flat.**  Let `X` be an `i`-flat `r`-multigraph
with respect to the reserve `Z` (`i < r < q`), let `Z₀ T W ⊆ Z` be a set of `q + r` vertices for
every outside part `T` and link piece `W` (the support of the completion of the lifted piece
`T * W`; it may depend on the piece, so that completions can later be spread out), and suppose
that the link of every outside `i`-set `T` has a `K_{q-i}^{r-i}`-multi-refiner with constant `Cl`
and empty residue, made of new copies inside `Z`.  Then `X` has a residual `K_q^r`-refiner with
constant `flatConst q r Cl` (independent of `X`, `Z` and of the number of links) whose residue is
`(i-1)`-flat and contained in `X ∪ R`; the only old copies in the residue are those already with
fewer than `i` outside vertices; the new copies carry new labels, and each one lies inside
`T ∪ Z` for some outside `i`-set `T` of `X` (locality of the new copies). -/
theorem flatStep_struct {q r i Cl : ℕ} {X : Finset E} {RN : Finset V → Finset N}
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
      (∀ c ∈ R, (∃ T ∈ outParts ends Z i X, ∃ y ∈ RN T, c = Sum.inr (Sum.inl (T, y))) ∨
        ∃ t ∈ fI ends Z i X 𝒲, ∃ k ≤ fakeModulus q r,
          c ∈ compLab ends Z endsN q r i (fakeModulus q r) (Z₀ t.1 t.2) t.1 t.2 k) ∧
      (∀ S : Finset V, pdeg (fEnds ends endsN) 𝒲' S ≤
        2 * ((fI ends Z i X 𝒲).filter fun t =>
          S ⊆ t.1 ∪ AW ends Z endsN (Z₀ t.1 t.2) t.1 t.2).card) := by
  set M := fakeModulus q r with hMdef
  have hM : 1 ≤ M := fakeModulus_pos hrq.le
  have hdvd : ∀ s < r, (q - s).choose (r - s) ∣ M := fun s hs => dvd_fakeModulus hs
  set I := fI ends Z i X 𝒲 with hIdef
  set Cc : Finset V × Finset (E ⊕ N) → ℕ → Finset (E ⊕ FLab V E N) :=
    fun t k => compLab ends Z endsN q r i M (Z₀ t.1 t.2) t.1 t.2 k with hCc
  set X' : Finset (E ⊕ FLab V E N) := X.image Sum.inl with hX'
  set R₀ := fR₀ ends Z i X RN with hR₀
  set Xact : Finset (E ⊕ FLab V E N) := fXact ends Z i X with hXact
  set CC := 2 ^ (q + r + Cl * r) * M * 2 ^ q with hCC
  obtain ⟨J₀, hJ₀I, hJ₀d, hJ₀⟩ := flat_base hX hL (empty_subset X) (mIsDivisible_empty q r ends)
  rw [image_empty, empty_inter, union_empty] at hJ₀
  set Fix := J₀.biUnion fun t => Cc t M with hFix
  -- basic facts
  have hCdisj : ∀ t ∈ I, ∀ k, ∀ t' ∈ I, ∀ k', (t, k) ≠ (t', k') →
      Disjoint (Cc t k) (Cc t' k') := by
    intro t _ k t' _ k' hne
    exact compLab_disj fun h => hne (by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2)
  have hsame : ∀ t ∈ I, ∀ k, ∀ S, mdeg (fEnds ends endsN) (Cc t k) S =
      mdeg (fEnds ends endsN) (Cc t 0) S := by
    intro t _ k S
    simp only [hCc]
    rw [mdeg_compLab, mdeg_compLab]
  have hpiece : ∀ t ∈ I, t.1 ∈ outParts ends Z i X ∧ t.2 ∈ 𝒲 t.1 := fun t ht => mem_fI.1 ht
  have hCends : ∀ t ∈ I, ∀ k, ∀ c ∈ Cc t k,
      (fEnds ends endsN c).card = r ∧ (fEnds ends endsN c \ Z).card < i := by
    intro t ht k c hc
    obtain ⟨hT, hW⟩ := hpiece t ht
    exact compLab_ends (hZ₀ _ _) (fun w hw => (link_piece_props hL hT hW w hw).2.1)
      (outParts_card hT).1 hc
  have hCtag : ∀ t k, ∀ c ∈ Cc t k, ∃ l : CLab V E N, c = Sum.inr (Sum.inr l) ∧ l.2.2.1 = k := by
    intro t k c hc
    obtain ⟨l, h1, -, -, h3, -⟩ := compLab_tag hc
    exact ⟨l, h1, h3⟩
  have hX'tag : ∀ c ∈ X', ∀ l : CLab V E N, c ≠ Sum.inr (Sum.inr l) := by
    intro c hc l h
    obtain ⟨x, -, rfl⟩ := mem_image.1 hc
    simp at h
  have hR₀tag : ∀ c ∈ R₀, ∀ l : CLab V E N, c ≠ Sum.inr (Sum.inr l) := by
    intro c hc l h
    simp only [hR₀, fR₀, mem_biUnion, mem_image] at hc
    obtain ⟨T, -, y, -, rfl⟩ := hc
    simp at h
  have hFix_mem : ∀ c ∈ Fix, ∃ t ∈ I, c ∈ Cc t M := by
    intro c hc
    obtain ⟨t, ht, hc⟩ := mem_biUnion.1 hc
    exact ⟨t, hJ₀I ht, hc⟩
  have hPdiv : ∀ t ∈ I, MIsDivisible q r (fEnds ends endsN) (fB t ∪ Cc t 0) :=
    fun t ht => flat_piece_div hir hrq hL (hZ₀ t.1 t.2) (hZ₀c t.1 t.2).ge hM hdvd ht
  have hpd : PairedData q r (fEnds ends endsN) X' R₀ Xact I fB M Cc Fix Cl CC := by
    refine ⟨hM, ?_, ?_, ?_, ?_, ?_, ?_, fun t ht k _ t' ht' k' _ hne => hCdisj t ht k t' ht' k' hne,
      ?_, ?_, ?_, hPdiv, ?_, ?_, ?_⟩
    · exact image_subset_image (filter_subset _ _)
    · rw [disjoint_left]
      intro c hc hc'
      obtain ⟨x, -, rfl⟩ := mem_image.1 hc
      simp only [hR₀, fR₀, mem_biUnion, mem_image] at hc'
      obtain ⟨T, -, y, -, h⟩ := hc'
      simp at h
    · intro t ht c hc
      obtain ⟨hT, hW⟩ := hpiece t ht
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hc
      rcases mem_LV.1 (link_piece_props hL hT hW w hw).1 with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
      · refine mem_union_left _ (mem_image.2 ⟨x, mem_filter.2 ⟨(mem_filter.1 hx).1, ?_⟩, rfl⟩)
        rw [(mem_filter.1 hx).2]; exact (outParts_card hT).1
      · exact mem_union_right _ (mem_biUnion.2 ⟨t.1, hT, mem_image.2 ⟨y, hy, rfl⟩⟩)
    · intro t ht
      obtain ⟨hT, hW⟩ := hpiece t ht
      exact card_image_le.trans ((hL.ref t.1 hT).card_le t.2 hW)
    · intro c _
      by_cases hex : ∃ t ∈ I, c ∈ fB t
      · obtain ⟨⟨T, W⟩, ht, hc⟩ := hex
        obtain ⟨hT, hW⟩ := hpiece _ ht
        obtain ⟨w, hw, rfl⟩ := mem_image.1 hc
        have hwLV := (link_piece_props hL hT hW w hw).1
        refine (card_le_card (t := ((𝒲 T).filter fun W' => w ∈ W').image fun W' => (T, W'))
          ?_).trans (card_image_le.trans ((hL.ref T hT).mult_le w hwLV))
        intro t' ht'
        obtain ⟨ht'I, hc'⟩ := mem_filter.1 ht'
        obtain ⟨hT', hW'⟩ := hpiece t' ht'I
        obtain ⟨w', hw', h⟩ := mem_image.1 hc'
        obtain ⟨h1, h2⟩ := liftT_eq (link_piece_props hL hT' hW' w' hw').1 hwLV h
        have h1' : t'.1 = T := h1
        refine mem_image.2 ⟨t'.2, mem_filter.2 ⟨by rw [← h1']; exact hW', h2 ▸ hw'⟩, ?_⟩
        exact Prod.ext h1'.symm rfl
      · push_neg at hex
        rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun t ht => hex t ht)]
        exact Nat.zero_le _
    · intro t ht k _
      obtain ⟨hT, hW⟩ := hpiece t ht
      have hp := link_piece_props hL hT hW
      have hAW : (AW ends Z endsN (Z₀ t.1 t.2) t.1 t.2).card ≤ q + r + Cl * r := by
        refine (AW_card_le (r := r) fun w hw => ?_).trans ?_
        · rw [(hp w hw).2.2]; exact Nat.sub_le _ _
        · rw [hZ₀c]
          exact Nat.add_le_add_left (Nat.mul_le_mul_right _ ((hL.ref t.1 hT).card_le t.2 hW)) _
      refine (card_compLab_le hM fun Q hQ => ?_).trans ?_
      · refine (card_union_le _ _).trans ?_
        rw [(outParts_card hT).1, (mem_powersetCard.1 hQ).2]; omega
      · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
          (Nat.pow_le_pow_right (by norm_num) hAW))
    · intro t ht k hk
      rw [disjoint_left]
      intro c hc hc'
      obtain ⟨l, rfl, hlk⟩ := hCtag t k c hc
      rcases mem_union.1 hc' with hc' | hc'
      · rcases mem_union.1 hc' with hc' | hc'
        · exact hX'tag _ hc' l rfl
        · exact hR₀tag _ hc' l rfl
      · obtain ⟨t', -, hc'⟩ := mem_biUnion.1 hc'
        obtain ⟨l', h, hl'k⟩ := hCtag t' M _ hc'
        simp only [Sum.inr.injEq] at h
        subst h
        omega
    · rw [disjoint_left]
      intro c hc hc'
      obtain ⟨t, -, hc⟩ := mem_biUnion.1 hc
      obtain ⟨l, rfl, -⟩ := hCtag t M _ hc
      rcases mem_union.1 hc' with hc' | hc'
      · exact hX'tag _ hc' l rfl
      · exact hR₀tag _ hc' l rfl
    · intro c hc
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hc; exact hXr x hx
      · rcases mem_union.1 hc with hc | hc
        · rcases mem_union.1 hc with hc | hc
          · simp only [hR₀, fR₀, mem_biUnion, mem_image] at hc
            obtain ⟨T, hT, y, hy, rfl⟩ := hc
            obtain ⟨hTc, hTZ⟩ := outParts_card hT
            have hyLV : (Sum.inr y : E ⊕ N) ∈ LV ends Z X RN T :=
              mem_union_right _ (mem_image_of_mem _ hy)
            have h1 : (endsN T y).card = r - i := (hL.ref T hT).rgraph _ hyLV
            show (T ∪ endsN T y).card = r
            rw [card_union_of_disjoint (disjoint_of_subset_right (hL.inZ T hT y hy) hTZ), hTc,
              h1]
            omega
          · obtain ⟨t, ht, k, -, hc⟩ := mem_allC.1 hc
            exact (hCends t ht k c hc).1
        · obtain ⟨t, ht, hc⟩ := hFix_mem c hc
          exact (hCends t ht M c hc).1
    · intro t ht
      refine divisible_copies (Cc t) (fun k _ k' _ hne => hCdisj t ht k t ht k' (by simpa using hne))
        (fun k _ S => hsame t ht k S) hdvd
    · exact fix_divisible hM hdvd hJ₀I hJ₀d hJ₀ (fun t ht => hPdiv t (hJ₀I ht)) hsame hCdisj
        (fun t _ t' _ k => fB_disj_compLab t)
    · intro L hL' hLdiv
      set L₀ := X.filter fun x => (Sum.inl x : E ⊕ FLab V E N) ∈ L with hL₀
      have hLL : L₀.image Sum.inl = L := by
        ext c
        constructor
        · rintro hc
          obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
          exact (mem_filter.1 hx).2
        · intro hc
          obtain ⟨x, hx, rfl⟩ := mem_image.1 (hL' hc)
          exact mem_image_of_mem _ (mem_filter.2 ⟨hx, hc⟩)
      have hL₀div : MIsDivisible q r ends L₀ := by
        intro S hS
        have := hLdiv S hS
        rw [← hLL] at this
        unfold mdeg at this ⊢
        rwa [filter_image, card_image_of_injective _ Sum.inl_injective] at this
      obtain ⟨J, hJI, hJd, hJ⟩ := flat_base hX hL (filter_subset _ X) hL₀div
      exact ⟨J, hJI, hJd, by rw [hJ, hLL]⟩
  have hCloc : ∀ t ∈ I, ∀ k, ∀ c ∈ Cc t k, fEnds ends endsN c ⊆ t.1 ∪ Z := by
    intro t ht k c hc
    obtain ⟨hT, hW⟩ := hpiece t ht
    obtain ⟨Q, hQ, j, -, e, he, rfl⟩ := mem_compLab.1 hc
    have hQZ : Q ⊆ Z := (mem_powersetCard.1 hQ).1.trans
      (AW_subset (hZ₀ _ _) fun w hw => (link_piece_props hL hT hW w hw).2.1)
    exact (mem_powersetCard.1 (mem_filter.1 he).1).1.trans (union_subset_union subset_rfl hQZ)
  have h := pairedStep hpd
  refine ⟨_, _, _, h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases mem_union.1 hc with hc | hc
    · rcases mem_union.1 hc with hc | hc
      · obtain ⟨hcX, hcA⟩ := mem_sdiff.1 hc
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hcX
        have hne : (ends x \ Z).card ≠ i := fun h' =>
          hcA (mem_image.2 ⟨x, mem_filter.2 ⟨hx, h'⟩, rfl⟩)
        have := hX x hx
        show (ends x \ Z).card ≤ i - 1
        omega
      · obtain ⟨t, ht, k, -, -, hc⟩ := mem_tailC.1 hc
        have := (hCends t ht k c hc).2
        omega
    · obtain ⟨t, ht, hc⟩ := hFix_mem c hc
      have := (hCends t ht M c hc).2
      omega
  · intro x hx
    rcases mem_union.1 hx with hx | hx
    · rcases mem_union.1 hx with hx | hx
      · obtain ⟨hcX, hcA⟩ := mem_sdiff.1 hx
        obtain ⟨x', hx', h⟩ := mem_image.1 hcX
        obtain rfl := Sum.inl_injective h
        refine ⟨hx', ?_⟩
        have hne : (ends x' \ Z).card ≠ i := fun h' =>
          hcA (mem_image.2 ⟨x', mem_filter.2 ⟨hx', h'⟩, rfl⟩)
        have := hX x' hx'
        omega
      · obtain ⟨t, -, k, -, -, hc⟩ := mem_tailC.1 hx
        obtain ⟨l, h, -⟩ := hCtag t k _ hc
        simp at h
    · obtain ⟨t, -, hc⟩ := mem_biUnion.1 hx
      obtain ⟨l, h, -⟩ := hCtag t M _ hc
      simp at h
  · intro c hc
    rcases mem_union.1 hc with hc | hc
    · rcases mem_union.1 hc with hc | hc
      · exact mem_union_left _ (mem_sdiff.1 hc).1
      · obtain ⟨t, ht, k, hk1, hkM, hc⟩ := mem_tailC.1 hc
        exact mem_union_right _ (mem_union_left _ (mem_union_right _
          (mem_allC.2 ⟨t, ht, k, hkM, hc⟩)))
    · exact mem_union_right _ (mem_union_right _ hc)
  · intro c hc x hcx
    subst hcx
    rcases mem_union.1 hc with hc | hc
    · rcases mem_union.1 hc with hc | hc
      · simp only [hR₀, fR₀, mem_biUnion, mem_image] at hc
        obtain ⟨T, -, y, -, h⟩ := hc
        simp at h
      · obtain ⟨t, -, k, -, hc⟩ := mem_allC.1 hc
        obtain ⟨l, h, -⟩ := hCtag t k _ hc
        simp at h
    · obtain ⟨t, -, hc⟩ := mem_biUnion.1 hc
      obtain ⟨l, h, -⟩ := hCtag t M _ hc
      simp at h
  · intro c hc
    rcases mem_union.1 hc with hc | hc
    · rcases mem_union.1 hc with hc | hc
      · simp only [hR₀, fR₀, mem_biUnion, mem_image] at hc
        obtain ⟨T, hT, y, hy, rfl⟩ := hc
        exact ⟨T, hT, union_subset_union subset_rfl (hL.inZ T hT y hy)⟩
      · obtain ⟨t, ht, k, -, hc⟩ := mem_allC.1 hc
        exact ⟨t.1, (hpiece t ht).1, hCloc t ht k c hc⟩
    · obtain ⟨t, ht, hc⟩ := hFix_mem c hc
      exact ⟨t.1, (hpiece t ht).1, hCloc t ht M c hc⟩
  · intro c hc
    rcases mem_union.1 hc with hc | hc
    · rcases mem_union.1 hc with hc | hc
      · simp only [hR₀, fR₀, mem_biUnion, mem_image] at hc
        obtain ⟨T, hT, y, hy, rfl⟩ := hc
        exact Or.inl ⟨T, hT, y, hy, rfl⟩
      · obtain ⟨t, ht, k, hk, hc⟩ := mem_allC.1 hc
        exact Or.inr ⟨t, ht, k, hk.le, hc⟩
    · obtain ⟨t, ht, hc⟩ := hFix_mem c hc
      exact Or.inr ⟨t, ht, M, le_rfl, hc⟩
  · intro S
    have hspanC : ∀ t k, ∀ c ∈ Cc t k,
        fEnds ends endsN c ⊆ t.1 ∪ AW ends Z endsN (Z₀ t.1 t.2) t.1 t.2 := by
      intro t k c hc
      obtain ⟨Q, hQ, j, -, e, he, rfl⟩ := mem_compLab.1 hc
      show e ⊆ t.1 ∪ AW ends Z endsN (Z₀ t.1 t.2) t.1 t.2
      exact (mem_powersetCard.1 (mem_filter.1 he).1).1.trans
        (union_subset_union subset_rfl (mem_powersetCard.1 hQ).1)
    have hspanB : ∀ t ∈ I, ∀ c ∈ fB t,
        fEnds ends endsN c ⊆ t.1 ∪ AW ends Z endsN (Z₀ t.1 t.2) t.1 t.2 := by
      intro t ht c hc v hv
      obtain ⟨hT, hW⟩ := hpiece t ht
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hc
      have hwAW : lE ends Z endsN t.1 w ⊆ AW ends Z endsN (Z₀ t.1 t.2) t.1 t.2 :=
        (subset_biUnion_of_mem _ hw).trans subset_union_right
      rcases mem_LV.1 (link_piece_props hL hT hW w hw).1 with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
      · change v ∈ ends x at hv
        by_cases hvZ : v ∈ Z
        · exact mem_union_right _ (hwAW (mem_inter.2 ⟨hv, hvZ⟩))
        · refine mem_union_left _ ?_
          rw [← (mem_filter.1 hx).2]
          exact mem_sdiff.2 ⟨hv, hvZ⟩
      · change v ∈ t.1 ∪ endsN t.1 y at hv
        rcases mem_union.1 hv with hv | hv
        · exact mem_union_left _ hv
        · exact mem_union_right _ (hwAW hv)
    have hP : ∀ t ∈ I, (pairP fB Cc t).biUnion (fEnds ends endsN) ⊆
        t.1 ∪ AW ends Z endsN (Z₀ t.1 t.2) t.1 t.2 := by
      intro t ht v hv
      obtain ⟨c, hc, hvc⟩ := mem_biUnion.1 hv
      rcases mem_union.1 hc with hc | hc
      · exact hspanB t ht c hc hvc
      · exact hspanC t 0 c hc hvc
    have hN : ∀ t ∈ I, (pairN M Cc t).biUnion (fEnds ends endsN) ⊆
        t.1 ∪ AW ends Z endsN (Z₀ t.1 t.2) t.1 t.2 := by
      intro t _ v hv
      obtain ⟨c, hc, hvc⟩ := mem_biUnion.1 hv
      obtain ⟨k, -, hc⟩ := mem_biUnion.1 hc
      exact hspanC t k c hc hvc
    exact pairFamily_pdeg_le (ends := fEnds ends endsN) (I := I) (M := M) (B := fB) (Cc := Cc)
      (fun t => t.1 ∪ AW ends Z endsN (Z₀ t.1 t.2) t.1 t.2) hP hN S

/-- **The flat step: from `i`-flat to `(i-1)`-flat** (see `flatStep_struct`, which also describes
the new copies). -/
theorem flatStep {q r i Cl : ℕ} {X : Finset E} {RN : Finset V → Finset N}
    {𝒲 : Finset V → Finset (Finset (E ⊕ N))} {Z₀ : Finset V → Finset (E ⊕ N) → Finset V}
    (hir : i < r) (hrq : r < q) (hXr : MIsRGraph r ends X) (hX : IsFlat i Z ends X)
    (hL : LinkRefiners q r i Cl ends Z X endsN RN 𝒲) (hZ₀ : ∀ T W, Z₀ T W ⊆ Z)
    (hZ₀c : ∀ T W, (Z₀ T W).card = q + r) :
    ∃ R Y : Finset (E ⊕ FLab V E N), ∃ 𝒲' : Finset (Finset (E ⊕ FLab V E N)),
      IsResidualMultiRefiner q r (flatConst q r Cl) (fEnds ends endsN) (X.image Sum.inl) R Y 𝒲' ∧
      IsFlat (i - 1) Z (fEnds ends endsN) Y ∧
      (∀ x, Sum.inl x ∈ Y → x ∈ X ∧ (ends x \ Z).card < i) ∧
      Y ⊆ X.image Sum.inl ∪ R ∧ (∀ c ∈ R, ∀ x, c ≠ Sum.inl x) ∧
      (∀ c ∈ R, ∃ T ∈ outParts ends Z i X, fEnds ends endsN c ⊆ T ∪ Z) := by
  obtain ⟨R, Y, 𝒲', h1, h2, h3, h4, h5, h6, -⟩ := flatStep_struct hir hrq hXr hX hL hZ₀ hZ₀c
  exact ⟨R, Y, 𝒲', h1, h2, h3, h4, h5, h6⟩

end Flat

end RefinedAbsorption.FlatDown
