module
public import RequestProject.RefineDown.Transport

/-!
# Flatness and the paired completion step

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (refine down, Sections 3–4).  Lean
formalization: Juan Pablo Traverso Gianini, Apache-2.0.

* `IsFlat i Z ends Y`: every copy of `Y` has at most `i` vertices outside the reserve `Z`.
* `MIsDivisible.of_union`: divisibility of a difference of divisible multigraphs.
* `divisible_sup`: a pairwise disjoint union of divisible multigraphs is divisible.
* `pairedStep`: the combinatorial core shared by every refine-down step.  Each *base piece*
  `B t` receives `M` disjoint copies `Cc t 0, …, Cc t (M-1)` of a *completion*.  If `B t` is
  used, it is completed by `Cc t 0` and the other `M - 1` copies go to the residue; if it is not
  used, the `M` copies form a piece by themselves.  Every copy then lies in at most `CB + 2`
  pieces, independently of how many base pieces there are.
-/

@[expose] public section

namespace RefinedAbsorption.FlatDown

open Finset RefinedAbsorption.MultiRefiner

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- `Y` is `i`-flat with respect to the reserve `Z`. -/
def IsFlat (i : ℕ) (Z : Finset V) (ends : E → Finset V) (Y : Finset E) : Prop :=
  ∀ x ∈ Y, (ends x \ Z).card ≤ i

omit [DecidableEq E] in
theorem IsFlat.mono {i j : ℕ} {Z : Finset V} {ends : E → Finset V} {Y Y' : Finset E}
    (h : IsFlat i Z ends Y) (hY : Y' ⊆ Y) (hij : i ≤ j) : IsFlat j Z ends Y' :=
  fun x hx => (h x (hY hx)).trans hij

/-- Divisibility of a difference. -/
theorem MIsDivisible.of_union {q r : ℕ} {ends : E → Finset V} {A B : Finset E}
    (hAB : Disjoint A B) (hU : MIsDivisible q r ends (A ∪ B)) (hA : MIsDivisible q r ends A) :
    MIsDivisible q r ends B := by
  intro S hS
  have h1 := hU S hS
  rw [mdeg_union_of_disjoint ends hAB] at h1
  exact (Nat.dvd_add_right (hA S hS)).1 h1

/-- A pairwise disjoint union of divisible multigraphs is divisible. -/
theorem divisible_sup {q r : ℕ} {ends : E → Finset V} (𝒰 : Finset (Finset E))
    (hpw : (𝒰 : Set (Finset E)).PairwiseDisjoint id)
    (hdiv : ∀ W ∈ 𝒰, MIsDivisible q r ends W) : MIsDivisible q r ends (𝒰.sup id) := by
  induction 𝒰 using Finset.induction_on with
  | empty => exact mIsDivisible_empty q r ends
  | insert W 𝒰 hW ih =>
    rw [sup_insert]
    have hpw' : (𝒰 : Set (Finset E)).PairwiseDisjoint id :=
      hpw.subset (by intro x hx; simp [hx])
    have hd : Disjoint W (𝒰.sup id) := by
      rw [Finset.disjoint_sup_right]
      intro W' hW'
      exact hpw (by simp) (by simp [hW']) (fun h => hW (h ▸ hW'))
    exact MIsDivisible.union hd (hdiv W (by simp)) (ih hpw' fun W' hW' => hdiv W' (by simp [hW']))

/-- If all `M` disjoint multigraphs `C k` have the same degrees and every relevant binomial
coefficient divides `M`, their union is divisible. -/
theorem divisible_copies {q r M : ℕ} {ends : E → Finset V} (C : ℕ → Finset E)
    (hdisj : ∀ k < M, ∀ k' < M, k ≠ k' → Disjoint (C k) (C k'))
    (hsame : ∀ k < M, ∀ S : Finset V, mdeg ends (C k) S = mdeg ends (C 0) S)
    (hM : ∀ s < r, (q - s).choose (r - s) ∣ M) :
    MIsDivisible q r ends ((range M).biUnion C) := by
  intro S hS
  have h1 : mdeg ends ((range M).biUnion C) S = ∑ k ∈ range M, mdeg ends (C k) S := by
    unfold mdeg
    rw [filter_biUnion, card_biUnion]
    intro k hk k' hk' hne
    exact disjoint_filter_filter (hdisj k (mem_range.1 hk) k' (mem_range.1 hk') hne)
  have : mdeg ends ((range M).biUnion C) S = M * mdeg ends (C 0) S := by
    rw [h1, sum_congr rfl fun k hk => hsame k (mem_range.1 hk) S, sum_const, card_range,
      smul_eq_mul]
  rw [this]
  exact Dvd.dvd.mul_right (hM _ hS) _

/-! ### The paired completion step -/

section Paired

variable {ι : Type*} [DecidableEq ι]

/-- All completion copies. -/
def allC (I : Finset ι) (M : ℕ) (Cc : ι → ℕ → Finset E) : Finset E :=
  I.biUnion fun t => (range M).biUnion (Cc t)

/-- The completion copies sent to the residue when the base piece is used. -/
def tailC (J : Finset ι) (M : ℕ) (Cc : ι → ℕ → Finset E) : Finset E :=
  J.biUnion fun t => (Ico 1 M).biUnion (Cc t)

/-- The piece used when `B t` is used. -/
def pairP (B : ι → Finset E) (Cc : ι → ℕ → Finset E) (t : ι) : Finset E := B t ∪ Cc t 0

/-- The piece used when `B t` is not used. -/
def pairN (M : ℕ) (Cc : ι → ℕ → Finset E) (t : ι) : Finset E := (range M).biUnion (Cc t)

/-- The family of the paired step. -/
def pairFamily (I : Finset ι) (M : ℕ) (B : ι → Finset E) (Cc : ι → ℕ → Finset E) :
    Finset (Finset E) :=
  I.image (pairP B Cc) ∪ I.image (pairN M Cc)

omit [DecidableEq ι] in
theorem mem_allC {I : Finset ι} {M : ℕ} {Cc : ι → ℕ → Finset E} {c : E} :
    c ∈ allC I M Cc ↔ ∃ t ∈ I, ∃ k < M, c ∈ Cc t k := by
  simp [allC]

omit [DecidableEq ι] in
theorem mem_tailC {J : Finset ι} {M : ℕ} {Cc : ι → ℕ → Finset E} {c : E} :
    c ∈ tailC J M Cc ↔ ∃ t ∈ J, ∃ k, 1 ≤ k ∧ k < M ∧ c ∈ Cc t k := by
  simp [tailC, and_assoc]

/-- Data and hypotheses of a paired completion step. -/
structure PairedData (q r : ℕ) (ends : E → Finset V) (X R₀ Xact : Finset E) (I : Finset ι)
    (B : ι → Finset E) (M : ℕ) (Cc : ι → ℕ → Finset E) (Fix : Finset E) (CB CC : ℕ) : Prop where
  hM : 1 ≤ M
  act : Xact ⊆ X
  disjXR : Disjoint X R₀
  B_sub : ∀ t ∈ I, B t ⊆ Xact ∪ R₀
  B_card : ∀ t ∈ I, (B t).card ≤ CB
  B_mult : ∀ c ∈ X ∪ R₀, (I.filter fun t => c ∈ B t).card ≤ CB
  C_card : ∀ t ∈ I, ∀ k < M, (Cc t k).card ≤ CC
  C_disj : ∀ t ∈ I, ∀ k < M, ∀ t' ∈ I, ∀ k' < M, (t, k) ≠ (t', k') → Disjoint (Cc t k) (Cc t' k')
  C_new : ∀ t ∈ I, ∀ k < M, Disjoint (Cc t k) (X ∪ R₀ ∪ Fix)
  fix_new : Disjoint Fix (X ∪ R₀)
  rgraph : MIsRGraph r ends (X ∪ (R₀ ∪ allC I M Cc ∪ Fix))
  P_div : ∀ t ∈ I, MIsDivisible q r ends (B t ∪ Cc t 0)
  N_div : ∀ t ∈ I, MIsDivisible q r ends ((range M).biUnion (Cc t))
  R_div : MIsDivisible q r ends (R₀ ∪ allC I M Cc ∪ Fix)
  base : ∀ L ⊆ X, MIsDivisible q r ends L → ∃ J ⊆ I,
    (∀ t ∈ J, ∀ t' ∈ J, t ≠ t' → Disjoint (B t) (B t')) ∧ J.biUnion B = R₀ ∪ (L ∩ Xact)

variable {q r : ℕ} {ends : E → Finset V} {X R₀ Xact : Finset E} {I : Finset ι}
  {B : ι → Finset E} {M : ℕ} {Cc : ι → ℕ → Finset E} {Fix : Finset E} {CB CC : ℕ}

omit [DecidableEq ι] in
theorem PairedData.C_ne_X (h : PairedData q r ends X R₀ Xact I B M Cc Fix CB CC) {t : ι}
    (ht : t ∈ I) {k : ℕ} (hk : k < M) {c : E} (hc : c ∈ Cc t k) : c ∉ X ∪ R₀ ∪ Fix :=
  fun h' => disjoint_left.1 (h.C_new t ht k hk) hc h'

theorem PairedData.C_unique (h : PairedData q r ends X R₀ Xact I B M Cc Fix CB CC) {t t' : ι}
    (ht : t ∈ I) (ht' : t' ∈ I) {k k' : ℕ} (hk : k < M) (hk' : k' < M) {c : E}
    (hc : c ∈ Cc t k) (hc' : c ∈ Cc t' k') : t = t' ∧ k = k' := by
  by_contra hne
  have : (t, k) ≠ (t', k') := fun h' => hne (by simp_all)
  exact disjoint_left.1 (h.C_disj t ht k hk t' ht' k' hk' this) hc hc'

omit [DecidableEq ι] in
theorem PairedData.B_not_C (h : PairedData q r ends X R₀ Xact I B M Cc Fix CB CC) {t t' : ι}
    (ht : t ∈ I) (ht' : t' ∈ I) {k : ℕ} (hk : k < M) {c : E} (hc : c ∈ B t) :
    c ∉ Cc t' k := by
  intro hc'
  apply h.C_ne_X ht' hk hc'
  rcases mem_union.1 (h.B_sub t ht hc) with h1 | h1
  · exact mem_union_left _ (mem_union_left _ (h.act h1))
  · exact mem_union_left _ (mem_union_right _ h1)

/-- **The paired completion step.** -/
theorem pairedStep (h : PairedData q r ends X R₀ Xact I B M Cc Fix CB CC) :
    IsResidualMultiRefiner q r (CB + CC * M + 2) ends X (R₀ ∪ allC I M Cc ∪ Fix)
      ((X \ Xact) ∪ tailC I M Cc ∪ Fix) (pairFamily I M B Cc) := by
  have hM := h.hM
  -- membership in pieces
  have hmemP : ∀ t c, c ∈ pairP B Cc t ↔ c ∈ B t ∨ c ∈ Cc t 0 := fun t c => mem_union
  have hmemN : ∀ t c, c ∈ pairN M Cc t ↔ ∃ k < M, c ∈ Cc t k := fun t c => by
    simp [pairN]
  refine ⟨h.rgraph, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- disjointness of `X` and the refiner
    rw [disjoint_left]
    intro c hcX hc
    rcases mem_union.1 hc with hc | hc
    · rcases mem_union.1 hc with hc | hc
      · exact disjoint_left.1 h.disjXR hcX hc
      · obtain ⟨t, ht, k, hk, hc⟩ := mem_allC.1 hc
        exact h.C_ne_X ht hk hc (mem_union_left _ (mem_union_left _ hcX))
    · exact disjoint_left.1 h.fix_new hc (mem_union_left _ hcX)
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨t, ht, rfl⟩ := mem_image.1 hW; exact h.P_div t ht
    · obtain ⟨t, ht, rfl⟩ := mem_image.1 hW; exact h.N_div t ht
  · intro W hW c hc
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨t, ht, rfl⟩ := mem_image.1 hW
      rcases (hmemP t c).1 hc with hc | hc
      · rcases mem_union.1 (h.B_sub t ht hc) with h1 | h1
        · exact mem_union_left _ (h.act h1)
        · exact mem_union_right _ (mem_union_left _ (mem_union_left _ h1))
      · exact mem_union_right _ (mem_union_left _ (mem_union_right _
          (mem_allC.2 ⟨t, ht, 0, hM, hc⟩)))
    · obtain ⟨t, ht, rfl⟩ := mem_image.1 hW
      obtain ⟨k, hk, hc⟩ := (hmemN t c).1 hc
      exact mem_union_right _ (mem_union_left _ (mem_union_right _
        (mem_allC.2 ⟨t, ht, k, hk, hc⟩)))
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨t, ht, rfl⟩ := mem_image.1 hW
      refine (card_union_le _ _).trans ?_
      have := h.B_card t ht
      have := h.C_card t ht 0 hM
      nlinarith
    · obtain ⟨t, ht, rfl⟩ := mem_image.1 hW
      refine (card_biUnion_le).trans ?_
      calc ∑ k ∈ range M, (Cc t k).card ≤ ∑ _k ∈ range M, CC :=
            sum_le_sum fun k hk => h.C_card t ht k (mem_range.1 hk)
        _ = CC * M := by simp [mul_comm]
        _ ≤ CB + CC * M + 2 := by omega
  · -- multiplicity
    intro c hc
    rw [pairFamily, filter_union]
    refine (card_union_le _ _).trans ?_
    rw [filter_image, filter_image]
    refine (Nat.add_le_add card_image_le card_image_le).trans ?_
    by_cases hcC : ∃ t ∈ I, ∃ k < M, c ∈ Cc t k
    · obtain ⟨t₀, ht₀, k₀, hk₀, hc₀⟩ := hcC
      have h1 : (I.filter fun t => c ∈ pairP B Cc t) ⊆ {t₀} := by
        intro t ht
        obtain ⟨ht, hct⟩ := mem_filter.1 ht
        rcases (hmemP t c).1 hct with hct | hct
        · exact absurd hc₀ (h.B_not_C ht ht₀ hk₀ hct)
        · exact mem_singleton.2 (h.C_unique ht ht₀ hM hk₀ hct hc₀).1
      have h2 : (I.filter fun t => c ∈ pairN M Cc t) ⊆ {t₀} := by
        intro t ht
        obtain ⟨ht, hct⟩ := mem_filter.1 ht
        obtain ⟨k, hk, hct⟩ := (hmemN t c).1 hct
        exact mem_singleton.2 (h.C_unique ht ht₀ hk hk₀ hct hc₀).1
      have := card_le_card h1
      have := card_le_card h2
      simp only [card_singleton] at *
      omega
    · push_neg at hcC
      have hN : (I.filter fun t => c ∈ pairN M Cc t) = ∅ := by
        refine filter_eq_empty_iff.2 fun t ht hct => ?_
        obtain ⟨k, hk, hct⟩ := (hmemN t c).1 hct
        exact hcC t ht k hk hct
      have hP : (I.filter fun t => c ∈ pairP B Cc t) = I.filter fun t => c ∈ B t := by
        refine filter_congr fun t ht => ?_
        rw [hmemP]
        exact ⟨fun h' => h'.resolve_right (hcC t ht 0 hM), Or.inl⟩
      rw [hN, hP, card_empty]
      by_cases hcXR : c ∈ X ∪ R₀
      · have := h.B_mult c hcXR; omega
      · have : (I.filter fun t => c ∈ B t) = ∅ := by
          refine filter_eq_empty_iff.2 fun t ht hct => hcXR ?_
          rcases mem_union.1 (h.B_sub t ht hct) with h1 | h1
          · exact mem_union_left _ (h.act h1)
          · exact mem_union_right _ h1
        rw [this]; simp
  · -- decomposition
    intro L hL hLdiv
    obtain ⟨J, hJI, hJpw, hJeq⟩ := h.base L hL hLdiv
    set 𝒰 : Finset (Finset E) := J.image (pairP B Cc) ∪ (I \ J).image (pairN M Cc) with h𝒰
    set Res : Finset E := (L \ Xact) ∪ tailC J M Cc ∪ Fix with hRes
    -- membership in the union of the chosen pieces
    have hsupmem : ∀ c, c ∈ 𝒰.sup id ↔ (∃ t ∈ J, c ∈ B t ∨ c ∈ Cc t 0) ∨
        (∃ t ∈ I \ J, ∃ k < M, c ∈ Cc t k) := by
      intro c
      simp only [mem_sup, id, h𝒰, mem_union, mem_image]
      constructor
      · rintro ⟨W, hW | hW, hcW⟩
        · obtain ⟨t, ht, rfl⟩ := hW
          exact Or.inl ⟨t, ht, (hmemP t c).1 hcW⟩
        · obtain ⟨t, ht, rfl⟩ := hW
          exact Or.inr ⟨t, ht, (hmemN t c).1 hcW⟩
      · rintro (⟨t, ht, hc⟩ | ⟨t, ht, hc⟩)
        · exact ⟨_, Or.inl ⟨t, ht, rfl⟩, (hmemP t c).2 hc⟩
        · exact ⟨_, Or.inr ⟨t, ht, rfl⟩, (hmemN t c).2 hc⟩
    have hJB : ∀ c, (∃ t ∈ J, c ∈ B t) ↔ c ∈ R₀ ∪ (L ∩ Xact) := by
      intro c; rw [← hJeq, mem_biUnion]
    have hdisjSR : Disjoint (𝒰.sup id) Res := by
      rw [disjoint_left]
      intro c hc hcR
      rw [hsupmem] at hc
      simp only [hRes, mem_union, mem_sdiff, mem_tailC] at hcR
      rcases hc with ⟨t, ht, hc⟩ | ⟨t, ht, k, hk, hc⟩
      · rcases hc with hc | hc
        · have hcB := (hJB c).1 ⟨t, ht, hc⟩
          rcases hcR with (⟨hcL, hcA⟩ | ⟨t', ht', k', hk1, hk', hc'⟩) | hcF
          · rcases mem_union.1 hcB with h1 | h1
            · exact disjoint_left.1 h.disjXR (hL hcL) h1
            · exact hcA (mem_inter.1 h1).2
          · exact h.B_not_C (hJI ht) (hJI ht') hk' hc hc'
          · rcases mem_union.1 (h.B_sub t (hJI ht) hc) with h1 | h1
            · exact disjoint_left.1 h.fix_new hcF (mem_union_left _ (h.act h1))
            · exact disjoint_left.1 h.fix_new hcF (mem_union_right _ h1)
        · rcases hcR with (⟨hcL, -⟩ | ⟨t', ht', k', hk1, hk', hc'⟩) | hcF
          · exact h.C_ne_X (hJI ht) hM hc (mem_union_left _ (mem_union_left _ (hL hcL)))
          · have := (h.C_unique (hJI ht) (hJI ht') hM hk' hc hc').2; omega
          · exact h.C_ne_X (hJI ht) hM hc (mem_union_right _ hcF)
      · have htI := (mem_sdiff.1 ht).1
        rcases hcR with (⟨hcL, -⟩ | ⟨t', ht', k', hk1, hk', hc'⟩) | hcF
        · exact h.C_ne_X htI hk hc (mem_union_left _ (mem_union_left _ (hL hcL)))
        · have := (h.C_unique htI (hJI ht') hk hk' hc hc').1
          subst this; exact (mem_sdiff.1 ht).2 ht'
        · exact h.C_ne_X htI hk hc (mem_union_right _ hcF)
    have hunion : 𝒰.sup id ∪ Res = (R₀ ∪ allC I M Cc ∪ Fix) ∪ L := by
      ext c
      simp only [mem_union, hsupmem, hRes, mem_sdiff, mem_tailC, mem_allC]
      constructor
      · rintro ((⟨t, ht, hc | hc⟩ | ⟨t, ht, k, hk, hc⟩) | ((⟨hcL, -⟩ | ⟨t, ht, k, -, hk, hc⟩) | hcF))
        · rcases mem_union.1 ((hJB c).1 ⟨t, ht, hc⟩) with h1 | h1
          · exact Or.inl (Or.inl (Or.inl h1))
          · exact Or.inr (mem_inter.1 h1).1
        · exact Or.inl (Or.inl (Or.inr ⟨t, hJI ht, 0, hM, hc⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨t, ht.1, k, hk, hc⟩))
        · exact Or.inr hcL
        · exact Or.inl (Or.inl (Or.inr ⟨t, hJI ht, k, hk, hc⟩))
        · exact Or.inl (Or.inr hcF)
      · rintro (((hcR | ⟨t, ht, k, hk, hc⟩) | hcF) | hcL)
        · exact Or.inl (Or.inl (by
            obtain ⟨t, ht, hct⟩ := (hJB c).2 (mem_union_left _ hcR)
            exact ⟨t, ht, Or.inl hct⟩))
        · by_cases htJ : t ∈ J
          · by_cases hk0 : k = 0
            · subst hk0; exact Or.inl (Or.inl ⟨t, htJ, Or.inr hc⟩)
            · exact Or.inr (Or.inl (Or.inr ⟨t, htJ, k, by omega, hk, hc⟩))
          · exact Or.inl (Or.inr ⟨t, ⟨ht, htJ⟩, k, hk, hc⟩)
        · exact Or.inr (Or.inr hcF)
        · by_cases hcA : c ∈ Xact
          · obtain ⟨t, ht, hct⟩ := (hJB c).2 (mem_union_right _ (mem_inter.2 ⟨hcL, hcA⟩))
            exact Or.inl (Or.inl ⟨t, ht, Or.inl hct⟩)
          · exact Or.inr (Or.inl (Or.inl ⟨hcL, hcA⟩))
    have hpw : (𝒰 : Set (Finset E)).PairwiseDisjoint id := by
      intro W hW W' hW' hne
      simp only [coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe, h𝒰] at hW hW'
      show Disjoint W W'
      rw [disjoint_left]
      intro c hc hc'
      rcases hW with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ <;> rcases hW' with ⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩
      · have htt : t ≠ t' := fun e => hne (by rw [e])
        rcases (hmemP t c).1 hc with hc | hc <;> rcases (hmemP t' c).1 hc' with hc' | hc'
        · exact disjoint_left.1 (hJpw t ht t' ht' htt) hc hc'
        · exact h.B_not_C (hJI ht) (hJI ht') hM hc hc'
        · exact h.B_not_C (hJI ht') (hJI ht) hM hc' hc
        · exact htt (h.C_unique (hJI ht) (hJI ht') hM hM hc hc').1
      · obtain ⟨k, hk, hc'⟩ := (hmemN t' c).1 hc'
        have ht'I := (mem_sdiff.1 ht').1
        rcases (hmemP t c).1 hc with hc | hc
        · exact h.B_not_C (hJI ht) ht'I hk hc hc'
        · have := (h.C_unique (hJI ht) ht'I hM hk hc hc').1
          subst this; exact (mem_sdiff.1 ht').2 ht
      · obtain ⟨k, hk, hc⟩ := (hmemN t c).1 hc
        have htI := (mem_sdiff.1 ht).1
        rcases (hmemP t' c).1 hc' with hc' | hc'
        · exact h.B_not_C (hJI ht') htI hk hc' hc
        · have := (h.C_unique (hJI ht') htI hM hk hc' hc).1
          subst this; exact (mem_sdiff.1 ht).2 ht'
      · have htt : t ≠ t' := fun e => hne (by rw [e])
        obtain ⟨k, hk, hc⟩ := (hmemN t c).1 hc
        obtain ⟨k', hk', hc'⟩ := (hmemN t' c).1 hc'
        exact htt (h.C_unique (mem_sdiff.1 ht).1 (mem_sdiff.1 ht').1 hk hk' hc hc').1
    have hUdiv : MIsDivisible q r ends (𝒰.sup id) := by
      refine divisible_sup 𝒰 hpw fun W hW => ?_
      rcases mem_union.1 hW with hW | hW
      · obtain ⟨t, ht, rfl⟩ := mem_image.1 hW; exact h.P_div t (hJI ht)
      · obtain ⟨t, ht, rfl⟩ := mem_image.1 hW; exact h.N_div t (mem_sdiff.1 ht).1
    have hRLdiv : MIsDivisible q r ends ((R₀ ∪ allC I M Cc ∪ Fix) ∪ L) := by
      refine MIsDivisible.union ?_ h.R_div hLdiv
      rw [disjoint_left]
      intro c hc hcL
      have hcX := hL hcL
      rcases mem_union.1 hc with hc | hc
      · rcases mem_union.1 hc with hc | hc
        · exact disjoint_left.1 h.disjXR hcX hc
        · obtain ⟨t, ht, k, hk, hc⟩ := mem_allC.1 hc
          exact h.C_ne_X ht hk hc (mem_union_left _ (mem_union_left _ hcX))
      · exact disjoint_left.1 h.fix_new hc (mem_union_left _ hcX)
    refine ⟨𝒰, ?_, Res, ?_, ?_, hpw, hdisjSR, hunion⟩
    · intro W hW
      rcases mem_union.1 hW with hW | hW
      · obtain ⟨t, ht, rfl⟩ := mem_image.1 hW
        exact mem_union_left _ (mem_image_of_mem _ (hJI ht))
      · obtain ⟨t, ht, rfl⟩ := mem_image.1 hW
        exact mem_union_right _ (mem_image_of_mem _ (mem_sdiff.1 ht).1)
    · intro c hc
      simp only [hRes, mem_union, mem_sdiff, mem_tailC] at hc ⊢
      rcases hc with (⟨hcL, hcA⟩ | ⟨t, ht, k, hk1, hk, hc⟩) | hcF
      · exact Or.inl (Or.inl ⟨hL hcL, hcA⟩)
      · exact Or.inl (Or.inr ⟨t, hJI ht, k, hk1, hk, hc⟩)
      · exact Or.inr hcF
    · rw [← hunion] at hRLdiv
      exact MIsDivisible.of_union hdisjSR hRLdiv hUdiv

end Paired

end RefinedAbsorption.FlatDown
