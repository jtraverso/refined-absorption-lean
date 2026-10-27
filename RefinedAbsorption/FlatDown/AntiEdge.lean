module
public import RefinedAbsorption.FlatDown.Basic
public import RefinedAbsorption.Counting
public import RefinedAbsorption.MultiRefiner.FakeEdge

/-!
# The anti-edge step into a reserve

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (refine down, first step).  Lean
formalization: Juan Pablo Traverso Gianini, Apache-2.0.

For every copy `x` of `X` we choose a `(q - r)`-set `Q x` inside the reserve `U`, disjoint from
`x`.  The anti-edge `A_x` consists of the `r`-subsets of `x ∪ Q x` other than `x`; every edge of
`A_x` meets `U`, so `A_x` is `(r-1)`-flat with respect to `U`.  With `M = fakeModulus q r` disjoint
copies of each anti-edge, the paired step (`pairedStep`) gives a residual refiner of `X` whose
residue is `(r-1)`-flat with respect to `U`, in which every piece contains at most one copy of `X`.
-/

@[expose] public section

namespace RefinedAbsorption.FlatDown

open Finset RefinedAbsorption.MultiRefiner

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- Degrees of a multigraph on which `ends` is injective. -/
theorem mdeg_eq_deg_image {ends : E → Finset V} {G : Finset E} (hinj : Set.InjOn ends G)
    (S : Finset V) : mdeg ends G S = deg (G.image ends) S := by
  unfold mdeg deg
  rw [filter_image, card_image_of_injOn (hinj.mono fun x hx => (mem_filter.1 hx).1)]

/-- Divisibility of the clique on a `q`-set. -/
theorem dvd_deg_cliqueEdges {q r : ℕ} {Q S : Finset V} (hQ : Q.card = q) (hS : S.card ≤ r) :
    (q - S.card).choose (r - S.card) ∣ deg (cliqueEdges r Q) S := by
  by_cases h : S ⊆ Q
  · rw [deg, cliqueEdges, card_powersetCard_filter_superset h hS, hQ]
  · rw [deg, cliqueEdges, card_powersetCard_filter_superset_of_not h]
    exact dvd_zero _

/-- A pairwise disjoint union of divisible multigraphs, indexed by a finset. -/
theorem divisible_biUnion {q r : ℕ} {ends : E → Finset V} {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset E)
    (hpw : ∀ t ∈ I, ∀ t' ∈ I, t ≠ t' → Disjoint (F t) (F t'))
    (hdiv : ∀ t ∈ I, MIsDivisible q r ends (F t)) : MIsDivisible q r ends (I.biUnion F) := by
  have h : (I.image F).sup id = I.biUnion F := by
    ext c; simp [mem_sup]
  rw [← h]
  refine divisible_sup _ ?_ ?_
  · intro W hW W' hW' hne
    obtain ⟨t, ht, rfl⟩ := mem_image.1 (mem_coe.1 hW)
    obtain ⟨t', ht', rfl⟩ := mem_image.1 (mem_coe.1 hW')
    exact hpw t ht t' ht' (fun e => hne (by rw [e]))
  · intro W hW
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hW
    exact hdiv t ht

section Anti

variable (r : ℕ) (ends : E → Finset V) (Q : E → Finset V)

/-- The anti-edge of `x` on `x ∪ Q x`. -/
def antiE (x : E) : Finset (Finset V) := (cliqueEdges r (ends x ∪ Q x)).erase (ends x)

/-- Labels of the anti-edge copies: copy, copy index, edge. -/
abbrev ALab (E V : Type*) := E × ℕ × Finset V

/-- Ends of the anti-edge step. -/
def aEnds : E ⊕ ALab E V → Finset V := Sum.elim ends fun y => y.2.2

/-- The `k`-th copy of the anti-edge of `x`. -/
def aC (x : E) (k : ℕ) : Finset (E ⊕ ALab E V) :=
  (antiE r ends Q x).image fun f => Sum.inr (x, k, f)

/-- All anti-edge copies. -/
def aR (X : Finset E) (M : ℕ) : Finset (ALab E V) :=
  X.biUnion fun x => (range M).biUnion fun k => (antiE r ends Q x).image fun f => (x, k, f)

/-- The anti-edge copies of index `≥ 1` (the residue set). -/
def aY (X : Finset E) (M : ℕ) : Finset (ALab E V) :=
  X.biUnion fun x => (Ico 1 M).biUnion fun k => (antiE r ends Q x).image fun f => (x, k, f)

variable {r ends Q}

theorem allC_aC (X : Finset E) (M : ℕ) :
    allC X M (aC r ends Q) = (aR r ends Q X M).image Sum.inr := by
  ext c; simp only [allC, aC, aR, mem_biUnion, mem_image, mem_range]
  constructor
  · rintro ⟨x, hx, k, hk, f, hf, rfl⟩; exact ⟨_, ⟨x, hx, k, hk, f, hf, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, k, hk, f, hf, rfl⟩, rfl⟩; exact ⟨x, hx, k, hk, f, hf, rfl⟩

theorem tailC_aC (X : Finset E) (M : ℕ) :
    tailC X M (aC r ends Q) = (aY r ends Q X M).image Sum.inr := by
  ext c; simp only [tailC, aC, aY, mem_biUnion, mem_image, mem_Ico]
  constructor
  · rintro ⟨x, hx, k, hk, f, hf, rfl⟩; exact ⟨_, ⟨x, hx, k, hk, f, hf, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, k, hk, f, hf, rfl⟩, rfl⟩; exact ⟨x, hx, k, hk, f, hf, rfl⟩

theorem mdeg_aC (x : E) (k : ℕ) (S : Finset V) :
    mdeg (aEnds ends : E ⊕ ALab E V → Finset V) (aC r ends Q x k) S =
      deg (antiE r ends Q x) S := by
  rw [mdeg_eq_deg_image]
  · congr 1
    ext f; simp [aC, aEnds]
  · intro c hc c' hc' h
    simp only [aC, coe_image, Set.mem_image, mem_coe] at hc hc'
    obtain ⟨f, -, rfl⟩ := hc
    obtain ⟨f', -, rfl⟩ := hc'
    simp only [aEnds, Sum.elim_inr] at h
    rw [h]

/-- **The anti-edge step into the reserve `U`.** -/
theorem antiEdgeStep_reserve {q : ℕ} (hrq : r < q) {X : Finset E} (hX : MIsRGraph r ends X)
    {U : Finset V} (hQ : ∀ x ∈ X, Q x ⊆ U ∧ Disjoint (ends x) (Q x) ∧ (Q x).card = q - r) :
    IsResidualMultiRefiner q r (1 + q.choose r * fakeModulus q r + 2) (aEnds ends)
      (X.image Sum.inl) ((aR r ends Q X (fakeModulus q r)).image Sum.inr)
      ((aY r ends Q X (fakeModulus q r)).image Sum.inr)
      (pairFamily X (fakeModulus q r) (fun x => {Sum.inl x}) (aC r ends Q)) ∧
    aY r ends Q X (fakeModulus q r) ⊆ aR r ends Q X (fakeModulus q r) ∧
    IsFlat (r - 1) U (fun y : ALab E V => y.2.2) (aY r ends Q X (fakeModulus q r)) ∧
    (∀ W ∈ pairFamily X (fakeModulus q r) (fun x => {Sum.inl x}) (aC r ends Q),
      (W.filter (· ∈ X.image Sum.inl)).card ≤ 1) := by
  set M := fakeModulus q r with hMdef
  have hM : 1 ≤ M := fakeModulus_pos hrq.le
  have hdvd : ∀ s < r, (q - s).choose (r - s) ∣ M := fun s hs => dvd_fakeModulus hs
  have hcard : ∀ x ∈ X, (ends x ∪ Q x).card = q := by
    intro x hx
    rw [card_union_of_disjoint (hQ x hx).2.1, hX x hx, (hQ x hx).2.2]; omega
  have hanti_r : ∀ x, ∀ f ∈ antiE r ends Q x, f.card = r := fun x f hf =>
    (mem_powersetCard.1 (mem_of_mem_erase hf)).2
  have hpd : PairedData q r (aEnds ends) (X.image Sum.inl) ∅ (X.image Sum.inl) X
      (fun x => ({Sum.inl x} : Finset (E ⊕ ALab E V))) M (aC r ends Q) ∅ 1 (q.choose r) := by
    refine ⟨hM, subset_rfl, disjoint_empty_right _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    · intro x hx
      rw [union_empty, singleton_subset_iff]
      exact mem_image_of_mem _ hx
    · intro x _; simp
    · intro c _
      refine (card_le_card (t := (X.filter fun x => c = Sum.inl x)) ?_).trans ?_
      · intro x hx; simpa using hx
      · rw [card_le_one]
        intro a ha b hb
        have := (mem_filter.1 ha).2.symm.trans (mem_filter.1 hb).2
        exact Sum.inl_injective this
    · intro x hx k _
      refine card_image_le.trans ((card_erase_le).trans ?_)
      rw [cliqueEdges, card_powersetCard, hcard x hx]
    · intro x _ k _ x' _ k' _ hne
      rw [disjoint_left]
      intro c hc hc'
      simp only [aC, mem_image] at hc hc'
      obtain ⟨f, -, rfl⟩ := hc
      obtain ⟨f', -, h⟩ := hc'
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      exact hne (by rw [h.1, h.2.1])
    · intro x _ k _
      rw [disjoint_left]
      intro c hc hc'
      simp only [aC, mem_image] at hc
      obtain ⟨f, -, rfl⟩ := hc
      simp at hc'
    · exact disjoint_empty_left _
    · intro c hc
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hc; exact hX x hx
      · simp only [empty_union, union_empty] at hc
        obtain ⟨x, -, k, -, hc⟩ := mem_allC.1 hc
        simp only [aC, mem_image] at hc
        obtain ⟨f, hf, rfl⟩ := hc
        exact hanti_r x f hf
    · intro x hx S hS
      have hins : ({Sum.inl x} ∪ aC r ends Q x 0).image (aEnds ends) =
          cliqueEdges r (ends x ∪ Q x) := by
        ext f
        simp only [mem_image, mem_union, mem_singleton, aC, antiE]
        constructor
        · rintro ⟨c, rfl | ⟨g, hg, rfl⟩, rfl⟩
          · simp only [aEnds, Sum.elim_inl, cliqueEdges, mem_powersetCard]
            exact ⟨subset_union_left, hX x hx⟩
          · exact mem_of_mem_erase hg
        · intro hf
          by_cases hfx : f = ends x
          · exact ⟨Sum.inl x, Or.inl rfl, hfx.symm⟩
          · exact ⟨Sum.inr (x, 0, f), Or.inr ⟨f, mem_erase.2 ⟨hfx, hf⟩, rfl⟩, rfl⟩
      have hinj : Set.InjOn (aEnds ends) ↑({Sum.inl x} ∪ aC r ends Q x 0) := by
        intro c hc c' hc' h
        simp only [coe_union, coe_singleton, Set.mem_union, Set.mem_singleton_iff, aC,
          coe_image, Set.mem_image, mem_coe, antiE] at hc hc'
        rcases hc with rfl | ⟨f, hf, rfl⟩ <;> rcases hc' with rfl | ⟨f', hf', rfl⟩
        · rfl
        · simp only [aEnds, Sum.elim_inl, Sum.elim_inr] at h
          exact absurd h.symm (ne_of_mem_erase hf')
        · simp only [aEnds, Sum.elim_inl, Sum.elim_inr] at h
          exact absurd h (ne_of_mem_erase hf)
        · simp only [aEnds, Sum.elim_inr] at h; rw [h]
      rw [mdeg_eq_deg_image hinj, hins]
      exact dvd_deg_cliqueEdges (hcard x hx) hS.le
    · intro x _
      refine divisible_copies _ ?_ (fun k _ S => by rw [mdeg_aC, mdeg_aC]) hdvd
      intro k _ k' _ hne
      rw [disjoint_left]
      intro c hc hc'
      simp only [aC, mem_image] at hc hc'
      obtain ⟨f, -, rfl⟩ := hc
      obtain ⟨f', -, h⟩ := hc'
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      exact hne h.2.1.symm
    · rw [empty_union, union_empty]
      refine divisible_biUnion X _ ?_ ?_
      · intro x _ x' _ hne
        rw [disjoint_left]
        intro c hc hc'
        simp only [mem_biUnion, mem_range, aC, mem_image] at hc hc'
        obtain ⟨k, -, f, -, rfl⟩ := hc
        obtain ⟨k', -, f', -, h⟩ := hc'
        simp only [Sum.inr.injEq, Prod.mk.injEq] at h
        exact hne h.1.symm
      · intro x _
        refine divisible_copies _ ?_ (fun k _ S => by rw [mdeg_aC, mdeg_aC]) hdvd
        intro k _ k' _ hne
        rw [disjoint_left]
        intro c hc hc'
        simp only [aC, mem_image] at hc hc'
        obtain ⟨f, -, rfl⟩ := hc
        obtain ⟨f', -, h⟩ := hc'
        simp only [Sum.inr.injEq, Prod.mk.injEq] at h
        exact hne h.2.1.symm
    · intro L hL _
      refine ⟨X.filter fun x => Sum.inl x ∈ L, filter_subset _ _, ?_, ?_⟩
      · intro x _ x' _ hne
        simpa using hne
      · ext c
        simp only [mem_biUnion, mem_filter, mem_singleton, empty_union, mem_inter]
        constructor
        · rintro ⟨x, ⟨hx, hxL⟩, rfl⟩; exact ⟨hxL, mem_image_of_mem _ hx⟩
        · rintro ⟨hcL, hc⟩
          obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
          exact ⟨x, ⟨hx, hcL⟩, rfl⟩
  have h := pairedStep hpd
  rw [empty_union, union_empty, allC_aC, sdiff_self, bot_eq_empty, empty_union, union_empty,
    tailC_aC] at h
  refine ⟨by simpa using h.mono (by omega), ?_, ?_, ?_⟩
  · intro y hy
    simp only [aY, aR, mem_biUnion, mem_image, mem_Ico, mem_range] at hy ⊢
    obtain ⟨x, hx, k, hk, f, hf, rfl⟩ := hy
    exact ⟨x, hx, k, hk.2, f, hf, rfl⟩
  · intro y hy
    simp only [aY, mem_biUnion, mem_image, mem_Ico] at hy
    obtain ⟨x, hx, k, -, f, hf, rfl⟩ := hy
    have hfx : f ≠ ends x := ne_of_mem_erase hf
    have hfs : f ⊆ ends x ∪ Q x := (mem_powersetCard.1 (mem_of_mem_erase hf)).1
    have hfr : f.card = r := hanti_r x f hf
    show (f \ U).card ≤ r - 1
    have hsub : f \ U ⊆ ends x := by
      intro v hv
      obtain ⟨hvf, hvU⟩ := mem_sdiff.1 hv
      rcases mem_union.1 (hfs hvf) with h1 | h1
      · exact h1
      · exact absurd ((hQ x hx).1 h1) hvU
    have hlt : (f \ U).card < r := by
      by_contra hge
      have heq : f \ U = f := eq_of_subset_of_card_le sdiff_subset (by omega)
      have : f = ends x := eq_of_subset_of_card_le (heq ▸ hsub) (by rw [hfr, hX x hx])
      exact hfx this
    omega
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨x, -, rfl⟩ := mem_image.1 hW
      refine (card_le_card (t := {Sum.inl x}) ?_).trans (by simp)
      intro c hc
      obtain ⟨hc, hcX⟩ := mem_filter.1 hc
      rcases mem_union.1 hc with hc | hc
      · exact hc
      · simp only [aC, mem_image] at hc
        obtain ⟨f, -, rfl⟩ := hc
        simp at hcX
    · obtain ⟨x, -, rfl⟩ := mem_image.1 hW
      rw [card_le_one]
      intro c hc
      obtain ⟨hc, hcX⟩ := mem_filter.1 hc
      simp only [pairN, mem_biUnion, aC, mem_image] at hc
      obtain ⟨k, -, f, -, rfl⟩ := hc
      simp at hcX

end Anti

end RefinedAbsorption.FlatDown
