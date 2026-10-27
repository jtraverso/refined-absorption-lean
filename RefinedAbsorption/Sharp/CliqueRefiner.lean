module
public import RefinedAbsorption.Sharp.Better

/-!
# Private cliques: the first refiner of the Edge Sparsification Lemma

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Lemma 3.12 (the refiner `R₁`).

Let `X` be an `r`-multigraph (labelled copies `ends : E → Finset V`) and suppose every copy `x`
comes with a `q`-set `Vx x ⊇ ends x`.  Let `M = fakeModulus q r`, which is divisible by every
`binom(q - s, r - s)`, `s < r`.  The refiner `R₁` consists of `M` copies of `K_q^r(Vx x) - ends x`
for every `x ∈ X` (labels `Sum.inr (x, j, f)`, `j < M`, `f` an `r`-subset of `Vx x` other than
`ends x`).  The pieces are the cliques `{x} ∪ {(x, 0, f)}`, one for each `x`.

* **`cliqueRefiner_residual`**: `R₁` is a `binom(q, r)`-refined residual multi-refiner of `X`
  with residue in `R₁` (the leftover of `L` is `R₁` minus the pieces of the copies in `L`).
* `cliqueRefiner_oneX`, `cliqueRefiner_ends`, `mdeg_cliqueR_le`, `pdeg_cliqueW_le`: each piece
  contains one copy of `X`; the new copies are `r`-subsets of the cliques other than the copies
  themselves; `mdeg R₁ S ≤ M · binom(q, r) · #{x : S ⊆ Vx x}` and the piece degree of `S` is at
  most `#{x : S ⊆ Vx x}`.
-/

@[expose] public section

namespace RefinedAbsorption.Sharp

open Finset RefinedAbsorption.MultiRefiner

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- Labels of the clique refiner. -/
abbrev CLab (V E : Type) := E ⊕ (E × ℕ × Finset V)

/-- Ends of the labels of the clique refiner. -/
def cEnds (ends : E → Finset V) : CLab V E → Finset V := Sum.elim ends fun p => p.2.2

/-- The `j`-th copy of `K_q^r(Vx x) - ends x`. -/
def cBlk (ends : E → Finset V) (r : ℕ) (Vx : E → Finset V) (x : E) (j : ℕ) :
    Finset (CLab V E) :=
  (((Vx x).powersetCard r).erase (ends x)).image fun f => Sum.inr (x, j, f)

/-- The clique refiner: `M` copies of `K_q^r(Vx x) - ends x` for every `x ∈ X`. -/
def cliqueR (ends : E → Finset V) (r M : ℕ) (Vx : E → Finset V) (X : Finset E) :
    Finset (CLab V E) :=
  X.biUnion fun x => (range M).biUnion fun j => cBlk ends r Vx x j

/-- The piece of `x`: the clique on `Vx x` made of `x` and the `0`-th block. -/
def cPiece (ends : E → Finset V) (r : ℕ) (Vx : E → Finset V) (x : E) : Finset (CLab V E) :=
  insert (Sum.inl x) (cBlk ends r Vx x 0)

/-- The refinement family. -/
def cliqueW (ends : E → Finset V) (r : ℕ) (Vx : E → Finset V) (X : Finset E) :
    Finset (Finset (CLab V E)) :=
  X.image (cPiece ends r Vx)

theorem mem_cBlk {ends : E → Finset V} {r : ℕ} {Vx : E → Finset V} {x : E} {j : ℕ}
    {c : CLab V E} :
    c ∈ cBlk ends r Vx x j ↔ ∃ f, f ⊆ Vx x ∧ f.card = r ∧ f ≠ ends x ∧ c = Sum.inr (x, j, f) := by
  unfold cBlk
  simp only [mem_image, mem_erase, mem_powersetCard]
  constructor
  · rintro ⟨f, ⟨hne, hsub, hcard⟩, rfl⟩; exact ⟨f, hsub, hcard, hne, rfl⟩
  · rintro ⟨f, hsub, hcard, hne, rfl⟩; exact ⟨f, ⟨hne, hsub, hcard⟩, rfl⟩

theorem mem_cliqueR {ends : E → Finset V} {r M : ℕ} {Vx : E → Finset V} {X : Finset E}
    {c : CLab V E} :
    c ∈ cliqueR ends r M Vx X ↔
      ∃ x ∈ X, ∃ j < M, ∃ f, f ⊆ Vx x ∧ f.card = r ∧ f ≠ ends x ∧ c = Sum.inr (x, j, f) := by
  unfold cliqueR
  simp only [mem_biUnion, mem_range, mem_cBlk]

theorem mem_cPiece {ends : E → Finset V} {r : ℕ} {Vx : E → Finset V} {x : E} {c : CLab V E} :
    c ∈ cPiece ends r Vx x ↔
      c = Sum.inl x ∨ ∃ f, f ⊆ Vx x ∧ f.card = r ∧ f ≠ ends x ∧ c = Sum.inr (x, 0, f) := by
  unfold cPiece
  rw [mem_insert, mem_cBlk]

/-- The ends of the members of a piece containing `S` are `r`-subsets of `Vx x` (the piece is
the complete `r`-graph on `Vx x`). -/
theorem mdeg_cPiece {ends : E → Finset V} {r : ℕ} {Vx : E → Finset V} {x : E}
    (hsub : ends x ⊆ Vx x) (hcard : (ends x).card = r) (S : Finset V) :
    mdeg (cEnds ends) (cPiece ends r Vx x) S =
      (((Vx x).powersetCard r).filter fun f => S ⊆ f).card := by
  unfold mdeg
  -- the piece is the image of `powersetCard r (Vx x)` under an injective map
  set φ : Finset V → CLab V E := fun f => if f = ends x then Sum.inl x else Sum.inr (x, 0, f)
    with hφ
  have hinj : Set.InjOn φ ((Vx x).powersetCard r : Set (Finset V)) := by
    intro f _ f' _ h
    simp only [hφ] at h
    by_cases h1 : f = ends x <;> by_cases h2 : f' = ends x <;> simp_all
  have himg : cPiece ends r Vx x = ((Vx x).powersetCard r).image φ := by
    ext c
    rw [mem_cPiece, mem_image]
    constructor
    · rintro (rfl | ⟨f, h1, h2, h3, rfl⟩)
      · exact ⟨ends x, mem_powersetCard.2 ⟨hsub, hcard⟩, by simp [hφ]⟩
      · exact ⟨f, mem_powersetCard.2 ⟨h1, h2⟩, by simp [hφ, h3]⟩
    · rintro ⟨f, hf, rfl⟩
      rw [mem_powersetCard] at hf
      by_cases h : f = ends x
      · left; simp [hφ, h]
      · right; exact ⟨f, hf.1, hf.2, h, by simp [hφ, h]⟩
  have hends : ∀ f, cEnds ends (φ f) = f := by
    intro f
    simp only [hφ]
    split_ifs with h
    · simp [cEnds, h]
    · simp [cEnds]
  rw [himg, filter_image, card_image_of_injOn (hinj.mono (fun f hf => by
    simp only [coe_filter, Set.mem_setOf_eq] at hf; exact hf.1))]
  congr 1
  exact filter_congr fun f _ => by rw [hends]

/-- Number of copies of `cBlk` containing `S`. -/
theorem mdeg_cBlk (ends : E → Finset V) (r : ℕ) (Vx : E → Finset V) (x : E) (j : ℕ)
    (S : Finset V) :
    mdeg (cEnds ends) (cBlk ends r Vx x j) S =
      ((((Vx x).powersetCard r).erase (ends x)).filter fun f => S ⊆ f).card := by
  unfold mdeg cBlk
  rw [filter_image, card_image_of_injective _ (fun f f' h => by simpa using h)]
  rfl

theorem disjoint_cBlk {ends : E → Finset V} {r : ℕ} {Vx : E → Finset V} {x x' : E} {j j' : ℕ}
    (h : (x, j) ≠ (x', j')) : Disjoint (cBlk ends r Vx x j) (cBlk ends r Vx x' j') := by
  rw [disjoint_left]
  intro c hc hc'
  obtain ⟨f, -, -, -, rfl⟩ := mem_cBlk.1 hc
  obtain ⟨f', -, -, -, hf'⟩ := mem_cBlk.1 hc'
  simp only [Sum.inr.injEq, Prod.mk.injEq] at hf'
  exact h (by rw [hf'.1, hf'.2.1])

theorem mdeg_cliqueR (ends : E → Finset V) (r M : ℕ) (Vx : E → Finset V) (X : Finset E)
    (S : Finset V) :
    mdeg (cEnds ends) (cliqueR ends r M Vx X) S =
      M * ∑ x ∈ X, ((((Vx x).powersetCard r).erase (ends x)).filter fun f => S ⊆ f).card := by
  unfold cliqueR
  have hd1 : (X : Set E).PairwiseDisjoint fun x => (range M).biUnion fun j => cBlk ends r Vx x j := by
    intro x _ x' _ hxx'
    simp only [Function.onFun]
    rw [disjoint_biUnion_left]
    intro j _
    rw [disjoint_biUnion_right]
    intro j' _
    exact disjoint_cBlk (by simp [hxx'])
  unfold mdeg
  rw [filter_biUnion, card_biUnion (fun x hx x' hx' h => disjoint_filter_filter (hd1 hx hx' h)),
    mul_sum]
  refine sum_congr rfl fun x _ => ?_
  have hd2 : ((range M : Finset ℕ) : Set ℕ).PairwiseDisjoint fun j => cBlk ends r Vx x j :=
    fun j _ j' _ hjj' => disjoint_cBlk (by simp [hjj'])
  rw [filter_biUnion, card_biUnion (fun j hj j' hj' h => disjoint_filter_filter (hd2 hj hj' h))]
  have : ∀ j ∈ range M, ((cBlk ends r Vx x j).filter fun i => S ⊆ cEnds ends i).card =
      ((((Vx x).powersetCard r).erase (ends x)).filter fun f => S ⊆ f).card :=
    fun j _ => mdeg_cBlk ends r Vx x j S
  rw [sum_congr rfl this, sum_const, card_range, smul_eq_mul]

theorem cliqueR_disjoint {ends : E → Finset V} {r M : ℕ} {Vx : E → Finset V} {X : Finset E} :
    Disjoint (X.image Sum.inl) (cliqueR ends r M Vx X) := by
  rw [disjoint_left]
  intro c hc hc'
  obtain ⟨x, -, rfl⟩ := mem_image.1 hc
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := mem_cliqueR.1 hc'
  exact Sum.inl_ne_inr h

/-- The clique piece of `x` is divisible. -/
theorem cPiece_divisible {q r : ℕ} {ends : E → Finset V} {Vx : E → Finset V} {x : E}
    (hsub : ends x ⊆ Vx x) (hcard : (ends x).card = r) (hq : (Vx x).card = q) :
    MIsDivisible q r (cEnds ends) (cPiece ends r Vx x) := by
  intro S hS
  rw [mdeg_cPiece hsub hcard]
  by_cases hSV : S ⊆ Vx x
  · rw [card_powersetCard_filter_superset hSV hS.le, hq]
  · rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun f hf hSf =>
      hSV (hSf.trans (mem_powersetCard.1 hf).1))]
    exact dvd_zero _

/-- **The clique refiner is a residual multi-refiner.** -/
theorem cliqueRefiner_residual {q r : ℕ} (hrq : r ≤ q) {ends : E → Finset V}
    {Vx : E → Finset V} {X : Finset E} (hXr : MIsRGraph r ends X)
    (hsub : ∀ x ∈ X, ends x ⊆ Vx x) (hq : ∀ x ∈ X, (Vx x).card = q) :
    IsResidualMultiRefiner q r (q.choose r) (cEnds ends) (X.image Sum.inl)
      (cliqueR ends r (RefinedAbsorption.MultiRefiner.fakeModulus q r) Vx X)
      (cliqueR ends r (RefinedAbsorption.MultiRefiner.fakeModulus q r) Vx X)
      (cliqueW ends r Vx X) := by
  set M := RefinedAbsorption.MultiRefiner.fakeModulus q r with hM
  have hM0 : 0 < M := RefinedAbsorption.MultiRefiner.fakeModulus_pos hrq
  set R := cliqueR ends r M Vx X with hR
  have hpieceR : ∀ x ∈ X, cPiece ends r Vx x ⊆ X.image Sum.inl ∪ R := by
    intro x hx c hc
    rcases mem_cPiece.1 hc with rfl | ⟨f, h1, h2, h3, rfl⟩
    · exact mem_union_left _ (mem_image_of_mem _ hx)
    · exact mem_union_right _ (mem_cliqueR.2 ⟨x, hx, 0, hM0, f, h1, h2, h3, rfl⟩)
  have hpiece_disj : ∀ x x', x ≠ x' → Disjoint (cPiece ends r Vx x) (cPiece ends r Vx x') := by
    intro x x' hxx'
    rw [disjoint_left]
    intro c hc hc'
    rcases mem_cPiece.1 hc with rfl | ⟨f, -, -, -, rfl⟩ <;>
      rcases mem_cPiece.1 hc' with h | ⟨f', -, -, -, h⟩
    · exact hxx' (Sum.inl_injective h)
    · exact Sum.inl_ne_inr h
    · exact Sum.inr_ne_inl h
    · simp only [Sum.inr.injEq, Prod.mk.injEq] at h; exact hxx' h.1
  have hpiece_inj : Set.InjOn (cPiece ends r Vx) (X : Set E) := by
    intro x _ x' _ h
    by_contra hne
    have := hpiece_disj x x' hne
    rw [h, disjoint_self_iff_empty] at this
    exact absurd this (by unfold cPiece; simp)
  refine ⟨?_, cliqueR_disjoint, ?_, ?_, ?_, ?_, ?_⟩
  · -- `r`-graph
    intro c hc
    rcases mem_union.1 hc with h | h
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 h
      exact hXr x hx
    · obtain ⟨x, -, j, -, f, -, hf, -, rfl⟩ := mem_cliqueR.1 h
      exact hf
  · intro W hW
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hW
    exact cPiece_divisible (hsub x hx) (hXr x hx) (hq x hx)
  · intro W hW
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hW
    exact hpieceR x hx
  · intro W hW
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hW
    have : (cPiece ends r Vx x).card = q.choose r := by
      have h := mdeg_cPiece (hsub x hx) (hXr x hx) (∅ : Finset V)
      unfold mdeg at h
      simp only [empty_subset, filter_true] at h
      rw [h, card_powersetCard, hq x hx]
    rw [this]
  · intro c _
    refine (card_le_one.2 ?_).trans (Nat.choose_pos hrq)
    intro W hW W' hW'
    rw [mem_filter] at hW hW'
    obtain ⟨x, -, rfl⟩ := mem_image.1 hW.1
    obtain ⟨x', -, rfl⟩ := mem_image.1 hW'.1
    by_contra hne
    have hxx' : x ≠ x' := fun h => hne (by rw [h])
    exact disjoint_left.1 (hpiece_disj x x' hxx') hW.2 hW'.2
  · -- decomposition
    intro L hL hLdiv
    set L₀ := X.filter fun x => Sum.inl x ∈ L with hL₀
    have hLL₀ : L = L₀.image Sum.inl := by
      ext c
      constructor
      · intro hc
        obtain ⟨x, hx, rfl⟩ := mem_image.1 (hL hc)
        exact mem_image_of_mem _ (mem_filter.2 ⟨hx, hc⟩)
      · intro hc
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
        exact (mem_filter.1 hx).2
    set 𝒰 := L₀.image (cPiece ends r Vx) with h𝒰
    set P := 𝒰.sup id with hP
    set Res := R \ P with hRes
    have hPsub : P ⊆ R ∪ L := by
      intro c hc
      obtain ⟨W, hW, hcW⟩ := mem_sup.1 hc
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hW
      have hx' := mem_filter.1 hx
      rcases mem_cPiece.1 hcW with rfl | ⟨f, h1, h2, h3, rfl⟩
      · exact mem_union_right _ hx'.2
      · exact mem_union_left _ (mem_cliqueR.2 ⟨x, hx'.1, 0, hM0, f, h1, h2, h3, rfl⟩)
    have hLP : L ⊆ P := by
      intro c hc
      rw [hLL₀] at hc
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
      exact mem_sup.2 ⟨_, mem_image_of_mem _ hx, by unfold cPiece; exact mem_insert_self _ _⟩
    have hunion : P ∪ Res = R ∪ L := by
      ext c
      simp only [hRes, mem_union, mem_sdiff]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact mem_union.1 (hPsub h)
        · exact Or.inl h
      · rintro (h | h)
        · by_cases hcP : c ∈ P
          · exact Or.inl hcP
          · exact Or.inr ⟨h, hcP⟩
        · exact Or.inl (hLP h)
    have hdisjPRes : Disjoint P Res := disjoint_sdiff
    have hpw : (𝒰 : Set (Finset (CLab V E))).PairwiseDisjoint id := by
      intro W hW W' hW' hne
      obtain ⟨x, -, rfl⟩ := mem_image.1 (mem_coe.1 hW)
      obtain ⟨x', -, rfl⟩ := mem_image.1 (mem_coe.1 hW')
      have hxx' : x ≠ x' := fun h => hne (by rw [h])
      exact hpiece_disj x x' hxx'
    refine ⟨𝒰, ?_, Res, sdiff_subset, ?_, hpw, hdisjPRes, hunion⟩
    · exact image_subset_image (filter_subset _ _)
    · -- divisibility of the leftover
      intro S hS
      set b := (q - S.card).choose (r - S.card) with hb
      have hRd : b ∣ mdeg (cEnds ends) R S := by
        rw [hR, mdeg_cliqueR]
        exact Dvd.dvd.mul_right (RefinedAbsorption.MultiRefiner.dvd_fakeModulus hS) _
      have hPd : b ∣ mdeg (cEnds ends) P S := by
        have hPeq : mdeg (cEnds ends) P S = ∑ W ∈ 𝒰, mdeg (cEnds ends) W S := by
          rw [hP, sup_eq_biUnion]
          unfold mdeg
          rw [filter_biUnion, card_biUnion (fun W hW W' hW' h =>
            disjoint_filter_filter (hpw (mem_coe.2 hW) (mem_coe.2 hW') h))]
          rfl
        rw [hPeq]
        refine dvd_sum fun W hW => ?_
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hW
        have hx' := (mem_filter.1 hx).1
        exact cPiece_divisible (hsub x hx') (hXr x hx') (hq x hx') S hS
      have hLd : b ∣ mdeg (cEnds ends) L S := hLdiv S hS
      have hRL : Disjoint R L := by
        refine disjoint_of_subset_right hL ?_
        exact cliqueR_disjoint.symm
      have heq : mdeg (cEnds ends) P S + mdeg (cEnds ends) Res S =
          mdeg (cEnds ends) R S + mdeg (cEnds ends) L S := by
        rw [← mdeg_union_of_disjoint _ hdisjPRes, ← mdeg_union_of_disjoint _ hRL, hunion]
      have : b ∣ mdeg (cEnds ends) P S + mdeg (cEnds ends) Res S := by
        rw [heq]; exact dvd_add hRd hLd
      exact (Nat.dvd_add_right hPd).1 this

theorem cliqueRefiner_oneX {r : ℕ} {ends : E → Finset V} {Vx : E → Finset V} {X : Finset E} :
    ∀ W ∈ cliqueW ends r Vx X, (W.filter (· ∈ X.image Sum.inl)).card ≤ 1 := by
  intro W hW
  obtain ⟨x, -, rfl⟩ := mem_image.1 hW
  refine card_le_one.2 fun c hc c' hc' => ?_
  rw [mem_filter] at hc hc'
  obtain ⟨y, -, rfl⟩ := mem_image.1 hc.2
  obtain ⟨y', -, rfl⟩ := mem_image.1 hc'.2
  rcases mem_cPiece.1 hc.1 with h | ⟨f, -, -, -, h⟩
  · rcases mem_cPiece.1 hc'.1 with h' | ⟨f', -, -, -, h'⟩
    · rw [h, h']
    · exact absurd h' Sum.inl_ne_inr
  · exact absurd h Sum.inl_ne_inr

/-- The new copies are `r`-subsets of a clique, other than the copy itself. -/
theorem cliqueRefiner_ends {r M : ℕ} {ends : E → Finset V} {Vx : E → Finset V} {X : Finset E}
    {c : CLab V E} (hc : c ∈ cliqueR ends r M Vx X) :
    ∃ x ∈ X, cEnds ends c ⊆ Vx x ∧ (cEnds ends c).card = r ∧ cEnds ends c ≠ ends x := by
  obtain ⟨x, hx, j, -, f, h1, h2, h3, rfl⟩ := mem_cliqueR.1 hc
  exact ⟨x, hx, h1, h2, h3⟩

theorem mdeg_cliqueR_le {r M : ℕ} {ends : E → Finset V} {Vx : E → Finset V} {X : Finset E}
    {q : ℕ} (hq : ∀ x ∈ X, (Vx x).card = q) (S : Finset V) :
    mdeg (cEnds ends) (cliqueR ends r M Vx X) S ≤
      M * (q.choose r * (X.filter fun x => S ⊆ Vx x).card) := by
  rw [mdeg_cliqueR]
  refine Nat.mul_le_mul_left _ ?_
  rw [card_eq_sum_ones, mul_sum, sum_filter]
  refine sum_le_sum fun x hx => ?_
  split_ifs with hS
  · rw [mul_one]
    refine (card_filter_le _ _).trans ((card_erase_le).trans ?_)
    rw [card_powersetCard, hq x hx]
  · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
    intro f hf hSf
    exact hS (hSf.trans (mem_powersetCard.1 (mem_of_mem_erase hf)).1)

theorem pdeg_cliqueW_le {r : ℕ} {ends : E → Finset V} {Vx : E → Finset V} {X : Finset E}
    (hsub : ∀ x ∈ X, ends x ⊆ Vx x) (S : Finset V) :
    RefinedAbsorption.MultiRefiner.pdeg (cEnds ends) (cliqueW ends r Vx X) S ≤
      (X.filter fun x => S ⊆ Vx x).card := by
  unfold RefinedAbsorption.MultiRefiner.pdeg cliqueW
  rw [filter_image]
  refine card_image_le.trans (card_le_card fun x hx => ?_)
  rw [mem_filter] at hx ⊢
  refine ⟨hx.1, hx.2.trans ?_⟩
  intro v hv
  obtain ⟨c, hc, hvc⟩ := mem_biUnion.1 hv
  rcases mem_cPiece.1 hc with rfl | ⟨f, h1, -, -, rfl⟩
  · exact hsub x hx.1 hvc
  · exact h1 hvc

end RefinedAbsorption.Sharp
