module
public import RequestProject.FlatOmni.LocalRefiner
public import RequestProject.Placement.FakeGadget
public import RequestProject.Placement.ReserveLemma52

/-!
# Replacing the new copies of a local refiner by fake edges in the reserve

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (fake edges, Definition 3.4 of the
survey arXiv:2510.19978, and the Partial Clique Embedding Lemma 5.2 inside a reserve).
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

Given a complete multi-refiner `(R, 𝒲)` of a graph multigraph `X` (copies of `X` inside `Y`, new
copies inside `Y ∪ P`, every piece containing at most one copy of `X`), every new copy `c ∈ R` is
replaced by a fake edge on `ends c` whose auxiliary vertices are placed in the reserve `P`
(`reserveCliqueEmbedding`), with pairwise disjoint new edges.  A placed fake edge behaves like
the edge `ends c` for `K_q^2`-divisibility (`deg_placedFake_cast`), so replacing, in every piece,
the new copies by their fake edges gives again a complete multi-refiner (`fakeStage`).  Its new
edges form a *simple* graph `F` all of whose edges meet `P`, and the copies of every piece have
pairwise distinct vertex sets.
-/

@[expose] public section

namespace RefinedAbsorption.FlatOmni

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.RefineDown
  RefinedAbsorption.FlatDown

section Pieces

variable {n : ℕ} {E : Type} [DecidableEq E]

/-- The piece `W` with its new copies replaced by their fake edges `NE c`. -/
def fakePiece (X R : Finset E) (NE : E → Finset (Finset (Fin n))) (W : Finset E) :
    Finset (E ⊕ Finset (Fin n)) :=
  (W.filter (· ∈ X)).image Sum.inl ∪ (W.filter (· ∈ R)).biUnion fun c => (NE c).image Sum.inr

theorem inl_mem_fakePiece {X R : Finset E} {NE : E → Finset (Finset (Fin n))} {W : Finset E}
    {x : E} : Sum.inl x ∈ fakePiece X R NE W ↔ x ∈ W ∧ x ∈ X := by
  simp [fakePiece]

theorem inr_mem_fakePiece {X R : Finset E} {NE : E → Finset (Finset (Fin n))} {W : Finset E}
    {f : Finset (Fin n)} : Sum.inr f ∈ fakePiece X R NE W ↔ ∃ c ∈ W, c ∈ R ∧ f ∈ NE c := by
  simp [fakePiece, and_assoc]

/-- Degrees in a fake piece: the copies of `X` plus the degrees of the fake edges. -/
theorem mdeg_fakePiece {X R : Finset E} {NE : E → Finset (Finset (Fin n))} {W : Finset E}
    (hNE : ∀ c ∈ R, ∀ c' ∈ R, c ≠ c' → Disjoint (NE c) (NE c')) (ends : E → Finset (Fin n))
    (S : Finset (Fin n)) :
    mdeg (Sum.elim ends id) (fakePiece X R NE W) S =
      mdeg ends (W.filter (· ∈ X)) S + ∑ c ∈ W.filter (· ∈ R), deg (NE c) S := by
  unfold fakePiece
  rw [mdeg_union_of_disjoint]
  · congr 1
    · exact mdeg_image_eq (A := W.filter (· ∈ X)) (fun c _ => rfl) Sum.inl_injective.injOn
        subset_rfl S
    · unfold mdeg deg
      rw [filter_biUnion, card_biUnion]
      · refine sum_congr rfl fun c _ => ?_
        rw [filter_image, card_image_of_injective _ Sum.inr_injective]
        rfl
      · intro c hc c' hc' hcc'
        simp only [Function.onFun]
        refine disjoint_filter_filter ?_
        rw [disjoint_image Sum.inr_injective]
        exact hNE c (mem_filter.1 hc).2 c' (mem_filter.1 hc').2 hcc'
  · rw [disjoint_left]
    intro y hy hy'
    obtain ⟨x, -, rfl⟩ := mem_image.1 hy
    obtain ⟨c, -, hc⟩ := mem_biUnion.1 hy'
    obtain ⟨f, -, hf⟩ := mem_image.1 hc
    exact Sum.inr_ne_inl hf

/-- The copies of a piece of a refiner split into copies of `X` and new copies. -/
theorem mdeg_split {V : Type*} [DecidableEq V] {ends : E → Finset V} {X R W : Finset E}
    (hXR : Disjoint X R) (hW : W ⊆ X ∪ R) (S : Finset V) :
    mdeg ends W S = mdeg ends (W.filter (· ∈ X)) S + mdeg ends (W.filter (· ∈ R)) S := by
  rw [← mdeg_union_of_disjoint ends (disjoint_filter_filter' _ _ ?_)]
  · congr 1
    ext c
    simp only [mem_union, mem_filter]
    constructor
    · intro hc
      rcases mem_union.1 (hW hc) with h | h
      · exact Or.inl ⟨hc, h⟩
      · exact Or.inr ⟨hc, h⟩
    · rintro (⟨hc, -⟩ | ⟨hc, -⟩) <;> exact hc
  · intro A hA hA' c hc
    exact disjoint_left.1 hXR (hA c hc) (hA' c hc)

/-- **Replacing new copies by fake edges keeps a refiner.**  If every new copy `c ∈ R` is replaced
by a graph `NE c` (pairwise disjoint for distinct copies, of at most `B₀` edges, and behaving like
the edge `ends c` modulo divisibility), the fake pieces form a complete multi-refiner of `X` with
new edges `⋃_c NE c`. -/
theorem fakePiece_refiner {q C B₀ : ℕ} {ends : E → Finset (Fin n)} {X R : Finset E}
    {𝒲 : Finset (Finset E)} {NE : E → Finset (Finset (Fin n))}
    (h : IsMultiRefiner q 2 C ends X R 𝒲)
    (hNE : ∀ c ∈ R, ∀ c' ∈ R, c ≠ c' → Disjoint (NE c) (NE c'))
    (hNEr : ∀ c ∈ R, ∀ f ∈ NE c, f.card = 2) (hNEc : ∀ c ∈ R, (NE c).card ≤ B₀)
    (hNEdiv : ∀ c ∈ R, ∀ S : Finset (Fin n), S.card < 2 →
      ((deg (NE c) S : ℕ) : ZMod ((q - S.card).choose (2 - S.card))) =
        if S ⊆ ends c then 1 else 0) :
    IsMultiRefiner q 2 (C * (1 + B₀)) (Sum.elim ends id) (X.image Sum.inl)
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
    have hdiv₀ : MIsDivisible q 2 ends L₀ := by
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

/-- Root density for graph gadgets whose roots lie in a set `U` with `|U| ≤ (K + 1) |P|`. -/
theorem rootDensity_two {ι : Type*} [DecidableEq ι] (I : Finset ι) (Rt : ι → Finset (Fin n))
    (U P : Finset (Fin n)) (K B : ℕ) (hRU : ∀ i ∈ I, Rt i ⊆ U) (hR1 : ∀ i ∈ I, 1 ≤ (Rt i).card)
    (hD : ∀ v, (I.filter fun i => v ∈ Rt i).card ≤ B) (hU : U.card ≤ (K + 1) * P.card) :
    ∀ J : Finset (Fin n), J.card ≤ 2 - 1 →
      (I.filter fun i => J ⊆ Rt i).card ≤ ((K + 1) * B) * P.card ^ (2 - 1 - J.card) := by
  intro J hJ
  have h := rootIncidence_of_subset (r := 2) I Rt U B hRU (fun i hi => hR1 i hi)
    (fun S hS => by
      obtain ⟨v, rfl⟩ := card_eq_one.1 hS
      simpa only [singleton_subset_iff] using hD v) J hJ
  refine h.trans ?_
  rcases Nat.lt_or_ge J.card 1 with h0 | h1
  · have : 2 - 1 - J.card = 1 := by omega
    rw [this, pow_one, pow_one]
    calc B * U.card ≤ B * ((K + 1) * P.card) := Nat.mul_le_mul_left _ hU
      _ = (K + 1) * B * P.card := by ring
  · have : 2 - 1 - J.card = 0 := by omega
    rw [this, pow_zero, pow_zero, mul_one, mul_one]
    exact Nat.le_mul_of_pos_left _ (by omega)

end Pieces

/-- **Fake edges for the new copies of a local refiner** (see the module docstring). -/
theorem fakeStage {q : ℕ} (hq : 2 < q) (C K : ℕ) :
    ∃ Cf C₂ : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (X R : Finset E) (𝒲 : Finset (Finset E)) (Y P : Finset (Fin n)) (B : ℕ),
      IsMultiRefiner q 2 C ends X R 𝒲 → (∀ c ∈ X, ends c ⊆ Y) → (∀ c ∈ R, ends c ⊆ Y ∪ P) →
      Disjoint Y P → (∀ W ∈ 𝒲, (W.filter (· ∈ X)).card ≤ 1) →
      (∀ v, mdeg ends R {v} ≤ B) → (∀ v, pdeg ends 𝒲 {v} ≤ B) →
      Y.card ≤ K * P.card → Cf * B ≤ P.card → 0 < P.card →
      ∃ (F : Finset (Finset (Fin n))) (𝒱 : Finset (Finset (E ⊕ Finset (Fin n)))),
        IsMultiRefiner q 2 C₂ (Sum.elim ends id) (X.image Sum.inl) (F.image Sum.inr) 𝒱 ∧
        (∀ f ∈ F, f ⊆ Y ∪ P ∧ (f ∩ P).Nonempty) ∧
        (∀ v, deg F {v} ≤ C₂ * B) ∧ (∀ v, pdeg (Sum.elim ends id) 𝒱 {v} ≤ C₂ * B) ∧
        (∀ W ∈ 𝒱, Set.InjOn (Sum.elim ends id) ↑W) := by
  classical
  obtain ⟨Ce, hCe, hemb⟩ := reserveCliqueEmbedding 2 (fakeAux q 2) 2
  set B₀ := fakeCount q 2 * q.choose 2 with hB₀
  refine ⟨Ce * (K + 1), C * (1 + B₀) + C * (Ce * (K + 1)) + Ce * (K + 1) + 1, ?_⟩
  intro n E _ ends X R 𝒲 Y P B h hXY hRYP hYP hone hdegR hpd hYK hCB hP
  set D := (K + 1) * B with hD
  have hRr : ∀ c ∈ R, (ends c).card = 2 := fun c hc => h.rgraph c (mem_union_right _ hc)
  have hYPc : (Y ∪ P).card ≤ (K + 1) * P.card :=
    (card_union_le Y P).trans (by rw [add_mul, one_mul]; omega)
  have hroot := rootDensity_two R ends (Y ∪ P) P K B hRYP (fun c hc => by rw [hRr c hc]; omega)
    (fun v => by
      have := hdegR v
      unfold mdeg at this
      simpa only [singleton_subset_iff] using this) hYPc
  obtain ⟨Φ, hvalid, hrange, hdisj, -, hdegF, hcov⟩ := hemb n R (fun c => ends c)
    (fun c => fakeTemplate q 2 (ends c)) ∅ P D (fun c hc => fakeTemplate_wf (hRr c hc))
    (fun S _ => by simp [deg]) (by rw [hD, ← mul_assoc]; exact hCB) hroot hP
  set NE : E → Finset (Finset (Fin n)) := fun c => newEdges (fakeTemplate q 2 (ends c)) (Φ c)
    with hNEdef
  have hNE : ∀ c ∈ R, ∀ c' ∈ R, c ≠ c' → Disjoint (NE c) (NE c') :=
    fun c hc c' hc' hcc' => hdisj c hc c' hc' hcc'
  have hNEr : ∀ c ∈ R, ∀ f ∈ NE c, f.card = 2 := fun c hc f hf =>
    card_of_mem_newEdges (fakeTemplate_wf (hRr c hc)) (hvalid c hc) hf
  have hNEc : ∀ c ∈ R, (NE c).card ≤ B₀ := fun c hc => by
    rw [hNEdef]
    simp only
    rw [card_newEdges (fakeTemplate_wf (hRr c hc)) (hvalid c hc)]
    exact card_fakeTemplate_le (by omega) (hRr c hc)
  have hNEdiv : ∀ c ∈ R, ∀ S : Finset (Fin n), S.card < 2 →
      ((deg (NE c) S : ℕ) : ZMod ((q - S.card).choose (2 - S.card))) =
        if S ⊆ ends c then 1 else 0 := fun c hc S hS =>
    deg_placedFake_cast (by omega) (hRr c hc) (hvalid c hc) S hS
  have href := fakePiece_refiner h hNE hNEr hNEc hNEdiv
  -- the new edges lie in `Y ∪ P` and meet `P`
  have hsubF : ∀ c ∈ R, ∀ f ∈ NE c, f ⊆ ends c ∪ auxImage (Φ c) := by
    intro c hc f hf
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hf
    exact placeEdge_subset (fakeTemplate_wf (hRr c hc)) (Φ c) ht
  have haux : ∀ c ∈ R, auxImage (Φ c) ⊆ P := by
    intro c hc v hv
    obtain ⟨p, -, rfl⟩ := mem_image.1 hv
    exact hrange c hc p
  have hflat : ∀ f ∈ R.biUnion NE, f ⊆ Y ∪ P ∧ (f ∩ P).Nonempty := by
    intro f hf
    obtain ⟨c, hc, hfc⟩ := mem_biUnion.1 hf
    refine ⟨(hsubF c hc f hfc).trans (union_subset (hRYP c hc)
      ((haux c hc).trans subset_union_right)), ?_⟩
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hfc
    obtain ⟨p, hp⟩ := (fakeTemplate_wf (hRr c hc)).edge_aux t ht
    exact ⟨Φ c p, mem_inter.2 ⟨mem_image.2 ⟨Sum.inr p, hp, rfl⟩, hrange c hc p⟩⟩
  have hC₂ : C * (1 + B₀) ≤ C * (1 + B₀) + C * (Ce * (K + 1)) + Ce * (K + 1) + 1 := by omega
  refine ⟨R.biUnion NE, 𝒲.image (fakePiece X R NE), href.mono hC₂, hflat, fun v => ?_,
    fun v => ?_, ?_⟩
  · refine (hdegF {v} (by simp)).trans ?_
    calc Ce * D = Ce * (K + 1) * B := by rw [hD]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · -- piece degrees
    set A₁ := 𝒲.filter fun W => {v} ⊆ W.biUnion ends with hA₁
    set Rv := R.filter fun c => {v} ⊆ ends c ∪ auxImage (Φ c) with hRv
    have hsub : (𝒲.image (fakePiece X R NE)).filter
        (fun W' => {v} ⊆ W'.biUnion (Sum.elim ends id)) ⊆
        (A₁ ∪ Rv.biUnion fun c => 𝒲.filter fun W => c ∈ W).image (fakePiece X R NE) := by
      intro W' hW'
      obtain ⟨hW', hvW'⟩ := mem_filter.1 hW'
      obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
      refine mem_image.2 ⟨W, ?_, rfl⟩
      obtain ⟨y, hy, hvy⟩ := mem_biUnion.1 (singleton_subset_iff.1 hvW')
      rcases y with x | f
      · obtain ⟨hxW, -⟩ := inl_mem_fakePiece.1 hy
        exact mem_union_left _ (mem_filter.2 ⟨hW, singleton_subset_iff.2
          (mem_biUnion.2 ⟨x, hxW, hvy⟩)⟩)
      · obtain ⟨c, hcW, hcR, hfc⟩ := inr_mem_fakePiece.1 hy
        refine mem_union_right _ (mem_biUnion.2 ⟨c, mem_filter.2 ⟨hcR, ?_⟩,
          mem_filter.2 ⟨hW, hcW⟩⟩)
        exact singleton_subset_iff.2 (hsubF c hcR f hfc hvy)
    have hRvc : Rv.card ≤ Ce * D := hcov {v} (by simp)
    have h1 : A₁.card ≤ B := hpd v
    have h2 : (Rv.biUnion fun c => 𝒲.filter fun W => c ∈ W).card ≤ Rv.card * C := by
      refine card_biUnion_le.trans ?_
      refine (sum_le_sum fun c hc => h.mult_le c
        (mem_union_right _ (mem_filter.1 hc).1)).trans ?_
      rw [sum_const, smul_eq_mul]
    unfold pdeg
    refine (card_le_card hsub).trans (card_image_le.trans ((card_union_le _ _).trans ?_))
    have h3 : Rv.card * C ≤ C * (Ce * (K + 1)) * B := by
      calc Rv.card * C ≤ Ce * D * C := Nat.mul_le_mul_right _ hRvc
        _ = C * (Ce * (K + 1)) * B := by rw [hD]; ring
    have h4 : B + C * (Ce * (K + 1)) * B ≤
        (C * (1 + B₀) + C * (Ce * (K + 1)) + Ce * (K + 1) + 1) * B := by
      have e : (C * (1 + B₀) + C * (Ce * (K + 1)) + Ce * (K + 1) + 1) * B =
          B + C * (Ce * (K + 1)) * B + (C * (1 + B₀) * B + Ce * (K + 1) * B) := by ring
      rw [e]; exact Nat.le_add_right _ _
    omega
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    intro y₁ hy₁ y₂ hy₂ heq
    rcases y₁ with x₁ | f₁ <;> rcases y₂ with x₂ | f₂
    · obtain ⟨hx₁W, hx₁X⟩ := inl_mem_fakePiece.1 hy₁
      obtain ⟨hx₂W, hx₂X⟩ := inl_mem_fakePiece.1 hy₂
      rw [card_le_one.1 (hone W hW) x₁ (mem_filter.2 ⟨hx₁W, hx₁X⟩) x₂
        (mem_filter.2 ⟨hx₂W, hx₂X⟩)]
    · exfalso
      obtain ⟨-, hx₁X⟩ := inl_mem_fakePiece.1 hy₁
      obtain ⟨c, -, hcR, hfc⟩ := inr_mem_fakePiece.1 hy₂
      obtain ⟨z, hz⟩ := (hflat f₂ (mem_biUnion.2 ⟨c, hcR, hfc⟩)).2
      have hzf := (mem_inter.1 hz).1
      change ends x₁ = f₂ at heq
      rw [← heq] at hzf
      exact disjoint_left.1 hYP (hXY x₁ hx₁X hzf) (mem_inter.1 hz).2
    · exfalso
      obtain ⟨-, hx₂X⟩ := inl_mem_fakePiece.1 hy₂
      obtain ⟨c, -, hcR, hfc⟩ := inr_mem_fakePiece.1 hy₁
      obtain ⟨z, hz⟩ := (hflat f₁ (mem_biUnion.2 ⟨c, hcR, hfc⟩)).2
      have hzf := (mem_inter.1 hz).1
      change f₁ = ends x₂ at heq
      rw [heq] at hzf
      exact disjoint_left.1 hYP (hXY x₂ hx₂X hzf) (mem_inter.1 hz).2
    · change f₁ = f₂ at heq
      rw [heq]

end RefinedAbsorption.FlatOmni
