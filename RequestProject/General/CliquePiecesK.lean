module
public import RequestProject.FlatOmni.CliquePieces

/-!
# Clique pieces from a refiner with attached absorbers, uniformity `k`

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Theorem 3.7 from Theorem 3.8 and
attached absorbers, Remark 3.9: the pieces of the omni-absorber are cliques `K_q^k`).
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

`cliquePieces_refinerK` is `cliquePieces_refiner` (`FlatOmni/CliquePieces.lean`) in uniformity
`k`: the cliques of the on/off decompositions of absorbers attached to the pieces of a complete
multi-refiner are the pieces of a complete multi-refiner, and every `k`-subset of the span of a
piece carries a copy of the piece.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.FlatDown
  RefinedAbsorption.FlatOmni

variable {n : ℕ} {E : Type} [DecidableEq E]

/-- The hypotheses on the attached absorbers. -/
structure AbsDataK (q k : ℕ) (ends : E → Finset (Fin n)) (X : Finset E) (F : Finset (Finset (Fin n)))
    (𝒱 : Finset (Finset (E ⊕ Finset (Fin n))))
    (AW Qon Qoff : Finset (E ⊕ Finset (Fin n)) → Finset (Finset (Fin n))) : Prop where
  on : ∀ W ∈ 𝒱, IsDecomposition q k (AW W ∪ W.image (Sum.elim ends id)) (Qon W)
  off : ∀ W ∈ 𝒱, IsDecomposition q k (AW W) (Qoff W)
  disj : ∀ W ∈ 𝒱, ∀ W' ∈ 𝒱, W ≠ W' → Disjoint (AW W) (AW W')
  host : ∀ W ∈ 𝒱, Disjoint (AW W) (X.image ends ∪ F)
  inj : ∀ W ∈ 𝒱, Set.InjOn (Sum.elim ends id) ↑W

section Facts

variable {q k C : ℕ} {ends : E → Finset (Fin n)} {X : Finset E} {F : Finset (Finset (Fin n))}
  {𝒱 : Finset (Finset (E ⊕ Finset (Fin n)))}
  {AW Qon Qoff : Finset (E ⊕ Finset (Fin n)) → Finset (Finset (Fin n))}

/-- A label of the absorber of `W` is not a label of any piece. -/
theorem inr_not_mem_pieceK (hA : AbsDataK q k ends X F 𝒱 AW Qon Qoff)
    {W W' : Finset (E ⊕ Finset (Fin n))} (hW : W ∈ 𝒱)
    (hW' : W' ⊆ X.image Sum.inl ∪ F.image Sum.inr) {f : Finset (Fin n)} (hf : f ∈ AW W) :
    Sum.inr f ∉ W' := by
  intro hfW'
  have := image_subset_host (ends := ends) hW' (mem_image_of_mem _ hfW')
  exact disjoint_left.1 (hA.host W hW) hf this

theorem fullP_injOnK (hA : AbsDataK q k ends X F 𝒱 AW Qon Qoff) {W : Finset (E ⊕ Finset (Fin n))}
    (hW : W ∈ 𝒱) (hsub : W ⊆ X.image Sum.inl ∪ F.image Sum.inr) :
    Set.InjOn (Sum.elim ends id) ↑(fullP AW W) := by
  have hcross : ∀ y ∈ W, ∀ f ∈ AW W, Sum.elim ends id y ≠ f := by
    intro y hy f hf h
    have := image_subset_host (ends := ends) hsub (mem_image_of_mem _ hy)
    rw [h] at this
    exact disjoint_left.1 (hA.host W hW) hf this
  intro y₁ hy₁ y₂ hy₂ heq
  rcases mem_union.1 (mem_coe.1 hy₁) with h1 | h1 <;> rcases mem_union.1 (mem_coe.1 hy₂) with h2 | h2
  · exact hA.inj W hW h1 h2 heq
  · obtain ⟨f, hf, rfl⟩ := mem_image.1 h2
    exact absurd heq (hcross y₁ h1 f hf)
  · obtain ⟨f, hf, rfl⟩ := mem_image.1 h1
    exact absurd heq.symm (hcross y₂ h2 f hf)
  · obtain ⟨f, -, rfl⟩ := mem_image.1 h1
    obtain ⟨f', -, rfl⟩ := mem_image.1 h2
    change f = f' at heq
    rw [heq]

/-- The labelled copies of an on-clique are exactly the edges of the clique. -/
theorem image_pOnK (hA : AbsDataK q k ends X F 𝒱 AW Qon Qoff) {W : Finset (E ⊕ Finset (Fin n))}
    (hW : W ∈ 𝒱) {Q : Finset (Fin n)} (hQ : Q ∈ Qon W) :
    (pOn ends AW ⟨W, Q⟩).image (Sum.elim ends id) = cliqueEdges k Q := by
  have hsub := (hA.on W hW).cliqueEdges_subset hQ
  ext e
  constructor
  · intro he
    obtain ⟨y, hy, rfl⟩ := mem_image.1 he
    obtain ⟨hyW, hyQ⟩ := mem_pOn.1 hy
    have hmem : Sum.elim ends id y ∈ AW W ∪ W.image (Sum.elim ends id) := by
      rw [← image_fullP]; exact mem_image_of_mem _ hyW
    rw [cliqueEdges, mem_powersetCard]
    exact ⟨hyQ, (hA.on W hW).rgraph _ hmem⟩
  · intro he
    have hmem := hsub he
    rw [← image_fullP] at hmem
    obtain ⟨y, hy, hye⟩ := mem_image.1 hmem
    refine mem_image.2 ⟨y, mem_pOn.2 ⟨hy, ?_⟩, hye⟩
    rw [hye]; exact (mem_powersetCard.1 he).1

theorem image_pOffK (hA : AbsDataK q k ends X F 𝒱 AW Qon Qoff) {W : Finset (E ⊕ Finset (Fin n))}
    (hW : W ∈ 𝒱) {Q : Finset (Fin n)} (hQ : Q ∈ Qoff W) :
    (pOff ends AW ⟨W, Q⟩).image (Sum.elim ends id) = cliqueEdges k Q := by
  have hsub := (hA.off W hW).cliqueEdges_subset hQ
  ext e
  constructor
  · intro he
    obtain ⟨y, hy, rfl⟩ := mem_image.1 he
    obtain ⟨hyW, hyQ⟩ := mem_pOff.1 hy
    obtain ⟨f, hf, rfl⟩ := mem_image.1 hyW
    rw [cliqueEdges, mem_powersetCard]
    exact ⟨hyQ, (hA.off W hW).rgraph f hf⟩
  · intro he
    have hmem := hsub he
    refine mem_image.2 ⟨Sum.inr e, mem_pOff.2 ⟨mem_image_of_mem _ hmem, ?_⟩, rfl⟩
    exact (mem_powersetCard.1 he).1

/-- Every copy of a piece with its absorber lies in a clique of the on-decomposition. -/
theorem exists_on_coverK (hA : AbsDataK q k ends X F 𝒱 AW Qon Qoff) {W : Finset (E ⊕ Finset (Fin n))}
    (hW : W ∈ 𝒱) {y : E ⊕ Finset (Fin n)} (hy : y ∈ fullP AW W) :
    ∃ Q ∈ Qon W, Sum.elim ends id y ⊆ Q := by
  have hmem : Sum.elim ends id y ∈ AW W ∪ W.image (Sum.elim ends id) := by
    rw [← image_fullP]; exact mem_image_of_mem _ hy
  have h1 := (hA.on W hW).mult_eq _ ((hA.on W hW).rgraph _ hmem)
  rw [if_pos hmem, cliqueMult] at h1
  obtain ⟨Q, hQ⟩ := card_pos.1 (show 0 < _ by rw [h1]; exact one_pos)
  exact ⟨Q, (mem_filter.1 hQ).1, (mem_filter.1 hQ).2⟩

omit [DecidableEq E] in
theorem exists_off_coverK (hA : AbsDataK q k ends X F 𝒱 AW Qon Qoff) {W : Finset (E ⊕ Finset (Fin n))}
    (hW : W ∈ 𝒱) {f : Finset (Fin n)} (hf : f ∈ AW W) : ∃ Q ∈ Qoff W, f ⊆ Q := by
  have h1 := (hA.off W hW).mult_eq _ ((hA.off W hW).rgraph _ hf)
  rw [if_pos hf, cliqueMult] at h1
  obtain ⟨Q, hQ⟩ := card_pos.1 (show 0 < _ by rw [h1]; exact one_pos)
  exact ⟨Q, (mem_filter.1 hQ).1, (mem_filter.1 hQ).2⟩

omit [DecidableEq E] in
/-- Two distinct cliques of a decomposition share no labelled copy. -/
theorem disjoint_sameK {q : ℕ} {G 𝒬 : Finset (Finset (Fin n))} (h : IsDecomposition q k G 𝒬)
    {Q₁ Q₂ : Finset (Fin n)} (hQ₁ : Q₁ ∈ 𝒬) (hQ₂ : Q₂ ∈ 𝒬) (hne : Q₁ ≠ Q₂)
    {A B : Finset (E ⊕ Finset (Fin n))} (hA : ∀ y ∈ A, Sum.elim ends id y ⊆ Q₁)
    (hB : ∀ y ∈ B, Sum.elim ends id y ⊆ Q₂) (h2 : ∀ y ∈ A, (Sum.elim ends id y).card = k) :
    Disjoint A B := by
  rw [disjoint_left]
  intro y hyA hyB
  have hd := h.disjoint_cliqueEdges hQ₁ hQ₂ hne
  exact disjoint_left.1 hd (mem_powersetCard.2 ⟨hA y hyA, h2 y hyA⟩)
    (mem_powersetCard.2 ⟨hB y hyB, h2 y hyA⟩)

/-- **Clique pieces from a refiner with attached absorbers** (see the module docstring). -/
theorem cliquePieces_refinerK
    (h : IsMultiRefiner q k C (Sum.elim ends id) (X.image Sum.inl) (F.image Sum.inr) 𝒱)
    (hA : AbsDataK q k ends X F 𝒱 AW Qon Qoff) :
    IsMultiRefiner q k (2 * (C + 1) + q.choose k) (Sum.elim ends id) (X.image Sum.inl)
        ((F ∪ 𝒱.biUnion AW).image Sum.inr) (cliqueFam ends 𝒱 AW Qon Qoff) ∧
      ∀ P ∈ cliqueFam ends 𝒱 AW Qon Qoff, ∀ S ⊆ P.biUnion (Sum.elim ends id), S.card = k →
        ∃ c ∈ P, Sum.elim ends id c = S := by
  set e₂ : E ⊕ Finset (Fin n) → Finset (Fin n) := Sum.elim ends id with he₂
  set X' := X.image (Sum.inl : E → E ⊕ Finset (Fin n)) with hX'
  set R' := (F ∪ 𝒱.biUnion AW).image (Sum.inr : Finset (Fin n) → E ⊕ Finset (Fin n)) with hR'
  have hsubV : ∀ W ∈ 𝒱, W ⊆ X' ∪ F.image Sum.inr := fun W hW => h.subset W hW
  have hfullR : ∀ W ∈ 𝒱, fullP AW W ⊆ X' ∪ R' := by
    intro W hW y hy
    rcases mem_union.1 hy with hy | hy
    · rcases mem_union.1 (hsubV W hW hy) with h1 | h1
      · exact mem_union_left _ h1
      · obtain ⟨f, hf, rfl⟩ := mem_image.1 h1
        exact mem_union_right _ (mem_image_of_mem _ (mem_union_left _ hf))
    · obtain ⟨f, hf, rfl⟩ := mem_image.1 hy
      exact mem_union_right _ (mem_image_of_mem _ (mem_union_right _ (mem_biUnion.2 ⟨W, hW, hf⟩)))
  have hpOn_sub : ∀ W Q, pOn ends AW ⟨W, Q⟩ ⊆ fullP AW W := fun W Q => filter_subset _ _
  have hpOff_sub : ∀ W Q, pOff ends AW ⟨W, Q⟩ ⊆ fullP AW W :=
    fun W Q => (filter_subset _ _).trans subset_union_right
  -- every copy is a pair
  have hrg : ∀ y ∈ X' ∪ R', (e₂ y).card = k := by
    intro y hy
    rcases mem_union.1 hy with hy | hy
    · exact h.rgraph y (mem_union_left _ hy)
    · obtain ⟨f, hf, rfl⟩ := mem_image.1 hy
      rcases mem_union.1 hf with hf | hf
      · exact h.rgraph _ (mem_union_right _ (mem_image_of_mem _ hf))
      · obtain ⟨W, hW, hfW⟩ := mem_biUnion.1 hf
        exact (hA.off W hW).rgraph f hfW
  -- the pieces and their copies
  have hmem_fam : ∀ P ∈ cliqueFam ends 𝒱 AW Qon Qoff, ∃ W ∈ 𝒱, ∃ Q : Finset (Fin n),
      Q.card = q ∧ P ⊆ fullP AW W ∧ P.image e₂ = cliqueEdges k Q ∧
      ∀ y ∈ P, e₂ y ⊆ Q := by
    intro P hP
    rcases mem_union.1 hP with hP | hP
    · obtain ⟨⟨W, Q⟩, hWQ, rfl⟩ := mem_image.1 hP
      obtain ⟨hW, hQ⟩ := mem_sigma.1 hWQ
      exact ⟨W, hW, Q, (hA.on W hW).card_eq Q hQ, hpOn_sub W Q, image_pOnK hA hW hQ,
        fun y hy => (mem_pOn.1 hy).2⟩
    · obtain ⟨⟨W, Q⟩, hWQ, rfl⟩ := mem_image.1 hP
      obtain ⟨hW, hQ⟩ := mem_sigma.1 hWQ
      exact ⟨W, hW, Q, (hA.off W hW).card_eq Q hQ, hpOff_sub W Q, image_pOffK hA hW hQ,
        fun y hy => (mem_pOff.1 hy).2⟩
  have hinjP : ∀ P ∈ cliqueFam ends 𝒱 AW Qon Qoff, Set.InjOn e₂ ↑P := by
    intro P hP
    obtain ⟨W, hW, Q, -, hPW, -, -⟩ := hmem_fam P hP
    exact (fullP_injOnK hA hW (hsubV W hW)).mono hPW
  refine ⟨⟨fun y hy => hrg y hy, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [disjoint_left]
    intro y hy hy'
    obtain ⟨x, -, rfl⟩ := mem_image.1 hy
    obtain ⟨f, -, hf⟩ := mem_image.1 hy'
    exact Sum.inr_ne_inl hf
  · intro P hP S hS
    obtain ⟨W, hW, Q, hQ, -, himg, -⟩ := hmem_fam P hP
    rw [mdeg_eq_deg_image (hinjP P hP), himg]
    exact dvd_deg_cliqueEdges hQ (by omega)
  · intro P hP
    obtain ⟨W, hW, Q, -, hPW, -, -⟩ := hmem_fam P hP
    exact hPW.trans (hfullR W hW)
  · intro P hP
    obtain ⟨W, hW, Q, hQ, -, himg, -⟩ := hmem_fam P hP
    rw [← card_image_of_injOn (hinjP P hP), himg, cliqueEdges, card_powersetCard, hQ]
    exact Nat.le_add_left _ _
  · -- every copy lies in few pieces
    intro y hy
    have hy2 := hrg y hy
    set 𝒮 := 𝒱.filter fun W => y ∈ fullP AW W with h𝒮
    have hsub : (cliqueFam ends 𝒱 AW Qon Qoff).filter (fun P => y ∈ P) ⊆
        (𝒮.sigma fun W => (Qon W).filter fun Q => e₂ y ⊆ Q).image (pOn ends AW) ∪
        (𝒮.sigma fun W => (Qoff W).filter fun Q => e₂ y ⊆ Q).image (pOff ends AW) := by
      intro P hP
      obtain ⟨hP, hyP⟩ := mem_filter.1 hP
      rcases mem_union.1 hP with hP | hP
      · obtain ⟨⟨W, Q⟩, hWQ, rfl⟩ := mem_image.1 hP
        obtain ⟨hW, hQ⟩ := mem_sigma.1 hWQ
        obtain ⟨hyW, hyQ⟩ := mem_pOn.1 hyP
        exact mem_union_left _ (mem_image.2 ⟨⟨W, Q⟩, mem_sigma.2 ⟨mem_filter.2 ⟨hW, hyW⟩,
          mem_filter.2 ⟨hQ, hyQ⟩⟩, rfl⟩)
      · obtain ⟨⟨W, Q⟩, hWQ, rfl⟩ := mem_image.1 hP
        obtain ⟨hW, hQ⟩ := mem_sigma.1 hWQ
        have hyW := hpOff_sub W Q hyP
        obtain ⟨-, hyQ⟩ := mem_pOff.1 hyP
        exact mem_union_right _ (mem_image.2 ⟨⟨W, Q⟩, mem_sigma.2 ⟨mem_filter.2 ⟨hW, hyW⟩,
          mem_filter.2 ⟨hQ, hyQ⟩⟩, rfl⟩)
    have h𝒮c : 𝒮.card ≤ C + 1 := by
      have hsplit : 𝒮 ⊆ (𝒱.filter fun W => y ∈ W) ∪
          (𝒱.filter fun W => y ∈ (AW W).image Sum.inr) := by
        intro W hW
        obtain ⟨hW, hyW⟩ := mem_filter.1 hW
        rcases mem_union.1 hyW with h1 | h1
        · exact mem_union_left _ (mem_filter.2 ⟨hW, h1⟩)
        · exact mem_union_right _ (mem_filter.2 ⟨hW, h1⟩)
      refine (card_le_card hsplit).trans ((card_union_le _ _).trans (Nat.add_le_add ?_ ?_))
      · by_cases hyXF : y ∈ X' ∪ F.image Sum.inr
        · exact h.mult_le y hyXF
        · rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun W hW hyW => hyXF (hsubV W hW hyW))]
          exact Nat.zero_le _
      · refine card_le_one.2 fun W₁ h₁ W₂ h₂ => ?_
        obtain ⟨hW₁, hy₁⟩ := mem_filter.1 h₁
        obtain ⟨hW₂, hy₂⟩ := mem_filter.1 h₂
        obtain ⟨f₁, hf₁, rfl⟩ := mem_image.1 hy₁
        obtain ⟨f₂, hf₂, hff⟩ := mem_image.1 hy₂
        obtain rfl := Sum.inr_injective hff
        by_contra hne
        exact disjoint_left.1 (hA.disj W₁ hW₁ W₂ hW₂ hne) hf₁ hf₂
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    refine (Nat.add_le_add card_image_le card_image_le).trans ?_
    rw [card_sigma, card_sigma]
    have hon1 : ∀ W ∈ 𝒮, ((Qon W).filter fun Q => e₂ y ⊆ Q).card ≤ 1 :=
      fun W hW => cliqueMult_le_one (hA.on W (mem_filter.1 hW).1) hy2
    have hoff1 : ∀ W ∈ 𝒮, ((Qoff W).filter fun Q => e₂ y ⊆ Q).card ≤ 1 :=
      fun W hW => cliqueMult_le_one (hA.off W (mem_filter.1 hW).1) hy2
    have := sum_le_sum hon1
    have := sum_le_sum hoff1
    simp only [sum_const, smul_eq_mul, mul_one] at *
    omega
  · -- decompositions
    intro L' hL' hdiv
    obtain ⟨𝒰, h𝒰, Res, hRes, -, hpw, -, heq⟩ := h.decomp L' hL' hdiv
    rw [subset_empty.1 hRes, union_empty] at heq
    set 𝒰on := (𝒱.filter (· ∈ 𝒰)).sigma Qon with h𝒰on
    set 𝒰off := (𝒱.filter (· ∉ 𝒰)).sigma Qoff with h𝒰off
    have hdisjFull : ∀ W₁ ∈ 𝒱, ∀ W₂ ∈ 𝒱, W₁ ≠ W₂ →
        Disjoint (fullP AW W₁) ((AW W₂).image Sum.inr) := by
      intro W₁ hW₁ W₂ hW₂ hne
      rw [disjoint_left]
      intro y hy1 hy2
      obtain ⟨f, hf, rfl⟩ := mem_image.1 hy2
      rcases mem_union.1 hy1 with h1 | h1
      · exact inr_not_mem_pieceK hA hW₂ (hsubV W₁ hW₁) hf h1
      · obtain ⟨f', hf', hff⟩ := mem_image.1 h1
        obtain rfl := Sum.inr_injective hff
        exact disjoint_left.1 (hA.disj W₁ hW₁ W₂ hW₂ hne) hf' hf
    have hdisjW : ∀ W₁ ∈ 𝒱, ∀ W₂ ∈ 𝒱, W₁ ≠ W₂ → Disjoint W₁ W₂ →
        Disjoint (fullP AW W₁) (fullP AW W₂) := by
      intro W₁ hW₁ W₂ hW₂ hne hd
      refine disjoint_union_right.2 ⟨?_, hdisjFull W₁ hW₁ W₂ hW₂ hne⟩
      refine disjoint_union_left.2 ⟨hd, ?_⟩
      exact (hdisjFull W₂ hW₂ W₁ hW₁ (Ne.symm hne)).symm.mono_right subset_union_left
    have h2full : ∀ W ∈ 𝒱, ∀ y ∈ fullP AW W, (e₂ y).card = k :=
      fun W hW y hy => hrg y (hfullR W hW hy)
    refine ⟨𝒰on.image (pOn ends AW) ∪ 𝒰off.image (pOff ends AW), ?_, ∅, empty_subset _,
      mIsDivisible_empty _ _ _, ?_, by simp, ?_⟩
    · exact union_subset_union
        (image_subset_image (sigma_mono (filter_subset _ _) fun _ => subset_rfl))
        (image_subset_image (sigma_mono (filter_subset _ _) fun _ => subset_rfl))
    · intro A hAm B hBm hAB
      simp only [Function.onFun, id]
      rcases mem_union.1 (mem_coe.1 hAm) with hA' | hA' <;>
        rcases mem_union.1 (mem_coe.1 hBm) with hB' | hB'
      · obtain ⟨⟨W₁, Q₁⟩, h1, rfl⟩ := mem_image.1 hA'
        obtain ⟨⟨W₂, Q₂⟩, h2, rfl⟩ := mem_image.1 hB'
        obtain ⟨hW₁, hQ₁⟩ := mem_sigma.1 h1
        obtain ⟨hW₂, hQ₂⟩ := mem_sigma.1 h2
        obtain ⟨hW₁V, hW₁U⟩ := mem_filter.1 hW₁
        obtain ⟨hW₂V, hW₂U⟩ := mem_filter.1 hW₂
        by_cases hW : W₁ = W₂
        · subst hW
          have hQ : Q₁ ≠ Q₂ := fun hQ => hAB (by rw [hQ])
          exact disjoint_sameK (hA.on W₁ hW₁V) hQ₁ hQ₂ hQ
            (fun y hy => (mem_pOn.1 hy).2) (fun y hy => (mem_pOn.1 hy).2)
            (fun y hy => h2full W₁ hW₁V y (hpOn_sub _ _ hy))
        · exact (hdisjW W₁ hW₁V W₂ hW₂V hW (hpw (mem_coe.2 hW₁U) (mem_coe.2 hW₂U) hW)).mono
            (hpOn_sub _ _) (hpOn_sub _ _)
      · obtain ⟨⟨W₁, Q₁⟩, h1, rfl⟩ := mem_image.1 hA'
        obtain ⟨⟨W₂, Q₂⟩, h2, rfl⟩ := mem_image.1 hB'
        obtain ⟨hW₁, -⟩ := mem_sigma.1 h1
        obtain ⟨hW₂, -⟩ := mem_sigma.1 h2
        obtain ⟨hW₁V, hW₁U⟩ := mem_filter.1 hW₁
        obtain ⟨hW₂V, hW₂U⟩ := mem_filter.1 hW₂
        have hne : W₁ ≠ W₂ := fun h => hW₂U (h ▸ hW₁U)
        exact (hdisjFull W₁ hW₁V W₂ hW₂V hne).mono (hpOn_sub _ _) (filter_subset _ _)
      · obtain ⟨⟨W₁, Q₁⟩, h1, rfl⟩ := mem_image.1 hA'
        obtain ⟨⟨W₂, Q₂⟩, h2, rfl⟩ := mem_image.1 hB'
        obtain ⟨hW₁, -⟩ := mem_sigma.1 h1
        obtain ⟨hW₂, -⟩ := mem_sigma.1 h2
        obtain ⟨hW₁V, hW₁U⟩ := mem_filter.1 hW₁
        obtain ⟨hW₂V, hW₂U⟩ := mem_filter.1 hW₂
        have hne : W₂ ≠ W₁ := fun h => hW₁U (h ▸ hW₂U)
        exact ((hdisjFull W₂ hW₂V W₁ hW₁V hne).mono (hpOn_sub _ _) (filter_subset _ _)).symm
      · obtain ⟨⟨W₁, Q₁⟩, h1, rfl⟩ := mem_image.1 hA'
        obtain ⟨⟨W₂, Q₂⟩, h2, rfl⟩ := mem_image.1 hB'
        obtain ⟨hW₁, hQ₁⟩ := mem_sigma.1 h1
        obtain ⟨hW₂, hQ₂⟩ := mem_sigma.1 h2
        obtain ⟨hW₁V, -⟩ := mem_filter.1 hW₁
        obtain ⟨hW₂V, -⟩ := mem_filter.1 hW₂
        by_cases hW : W₁ = W₂
        · subst hW
          have hQ : Q₁ ≠ Q₂ := fun hQ => hAB (by rw [hQ])
          exact disjoint_sameK (hA.off W₁ hW₁V) hQ₁ hQ₂ hQ
            (fun y hy => (mem_pOff.1 hy).2) (fun y hy => (mem_pOff.1 hy).2)
            (fun y hy => h2full W₁ hW₁V y (hpOff_sub _ _ hy))
        · exact (hdisjFull W₁ hW₁V W₂ hW₂V hW).mono (hpOff_sub _ _) (filter_subset _ _)
    · rw [union_empty]
      have hU : ∀ y, (∃ W ∈ 𝒰, y ∈ W) ↔ y ∈ F.image Sum.inr ∪ L' := by
        intro y
        rw [← heq, mem_sup]
        rfl
      ext y
      simp only [hR', mem_sup, mem_union, mem_image, id]
      constructor
      · rintro ⟨P, hP, hyP⟩
        rcases hP with ⟨⟨W, Q⟩, hWQ, rfl⟩ | ⟨⟨W, Q⟩, hWQ, rfl⟩
        · obtain ⟨hW, -⟩ := mem_sigma.1 hWQ
          obtain ⟨hWV, hWU⟩ := mem_filter.1 hW
          obtain ⟨hyW, -⟩ := mem_pOn.1 hyP
          rcases mem_union.1 hyW with h1 | h1
          · rcases mem_union.1 ((hU y).1 ⟨W, hWU, h1⟩) with h2 | h2
            · obtain ⟨f, hf, rfl⟩ := mem_image.1 h2
              exact Or.inl ⟨f, Or.inl hf, rfl⟩
            · exact Or.inr h2
          · obtain ⟨f, hf, rfl⟩ := mem_image.1 h1
            exact Or.inl ⟨f, Or.inr (mem_biUnion.2 ⟨W, hWV, hf⟩), rfl⟩
        · obtain ⟨hW, -⟩ := mem_sigma.1 hWQ
          obtain ⟨hWV, -⟩ := mem_filter.1 hW
          obtain ⟨hyA, -⟩ := mem_pOff.1 hyP
          obtain ⟨f, hf, rfl⟩ := mem_image.1 hyA
          exact Or.inl ⟨f, Or.inr (mem_biUnion.2 ⟨W, hWV, hf⟩), rfl⟩
      · have hon : ∀ W ∈ 𝒰, y ∈ fullP AW W →
            ∃ P, ((∃ a ∈ 𝒰on, pOn ends AW a = P) ∨ ∃ a ∈ 𝒰off, pOff ends AW a = P) ∧ y ∈ P := by
          intro W hWU hyW
          have hWV := h𝒰 hWU
          obtain ⟨Q, hQ, hyQ⟩ := exists_on_coverK hA hWV hyW
          exact ⟨_, Or.inl ⟨⟨W, Q⟩, mem_sigma.2 ⟨mem_filter.2 ⟨hWV, hWU⟩, hQ⟩, rfl⟩,
            mem_pOn.2 ⟨hyW, hyQ⟩⟩
        rintro (⟨f, hf, rfl⟩ | hyL)
        · rcases hf with hfF | hfA
          · obtain ⟨W, hWU, hyW⟩ := (hU _).2 (mem_union_left _ (mem_image_of_mem _ hfF))
            exact hon W hWU (mem_union_left _ hyW)
          · obtain ⟨W, hWV, hfW⟩ := mem_biUnion.1 hfA
            by_cases hWU : W ∈ 𝒰
            · exact hon W hWU (mem_union_right _ (mem_image_of_mem _ hfW))
            · obtain ⟨Q, hQ, hfQ⟩ := exists_off_coverK hA hWV hfW
              exact ⟨_, Or.inr ⟨⟨W, Q⟩, mem_sigma.2 ⟨mem_filter.2 ⟨hWV, hWU⟩, hQ⟩, rfl⟩,
                mem_pOff.2 ⟨mem_image_of_mem _ hfW, hfQ⟩⟩
        · obtain ⟨W, hWU, hyW⟩ := (hU y).2 (mem_union_right _ hyL)
          exact hon W hWU (mem_union_left _ hyW)
  · -- the pieces are cliques
    intro P hP S hS hSk
    obtain ⟨W, hW, Q, -, -, himg, hPQ⟩ := hmem_fam P hP
    have hSQ : S ⊆ Q := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := mem_biUnion.1 (hS hx)
      exact hPQ c hc hxc
    have : S ∈ P.image e₂ := by
      rw [himg, cliqueEdges, mem_powersetCard]
      exact ⟨hSQ, hSk⟩
    obtain ⟨c, hc, hce⟩ := mem_image.1 this
    exact ⟨c, hc, hce⟩

end Facts

end RefinedAbsorption.General
