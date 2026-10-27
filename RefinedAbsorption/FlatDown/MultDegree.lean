module
public import RefinedAbsorption.FlatDown.Small

/-!
# Quantitative Multiplicity Reduction

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Multiplicity Reduction Lemma); the
survey arXiv:2510.19978, Section 3.4.  Lean formalization: Juan Pablo Traverso Gianini,
Apache-2.0.

`multReduction` (in `Small.lean`) applies the 1-uniform chain construction to every class of
parallel copies.  Here we add the two quantitative facts used when Multiplicity Reduction is
alternated with Refine Down:

* `mdeg_mR_le`: the new copies have `(r-1)`-degrees (indeed degrees of all sets) at most
  `(M + 2)^2` times those of `X`: no new edge is created, and each class of `c ≥ 1` parallel copies
  gets at most `(M + 2)^2 · c` new parallel copies;
* `mult_mY_le`: the residue has multiplicity at most `M` on every `r`-set.

`multiplicityReduction_quant` packages them: for `r ≤ q` there are `M ≥ 1` and `C` such that
every `r`-multigraph `X` has a `C`-refined residual multi-refiner made of new parallel copies of
its own edges, with residue contained in the new copies, of multiplicity `≤ M` on every `r`-set,
and with `mdeg R S ≤ (M + 2)^2 · mdeg X S` for every `S`.
-/

@[expose] public section

namespace RefinedAbsorption.FlatDown

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.ChainRefiner

variable {V E : Type} [DecidableEq V] [DecidableEq E] {ends : E → Finset V} {X : Finset E}
  {M : ℕ}

theorem card_Rlab_le (M m : ℕ) : (Rlab M m).card ≤ (m + 1) * (M - 1) + M := by
  unfold Rlab
  refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · refine card_image_le.trans ?_
    rw [card_product, card_range, card_range]
  · refine card_image_le.trans ?_
    rw [card_range]
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM; simp
    · exact (Nat.mod_lt _ hM).le

/-- The new copies of one class. -/
def mRcls (ends : E → Finset V) (X : Finset E) (M : ℕ) (e : Finset V) : Finset (MLab V) :=
  (Rlab M (clen ends X M e) ∪ (resIdx ends X M e).image xl).image fun a => (e, a)

omit [DecidableEq E] in
theorem card_mRcls_le (e : Finset V) (he : 1 ≤ (cls ends X e).card) :
    (mRcls ends X M e).card ≤ (M + 2) ^ 2 * (cls ends X e).card := by
  unfold mRcls
  refine card_image_le.trans ((card_union_le _ _).trans ?_)
  have h1 := card_Rlab_le M (clen ends X M e)
  have h2 : ((resIdx ends X M e).image xl).card ≤ M := by
    refine card_image_le.trans ?_
    simp [resIdx, clen]
  set c := (cls ends X e).card
  have hc : clen ends X M e = c + M := rfl
  rw [hc] at h1 ⊢
  have h3 : (c + M + 1) * (M - 1) ≤ (c + M + 1) * M := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h4 : M * M ≤ c * (M * M) := Nat.le_mul_of_pos_left _ he
  have h5 : M ≤ c * M := Nat.le_mul_of_pos_left _ he
  have h6 : (M + 2) ^ 2 * c = c * (M * M) + 4 * (c * M) + 4 * c := by ring
  have h7 : (c + M + 1) * M = c * M + M * M + M := by ring
  omega

omit [DecidableEq E] in
theorem mem_mRcls_fst {e : Finset V} {y : MLab V} (hy : y ∈ mRcls ends X M e) : y.1 = e := by
  obtain ⟨a, -, rfl⟩ := mem_image.1 hy
  rfl

omit [DecidableEq E] in
theorem mR_eq_biUnion : mR ends X M = (X.image ends).biUnion (mRcls ends X M) := rfl

/-- **Degree bound for multiplicity reduction.**  The new copies have degree at most
`(M + 2)^2` times the degree of `X`, at every vertex set `S`. -/
theorem mdeg_mR_le (S : Finset V) :
    mdeg (mEnds ends) ((mR ends X M).image Sum.inr) S ≤ (M + 2) ^ 2 * mdeg ends X S := by
  classical
  have hleft : mdeg (mEnds ends) ((mR ends X M).image Sum.inr) S =
      ((mR ends X M).filter fun y => S ⊆ y.1).card := by
    unfold mdeg
    rw [filter_image, card_image_of_injective _ Sum.inr_injective]
    rfl
  rw [hleft, mR_eq_biUnion, filter_biUnion]
  refine card_biUnion_le.trans ?_
  have hX : mdeg ends X S = ∑ e ∈ (X.image ends).filter (S ⊆ ·), (cls ends X e).card := by
    unfold mdeg cls
    rw [card_eq_sum_card_fiberwise (f := ends) (t := (X.image ends).filter (S ⊆ ·))]
    · apply sum_congr rfl
      intro e he
      congr 1
      ext x
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨hx, -⟩, rfl⟩; exact ⟨hx, rfl⟩
      · rintro ⟨hx, rfl⟩; exact ⟨⟨hx, (mem_filter.1 he).2⟩, rfl⟩
    · intro x hx
      exact mem_filter.2 ⟨mem_image_of_mem _ (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩
  rw [hX, mul_sum, ← sum_filter_add_sum_filter_not (X.image ends) (S ⊆ ·)]
  have hzero : ∑ e ∈ (X.image ends).filter (fun e => ¬ S ⊆ e),
      ((mRcls ends X M e).filter fun y => S ⊆ y.1).card = 0 := by
    apply sum_eq_zero
    intro e he
    rw [card_eq_zero, filter_eq_empty_iff]
    intro y hy
    rw [mem_mRcls_fst hy]
    exact (mem_filter.1 he).2
  rw [hzero, add_zero]
  apply sum_le_sum
  intro e he
  obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_filter.1 he).1
  have hc : 1 ≤ (cls ends X (ends x)).card :=
    card_pos.2 ⟨x, mem_filter.2 ⟨hx, rfl⟩⟩
  exact (card_filter_le _ _).trans (card_mRcls_le _ hc)

/-- **The residue of multiplicity reduction has multiplicity at most `M`.** -/
theorem mult_mY_le (e : Finset V) : mult (mEnds ends) (mY ends X M) e ≤ M := by
  classical
  unfold mult
  have hsub : (mY ends X M).filter (fun i => mEnds ends i = e) ⊆
      (resIdx ends X M e).image fun i => phi ends X e (xl i) := by
    intro c hc
    obtain ⟨hc, hce⟩ := mem_filter.1 hc
    obtain ⟨e', -, hc⟩ := mem_biUnion.1 hc
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hc
    have : e' = e := by rw [← hce, mEnds_phi]
    subst this
    exact mem_image_of_mem _ hi
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  simp [resIdx, clen]

/-- The pieces of multiplicity reduction consist of parallel copies. -/
theorem mW_parallel {W : Finset (E ⊕ MLab V)} (hW : W ∈ mW ends X M) :
    ∀ c ∈ W, W.biUnion (Sum.elim ends Prod.fst) ⊆ Sum.elim ends Prod.fst c := by
  classical
  have key : ∃ e, ∀ c ∈ W, Sum.elim ends Prod.fst c = e := by
    unfold mW at hW
    obtain ⟨e, -, hW⟩ := mem_biUnion.1 hW
    refine ⟨e, fun c hc => ?_⟩
    rcases mem_insert.1 hW with rfl | hW
    · obtain ⟨a, -, rfl⟩ := mem_image.1 hc
      exact mEnds_phi e a
    · obtain ⟨p, -, rfl⟩ := mem_image.1 hW
      obtain ⟨a, -, rfl⟩ := mem_image.1 hc
      exact mEnds_phi e a
  obtain ⟨e, he⟩ := key
  intro c hc v hv
  obtain ⟨c', hc', hvc'⟩ := mem_biUnion.1 hv
  rw [he c' hc'] at hvc'
  rw [he c hc]
  exact hvc'

/-- **Multiplicity Reduction Lemma, quantitative form.**  For `r ≤ q` there are `M ≥ 1` and `C`
such that every `r`-multigraph `X` has a `C`-refined residual multi-refiner `R` made of new copies
parallel to copies of `X`, whose residue `Y` consists of new copies, has multiplicity at most `M`
on every `r`-set, and such that `mdeg R S ≤ (M + 2)^2 · mdeg X S` for every vertex set `S`.
Every piece consists of parallel copies. -/
theorem multiplicityReduction_quant (q r : ℕ) (hrq : r ≤ q) :
    ∃ M C : ℕ, 1 ≤ M ∧ ∀ {V E : Type} [DecidableEq V] [DecidableEq E]
      (ends : E → Finset V) (X : Finset E), MIsRGraph r ends X →
      ∃ (N : Type) (_ : DecidableEq N) (endsN : N → Finset V) (R : Finset N)
        (Y : Finset (E ⊕ N)) (𝒲 : Finset (Finset (E ⊕ N))),
        (∀ y ∈ R, endsN y ∈ X.image ends) ∧ Y ⊆ R.image Sum.inr ∧
        IsResidualMultiRefiner q r C (Sum.elim ends endsN) (X.image Sum.inl) (R.image Sum.inr)
          Y 𝒲 ∧
        (∀ e, mult (Sum.elim ends endsN) Y e ≤ M) ∧
        (∀ S, mdeg (Sum.elim ends endsN) (R.image Sum.inr) S ≤ (M + 2) ^ 2 * mdeg ends X S) ∧
        (∀ W ∈ 𝒲, ∀ c ∈ W, W.biUnion (Sum.elim ends endsN) ⊆ Sum.elim ends endsN c) := by
  set M := RefinedAbsorption.MultiRefiner.fakeModulus q r with hMdef
  have hM : 1 ≤ M := fakeModulus_pos hrq
  have hdvd : ∀ s < r, (q - s).choose (r - s) ∣ M := fun s hs => dvd_fakeModulus hs
  refine ⟨M, 5 * M + 1, hM, ?_⟩
  intro V E _ _ ends X hX
  exact ⟨MLab V, inferInstance, Prod.fst, mR ends X M, mY ends X M, mW ends X M,
    fun y hy => mR_ends hy, mY_subset_mR, multReduction hM hdvd hX, fun e => mult_mY_le e,
    fun S => mdeg_mR_le S, fun W hW => mW_parallel hW⟩

end RefinedAbsorption.FlatDown
