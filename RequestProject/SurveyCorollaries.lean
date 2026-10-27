module
public import RequestProject.SurveyReserves
public import RequestProject.Final
public import RequestProject.Multigraph.Existence

/-!
# Further results of the survey, unconditionally

L. Postle, *Refined Absorption* (survey, arXiv:2510.19978).

* `theorem_1_8`: Theorem 1.8 (efficient omni-absorbers), the statement of Theorem 1.10 without
  refinedness.
* `lemma_2_1`: Lemma 2.1 (Reserves), exactly as stated (`reservesLemma`).
* `existenceConjecture_steiner_section2`: the Existence Conjecture for Steiner systems, obtained by
  instantiating the Section 2 argument (`steinerExistence_of_refinedAbsorption`) with the proved
  Lemma 2.1, Theorem 1.10, Lemma 2.2 and Corollary 2.4.
* `existenceConjecture`: Conjecture 1.1 (Keevash's Theorem 1.2), for every `λ ≥ 1`.
-/

@[expose] public section

namespace RefinedAbsorption.Final

open RefinedAbsorption

/-- **Theorem 1.8 (Efficient omni-absorber).**  For `q > r ≥ 1` there is `C ≥ 1` such that: if
`X ⊆ K_n^r` has `Δ_{r-1}(X) ≤ D ≤ n / C`, then there is a `K_q^r`-omni-absorber `A` for `X` with
`Δ_{r-1}(A) ≤ C · max(D, n^{1-1/r} log n)`. -/
def EfficientOmniAbsorber : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, ∀ X : Finset (Finset (Fin n)),
    ∀ D : ℝ, IsRGraph r X → MaxDegLE r X D → D ≤ n / C →
      ∃ A F : Finset (Finset (Fin n)), ∃ QA : Finset (Finset (Fin n)) → Finset (Finset (Fin n)),
        IsOmniAbsorber q r X A F QA ∧
          MaxDegLE r A (C * max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n))

/-- **Theorem 1.8** (from Theorem 1.10). -/
theorem theorem_1_8 : EfficientOmniAbsorber := by
  intro q r hr hrq
  obtain ⟨C, hC, h⟩ := theorem_1_10 q r hr hrq
  refine ⟨C, hC, fun n X D hX hXD hDn => ?_⟩
  obtain ⟨A, F, QA, h1, -, h3⟩ := h n X D hX hXD hDn
  exact ⟨A, F, QA, h1, h3⟩

/-- **Lemma 2.1 (Reserves)**, exactly as stated in the survey. -/
theorem lemma_2_1 : ReservesLemma := reservesLemma

/-- **The Existence Conjecture for Steiner systems via Section 2 of the survey**: the argument of
Section 2 (`steinerExistence_of_refinedAbsorption`), instantiated with the proved Lemma 2.1,
Theorem 1.10, Lemma 2.2 and Corollary 2.4 (general polynomial error). -/
theorem existenceConjecture_steiner_section2 : SteinerExistenceConjecture :=
  steinerExistence_of_refinedAbsorption lemma_2_1 theorem_1_10 lemma_2_2 nibbleWithReservesGen_proved

/-- **Conjecture 1.1 (Existence Conjecture; Keevash's Theorem 1.2)** for every `λ ≥ 1`. -/
theorem existenceConjecture : ExistenceConjecture := existenceConjecture_proved

end RefinedAbsorption.Final
