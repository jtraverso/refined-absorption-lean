module
public import RefinedAbsorption.Original2024.MinDegree

/-!
# The theorems of the original article (Delcourt–Postle 2024), collected

M. Delcourt and L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture*,
arXiv:2402.17855v1.  The statements are those of `RequestProject/Original2024/Defs.lean`.

* `theorem_1_4`: Theorem 1.4 (absorbers exist; Glock–Kühn–Lo–Osthus), proved in this project.
* `theorem_3_8`: Theorem 3.8 (multi-refiner theorem) for `q > r ≥ 1`, in the inductive form of
  the article; the lower-uniformity hypothesis is not needed (the conclusion is proved outright).
  The conclusion `MultiRefinerConclusion` does not include the `Y`-flatness output of the article;
  the version with flatness is `theorem_3_8_flat` (`RequestProject/Original2024/FlatOne.lean`).
* `theorem_1_11`, `theorem_1_11_strong`: Theorem 1.11 (refined efficient refiner inside a dense
  host) for `q > r ≥ 1`; the strong form adds one `X`-edge per piece and the family degree bound.
* `theorem_1_7`, `theorem_1_7_strong`: Theorem 1.7 (refined efficient omni-absorber inside a
  dense host) for `q > r ≥ 1`; the strong form adds one `X`-edge per clique of the family.
* `theorem_6_1` (in `MinDegree.lean`): Theorem 6.1 (minimum degree version of the Existence
  Conjecture, `λ = 1`).

The survey interface (`RequestProject/Final.lean`) is unchanged.
-/

@[expose] public section

namespace RefinedAbsorption.Original2024

open Finset

/-- **Theorem 1.4 (existence of absorbers, Glock–Kühn–Lo–Osthus).** -/
theorem theorem_1_4 : Theorem_1_4 := Absorber17.absorberExistence

/-- The multi-refiner conclusion for `q > r ≥ 2`: the witnesses of the project's multi-refiner
construction (`General.nativeStrongMultiRefiners_all`), with the ambient vertex set `Fin n`. -/
theorem multiRefinerConclusion_two_le {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    MultiRefinerConclusion q r := by
  obtain ⟨C, hC, n₀, h⟩ := General.nativeStrongMultiRefiners_all hr hrq
  refine ⟨C, hC, n₀, fun n hn X D hX hXD hDn => ?_⟩
  obtain ⟨E, hE, ends, K, Xl, R, 𝒲, B, hXl, hB, hS⟩ := h n hn X D hX hXD hDn
  exact ⟨E, hE, ends, K, Xl, R, 𝒲, B, hXl, hB, ⟨fun _ _ => subset_univ _, hS.refiner⟩, hS⟩

/-- **Theorem 3.8 (multi-refiner theorem)**, `q > r ≥ 2`. -/
theorem theorem_3_8_two_le {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) : Theorem_3_8_for q r :=
  fun _ => multiRefinerConclusion_two_le hr hrq

/-- **Theorem 1.11** for all `q > r ≥ 1`. -/
theorem theorem_1_11 : Theorem_1_11 := by
  intro q r hr hrq
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    exact theorem_1_11_one (by omega)
  · exact theorem_1_11_two_le h hrq

/-- **Theorem 1.7** for all `q > r ≥ 1`. -/
theorem theorem_1_7 : Theorem_1_7 := by
  intro q r hr hrq
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    exact theorem_1_7_one (by omega)
  · exact theorem_1_7_two_le h hrq


/-- A simple refined refiner is a multi-refiner whose copies are labelled by themselves. -/
theorem IsRefinedRefiner.toMulti {V : Type*} [DecidableEq V] {q r C : ℕ}
    {X R : Finset (Finset V)} {𝒲 : Finset (Finset (Finset V))}
    (h : IsRefinedRefiner q r C X R 𝒲) : MultiRefiner.IsMultiRefiner q r C id X R 𝒲 := by
  refine ⟨h.rgraph, h.disjoint, h.divisible, h.subset, h.card_le, h.mult_le, fun L hL hd => ?_⟩
  obtain ⟨𝒰, h1, h2, h3⟩ := h.decomp L hL hd
  exact ⟨𝒰, h1, ∅, subset_rfl, MultiRefiner.mIsDivisible_empty q r id, h2,
    disjoint_empty_right _, by simpa using h3⟩

/-- The multi-refiner conclusion for `r = 1` (from the chain refiner). -/
theorem multiRefinerConclusion_one {q : ℕ} (hq : 2 ≤ q) : MultiRefinerConclusion q 1 := by
  refine ⟨8 * q, by omega, 0, fun n _ X D hX hXD hDn => ?_⟩
  have hδ : MinDegGE 1 (completeRGraph (Fin n) 1) ((1 - 1 / 2) * n) := by
    intro S hS
    have hS0 : S = ∅ := by rw [← card_eq_zero]; omega
    subst hS0
    rw [deg_completeRGraph (by simp)]
    simp only [card_empty, Nat.sub_zero, Nat.choose_one_right]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hXK : X ⊆ completeRGraph (Fin n) 1 := fun e he =>
    mem_powersetCard.2 ⟨subset_univ _, hX e he⟩
  obtain ⟨R, 𝒲, hR, -, -, -, honeX, hRc, h𝒲c⟩ :=
    hostChain hq n (completeRGraph (Fin n) 1) X D (fun e he => (mem_powersetCard.1 he).2) hδ
      hXK hXD hDn
  have hXD' : (X.card : ℝ) ≤ D := by
    have h := hXD ∅ (by simp)
    rwa [RefinedAbsorption.ChainRefiner.deg_empty] at h
  have hS0 : ∀ S : Finset (Fin n), S.card = 1 - 1 → S = ∅ := fun S hS => by
    rw [← card_eq_zero]; omega
  refine ⟨Finset (Fin n), inferInstance, id, X, X, R, 𝒲, X.card, image_id, ?_,
    ⟨fun _ _ => subset_univ _, IsRefinedRefiner.toMulti hR⟩,
    ⟨IsRefinedRefiner.toMulti hR, subset_rfl, Set.injOn_id _, honeX, fun S hS => ?_, fun S hS => ?_,
      fun S hS => ?_⟩⟩
  · have hM : D ≤ max D (budget n 1) := le_max_left _ _
    have hq1 : (1 : ℝ) ≤ 8 * q := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    have h0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
    push_cast
    nlinarith
  · rw [hS0 S hS]
    exact le_of_eq (RefinedAbsorption.ChainRefiner.deg_empty X)
  · rw [hS0 S hS]
    show deg R ∅ ≤ _
    rw [RefinedAbsorption.ChainRefiner.deg_empty]
    exact hRc.trans (Nat.mul_le_mul_right _ (by omega))
  · exact (card_filter_le _ _).trans (h𝒲c.trans (Nat.mul_le_mul_right _ (by omega)))

/-- **Theorem 3.8 (multi-refiner theorem)**, `r = 1`. -/
theorem theorem_3_8_one {q : ℕ} (hq : 2 ≤ q) : Theorem_3_8_for q 1 :=
  fun _ => multiRefinerConclusion_one hq

/-- **Theorem 3.8** for all `q > r ≥ 1`. -/
theorem theorem_3_8 : ∀ q r : ℕ, 1 ≤ r → r < q → Theorem_3_8_for q r := by
  intro q r hr hrq
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    exact theorem_3_8_one (by omega)
  · exact theorem_3_8_two_le h hrq

/-- **Theorem 1.11 (strong form)** for all `q > r ≥ 1`. -/
theorem theorem_1_11_strong : ∀ q r : ℕ, 1 ≤ r → r < q → Theorem_1_11_strong_for q r := by
  intro q r hr hrq
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    exact theorem_1_11_strong_one (by omega)
  · exact theorem_1_11_strong_two_le h hrq

/-- **Theorem 1.7 (strong form)** for all `q > r ≥ 1`. -/
theorem theorem_1_7_strong : ∀ q r : ℕ, 1 ≤ r → r < q → Theorem_1_7_strong_for q r := by
  intro q r hr hrq
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    exact theorem_1_7_strong_one (by omega)
  · exact theorem_1_7_strong_two_le h hrq

end RefinedAbsorption.Original2024
