module
public import RefinedAbsorption.Extensions.PolynomialResolution
public import RefinedAbsorption.Extensions.NashWilliamsSchedule
public import RefinedAbsorption.ExternalProofs

/-! Closed assembly from the proved external endpoints. The older conditional consumers remain unchanged. -/
@[expose] public section
namespace RefinedAbsorption.Assembly
open Finset RefinedAbsorption.Extensions RefinedAbsorption.Original2024
open RefinedAbsorption.External RefinedAbsorption.External.NashWilliams
open RefinedAbsorption.External.PippengerSpencer

variable {q r : ℕ}

theorem steiner_quantitatively_almost_resolvable
    (hr : 2 ≤ r) (hrq : r < q) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ 𝒮 : Finset (Finset (Fin n)),
      IsSteinerSystem q r 𝒮 →
      ∃ (m : ℕ) (c : Finset (Fin n) → Fin m),
        (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) +
          (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ^ (1 - γ) ∧
        ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B' :=
  RefinedAbsorption.Extensions.steiner_quantitatively_almost_resolvable pippengerSpencerPolynomial hr hrq

theorem exists_quantitatively_almost_resolvable_steiner
    (hr : 2 ≤ r) (hrq : r < q) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮 ∧
      ∃ (m : ℕ) (c : Finset (Fin n) → Fin m),
        (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) +
          (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ^ (1 - γ) ∧
        ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B' :=
  RefinedAbsorption.Extensions.exists_quantitatively_almost_resolvable_steiner pippengerSpencerPolynomial hr hrq

theorem nash_williams_scheduled_decomposition :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → IsTriangleDivisible G → 3 * Fintype.card V ≤ 4 * G.minDegree →
      ∃ T : Finset (Finset V), IsTriangleDecomposition G T ∧
        ∃ (m : ℕ) (c : Finset V → Fin m), IsProperEdgeColouring T m c ∧
          (G.maxDegree : ℝ) / 2 ≤ (m : ℝ) ∧
          (m : ℝ) ≤ (G.maxDegree : ℝ) / 2 + ((G.maxDegree : ℝ) / 2) ^ (1 - γ) :=
  RefinedAbsorption.External.nash_williams_scheduled_decomposition pippengerSpencerPolynomial nashWilliamsExternal

end RefinedAbsorption.Assembly
