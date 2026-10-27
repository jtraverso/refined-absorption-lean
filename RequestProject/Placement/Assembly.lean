module
public import RequestProject.Placement.Reduction
public import RequestProject.Placement.Absorbers

/-!
# Assembling the final embedding step

* `absorbersOnStrongRefiner`: bounded absorbers are attached, inside `Fin n`, to the pieces of a
  strong refiner, with total degree `O(D)`.
* `refinerAbsorbers_of_strongMultiRefiner`: from a strong multi-refiner on `Fin n` with budget `D`
  we obtain, inside `Fin n`, a refined refiner of `X` with attached absorbers and
  `Δ_{r-1}(R ∪ ⋃ A W) = O(D)`: fake edges are placed first (`placedMultiplicityReduction`), then
  absorbers (`placedAttachedAbsorbers`).
* `refinerAbsorbersFor_of_native`: `RefinerAbsorbersFor q r` follows from the native
  construction `NativeStrongMultiRefiners q r` (strong multi-refiners with budget
  `O(max(D, n^{1-1/r} log n))`, the output of the refine-down construction).  The native
  construction itself is **not** proved here, so `RefinerAbsorbersFor q r` (for `r ≥ 2`) remains
  conditional on it.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Absorber17

/-- **Absorbers on a strong refiner, inside `Fin n`.** -/
theorem absorbersOnStrongRefiner {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) (C : ℕ) :
    ∃ Ca : ℕ, 0 < Ca ∧ ∀ (n : ℕ) (X R : Finset (Finset (Fin n)))
      (𝒲 : Finset (Finset (Finset (Fin n)))) (D : ℕ),
      IsStrongRefiner q r C X R 𝒲 D → Ca * D ≤ n → 0 < n →
      ∃ A Qon Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n)),
        IsAttachedAbsorbers q r X R 𝒲 A Qon Qoff ∧
        ∀ S : Finset (Fin n), S.card = r - 1 → deg (R ∪ 𝒲.sup A) S ≤ Ca * D := by
  obtain ⟨B, Cp, hCp, habs⟩ := placedAttachedAbsorbers (by omega : 1 ≤ r) hrq C
  refine ⟨Cp * (1 + C) + C + Cp * C + 1, by omega, ?_⟩
  intro n X R 𝒲 D hS hD hn
  have hR := hS.refiner
  have hdegXR : ∀ S : Finset (Fin n), S.card = r - 1 → deg (X ∪ R) S ≤ (1 + C) * D := by
    intro S hS'
    have h1 : deg (X ∪ R) S ≤ deg X S + deg R S := by
      unfold deg; rw [filter_union]; exact card_union_le _ _
    have := hS.degX S hS'
    have := hS.degR S hS'
    nlinarith
  have hle : ∀ x : ℕ, x ≤ Cp * (1 + C) + C + Cp * C + 1 → x * D ≤ n := fun x hx =>
    (Nat.mul_le_mul_right _ hx).trans hD
  obtain ⟨A, Qon, Qoff, hA, -, hdeg⟩ := habs n X R 𝒲 (C * D)
    (fun W hW e he => hR.rgraph e (hR.subset W hW he)) hR.divisible hR.card_le
    (fun S hS' => le_trans (Nat.mul_le_mul_left _ (hdegXR S hS'))
      (by rw [← mul_assoc]; exact hle _ (by omega)))
    hS.pieceDeg (by rw [← mul_assoc]; exact hle _ (by omega)) hn
  refine ⟨A, Qon, Qoff, hA, fun S hS' => ?_⟩
  have h1 : deg (R ∪ 𝒲.sup A) S ≤ deg R S + deg (𝒲.sup A) S := by
    unfold deg; rw [filter_union]; exact card_union_le _ _
  have h2 := hS.degR S hS'
  have h3 := hdeg S hS'
  calc deg (R ∪ 𝒲.sup A) S ≤ C * D + Cp * (C * D) := h1.trans (Nat.add_le_add h2 h3)
    _ = (C + Cp * C) * D := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

/-- **Refiner with attached absorbers inside `Fin n` from a strong multi-refiner.**  Fake edges
and absorbers are both placed inside `Fin n` with the (clustered) Partial Clique Embedding
Lemma. -/
theorem refinerAbsorbers_of_strongMultiRefiner {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) (C : ℕ)
    (hC : 1 ≤ C) :
    ∃ Cf : ℕ, 1 ≤ Cf ∧ ∀ (n : ℕ) {E : Type*} [DecidableEq E] (ends : E → Finset (Fin n))
      (K X R : Finset E) (𝒲 : Finset (Finset E)) (D : ℕ),
      IsStrongMultiRefiner q r C ends K X R 𝒲 D → Cf * D ≤ n → 0 < n →
      ∃ (R' : Finset (Finset (Fin n))) (𝒲' : Finset (Finset (Finset (Fin n))))
        (A Qon Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
        IsRefinedRefiner q r Cf (X.image ends) R' 𝒲' ∧
        IsAttachedAbsorbers q r (X.image ends) R' 𝒲' A Qon Qoff ∧
        ∀ S : Finset (Fin n), S.card = r - 1 → deg (R' ∪ 𝒲'.sup A) S ≤ Cf * D := by
  obtain ⟨C', hC', hred⟩ := placedMultiplicityReduction hr hrq C hC
  obtain ⟨Ca, hCa, habs⟩ := absorbersOnStrongRefiner hr hrq C'
  refine ⟨C' + Ca + 1, by omega, ?_⟩
  intro n E _ ends K X R 𝒲 D hS hD hn
  obtain ⟨R', 𝒲', hS'⟩ := hred n ends K X R 𝒲 D hS
    ((Nat.mul_le_mul_right _ (by omega)).trans hD) hn
  obtain ⟨A, Qon, Qoff, hA, hdeg⟩ := habs n _ R' 𝒲' D hS'
    ((Nat.mul_le_mul_right _ (by omega)).trans hD) hn
  exact ⟨R', 𝒲', A, Qon, Qoff, hS'.refiner.mono (by omega), hA, fun S hS'' =>
    (hdeg S hS'').trans (Nat.mul_le_mul_right _ (by omega))⟩

/-- **The native construction** (output of the refine-down construction, not proved here):
for `q > r` there is `C ≥ 1` such that for all large `n`, every `r`-graph `X ⊆ K_n^r` with
`Δ_{r-1}(X) ≤ D ≤ n / C` is the image of the kept part of a strong `C`-refined multi-refiner on
`Fin n` with degree budget `B ≤ C · max(D, n^{1-1/r} log n)`. -/
def NativeStrongMultiRefiners (q r : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Finset (Fin n)), ∀ D : ℝ,
    IsRGraph r X → MaxDegLE r X D → D ≤ n / C →
    ∃ (E : Type) (_ : DecidableEq E) (ends : E → Finset (Fin n)) (K Xl R : Finset E)
      (𝒲 : Finset (Finset E)) (B : ℕ),
      Xl.image ends = X ∧ (B : ℝ) ≤ C * max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n) ∧
      IsStrongMultiRefiner q r C ends K Xl R 𝒲 B

/-- `n^{1-1/r} log n = o(n)`, in the form needed for the degree budget. -/
theorem eventually_mul_rpow_log_le {r : ℕ} (hr : 1 ≤ r) (K : ℝ) (hK : 0 ≤ K) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
      K * ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n) ≤ n := by
  have hr' : (0 : ℝ) < 1 / (r : ℝ) := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  have hlo := isLittleO_log_rpow_atTop hr'
  have hε : (0 : ℝ) < 1 / (K + 1) := by positivity
  have hb := hlo.bound hε
  have hb' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hb
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1 hb'
  refine ⟨max n₁ 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_of_max_le_right hn)
  have hn0 : (0 : ℝ) < n := by linarith
  have h := hn₁ n (le_of_max_le_left hn)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg (by positivity)] at h
  have hsplit : (n : ℝ) ^ (1 - 1 / (r : ℝ)) * (n : ℝ) ^ (1 / (r : ℝ)) = n := by
    rw [← Real.rpow_add hn0]; simp
  have hpos : 0 ≤ (n : ℝ) ^ (1 - 1 / (r : ℝ)) := by positivity
  calc K * ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n)
      ≤ K * ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * (1 / (K + 1) * (n : ℝ) ^ (1 / (r : ℝ)))) := by
        gcongr
    _ = K / (K + 1) * ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * (n : ℝ) ^ (1 / (r : ℝ))) := by ring
    _ = K / (K + 1) * n := by rw [hsplit]
    _ ≤ 1 * n := by
        gcongr
        rw [div_le_one (by linarith)]; linarith
    _ = n := one_mul _

/-- **`RefinerAbsorbersFor q r` from the native construction.**  Both placements (fake edges
and absorbers) are proved; the only remaining input is `NativeStrongMultiRefiners q r`. -/
theorem refinerAbsorbersFor_of_native {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hnat : NativeStrongMultiRefiners q r) : RefinerAbsorbersFor q r := by
  obtain ⟨C, hC, n₀, hN⟩ := hnat
  obtain ⟨Cf, hCf, hasm⟩ := refinerAbsorbers_of_strongMultiRefiner hr hrq C hC
  obtain ⟨n₁, hn₁⟩ := eventually_mul_rpow_log_le (by omega : 1 ≤ r) ((Cf : ℝ) * C)
    (by positivity)
  set C₀ := Cf * C + C + Cf
  refine refinerAbsorbersFor_of_eventually (by omega : 1 ≤ r) C₀ (max (max n₀ n₁) 1)
    (by omega) ?_
  intro n hn X D hX hXD hDn
  have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ _) hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hC₀pos : (0 : ℝ) < C₀ := by positivity
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hCC₀ : (C : ℝ) ≤ C₀ := by exact_mod_cast (show C ≤ C₀ by omega)
  have hDn' : D ≤ n / C := hDn.trans (div_le_div_of_nonneg_left hnR.le hCpos hCC₀)
  obtain ⟨E, _, ends, K, Xl, R, 𝒲, B, hXl, hB, hS⟩ := hN n hn0 X D hX hXD hDn'
  set L := (n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n
  have hL0 : 0 ≤ L := mul_nonneg (by positivity) (Real.log_natCast_nonneg n)
  have hCfC : ((Cf * C : ℕ) : ℝ) ≤ C₀ := by exact_mod_cast (show Cf * C ≤ C₀ by omega)
  have hD1 : (Cf : ℝ) * C * D ≤ n := by
    rcases le_or_gt D 0 with hD0 | hD0
    · have : (Cf : ℝ) * C * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hD0
      linarith
    · calc (Cf : ℝ) * C * D ≤ C₀ * D := by
            apply mul_le_mul_of_nonneg_right _ hD0.le; exact_mod_cast hCfC
        _ ≤ C₀ * (n / C₀) := mul_le_mul_of_nonneg_left hDn hC₀pos.le
        _ = n := by field_simp
  have hL1 : (Cf : ℝ) * C * L ≤ n := hn₁ n hn1
  have hCfB : ((Cf * B : ℕ) : ℝ) ≤ n := by
    push_cast
    calc (Cf : ℝ) * B ≤ Cf * (C * max D L) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = max ((Cf : ℝ) * C * D) ((Cf : ℝ) * C * L) := by
          rw [← mul_assoc, mul_max_of_nonneg _ _ (by positivity)]
      _ ≤ n := max_le hD1 hL1
  have hCfB' : Cf * B ≤ n := by exact_mod_cast hCfB
  obtain ⟨R', 𝒲', A, Qon, Qoff, hR', hA, hdeg⟩ := hasm n ends K Xl R 𝒲 B hS hCfB' hnpos
  rw [hXl] at hR' hA
  refine ⟨R', 𝒲', A, Qon, Qoff, hR'.mono (by omega), hA, fun S hS' => ?_⟩
  have h := hdeg S (by omega)
  have hmax : 0 ≤ max D L := le_max_of_le_right hL0
  calc (deg (R' ∪ 𝒲'.sup A) S : ℝ) ≤ ((Cf * B : ℕ) : ℝ) := by exact_mod_cast h
    _ = Cf * B := by push_cast; ring
    _ ≤ Cf * (C * max D L) := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = ((Cf * C : ℕ) : ℝ) * max D L := by push_cast; ring
    _ ≤ C₀ * max D L := mul_le_mul_of_nonneg_right hCfC hmax

end RefinedAbsorption.Placement
