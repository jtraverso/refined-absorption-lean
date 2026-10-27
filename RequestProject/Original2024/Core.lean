module
public import RequestProject.Original2024.Defs
public import RequestProject.Original2024.HostAssembly

/-!
# The common core of Theorems 1.11 and 1.7 (uniformity `r ≥ 2`)

`hostCore`: for `q > r ≥ 2` there is `C ≥ 1` such that for every `r`-graph `X ⊆ K_n^r` with
`Δ(X) ≤ D ≤ n / C` and every *forbidden* `r`-graph `F` with `C · Δ(F) ≤ n`, there are a
`C`-refined refiner `R` of `X` with family `𝒲` (pieces with at most one `X`-edge and at most `C`
vertices) and attached absorbers `A W`, such that neither `R` nor any `A W` meets `F`, and
`Δ(R)`, `Δ(R ∪ ⋃ A W)` and the family degree are at most `C · max(D, n^{1-1/r} log n)`.

The proof composes the multi-refiner theorem (`General.nativeStrongMultiRefiners_all`, i.e. the
witness of Theorem 3.8, with its strong invariants) with `hostRefinerAbsorbers`.
-/

@[expose] public section

namespace RefinedAbsorption.Original2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Absorber17 RefinedAbsorption.Placement

/-- The data produced by `hostCore`. -/
structure HostWitness (q r C : ℕ) {n : ℕ} (X F : Finset (Finset (Fin n))) (M : ℝ)
    (R : Finset (Finset (Fin n))) (𝒲 : Finset (Finset (Finset (Fin n))))
    (A Qon Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n))) : Prop where
  refiner : IsRefinedRefiner q r C X R 𝒲
  oneX : ∀ W ∈ 𝒲, (W.filter (· ∈ X)).card ≤ 1
  vert_le : ∀ W ∈ 𝒲, (vertexSet W).card ≤ C
  avoidR : Disjoint R F
  absorbers : IsAttachedAbsorbers q r X R 𝒲 A Qon Qoff
  avoidA : ∀ W ∈ 𝒲, Disjoint (A W) F
  degR : MaxDegLE r R (C * M)
  degRA : MaxDegLE r (R ∪ 𝒲.sup A) (C * M)
  pieceDeg : ∀ S : Finset (Fin n), S.card + 1 = r →
    ((𝒲.filter fun W => S ⊆ vertexSet W).card : ℝ) ≤ C * M

theorem budget_nonneg (n r : ℕ) : 0 ≤ budget n r :=
  mul_nonneg (by positivity) (Real.log_natCast_nonneg n)

/-- The empty witness (for `X = ∅`). -/
theorem hostWitness_empty (q r C n : ℕ) (F : Finset (Finset (Fin n))) (M : ℝ) (hM : 0 ≤ M) :
    HostWitness q r C (∅ : Finset (Finset (Fin n))) F M ∅ ∅
      (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) := by
  obtain ⟨h1, h2, -⟩ := refinerAbsorbers_empty q r C n 0
  have hCM : (0 : ℝ) ≤ C * M := mul_nonneg (Nat.cast_nonneg _) hM
  refine ⟨h1, by simp, by simp, by simp, h2, by simp, fun S _ => ?_, fun S _ => ?_,
    fun S _ => ?_⟩
  · simpa [deg] using hCM
  · simpa [deg] using hCM
  · simpa using hCM

/-- **Core of Theorems 1.11 and 1.7, `r ≥ 2`.** -/
theorem hostCore {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (n : ℕ) (X F : Finset (Finset (Fin n))) (D : ℝ),
      IsRGraph r X → MaxDegLE r X D → D ≤ n / C →
      (∀ S : Finset (Fin n), S.card + 1 = r → C * deg F S ≤ n) →
      ∃ (R : Finset (Finset (Fin n))) (𝒲 : Finset (Finset (Finset (Fin n))))
        (A Qon Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
        HostWitness q r C X F (max D (budget n r)) R 𝒲 A Qon Qoff := by
  obtain ⟨C₁, hC₁, n₀, hN⟩ := General.nativeStrongMultiRefiners_all hr hrq
  obtain ⟨B₀, Cf, hCf, hasm⟩ := hostRefinerAbsorbers hr hrq C₁ hC₁
  obtain ⟨n₁, hn₁⟩ := eventually_mul_rpow_log_le (by omega : 1 ≤ r) (2 * (Cf : ℝ) * C₁)
    (by positivity)
  set C₀ := 2 * Cf * C₁ + 2 * Cf + r * Cf + Cf * C₁ + C₁ + n₀ + n₁ + 1 with hC₀
  refine ⟨C₀, by omega, ?_⟩
  intro n X F D hX hXD hDn hF
  have hC₀pos : (0 : ℝ) < C₀ := by positivity
  have hn0R : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set L := budget n r with hL
  have hL0 : 0 ≤ L := budget_nonneg n r
  have hM0 : 0 ≤ max D L := le_max_of_le_right hL0
  by_cases hsmall : n₀ ≤ n ∧ n₁ ≤ n ∧ 1 ≤ n
  · obtain ⟨hn0, hn1, hnpos⟩ := hsmall
    have hCC : (C₁ : ℝ) ≤ C₀ := by exact_mod_cast (show C₁ ≤ C₀ by omega)
    have hC₁pos : (0 : ℝ) < C₁ := by exact_mod_cast hC₁
    have hDn' : D ≤ n / C₁ := hDn.trans (div_le_div_of_nonneg_left hn0R hC₁pos hCC)
    obtain ⟨E, _, ends, K, Xl, R, 𝒲, B, hXl, hB, hS⟩ := hN n hn0 X D hX hXD hDn'
    -- `2 Cf B ≤ n`
    have hD1 : 2 * (Cf : ℝ) * C₁ * D ≤ n := by
      rcases le_or_gt D 0 with hD0 | hD0
      · have : 2 * (Cf : ℝ) * C₁ * D ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hD0
        linarith
      · have h2 : ((2 * Cf * C₁ : ℕ) : ℝ) ≤ C₀ := by exact_mod_cast (show 2 * Cf * C₁ ≤ C₀ by omega)
        calc 2 * (Cf : ℝ) * C₁ * D = ((2 * Cf * C₁ : ℕ) : ℝ) * D := by push_cast; ring
          _ ≤ C₀ * D := mul_le_mul_of_nonneg_right h2 hD0.le
          _ ≤ C₀ * (n / C₀) := mul_le_mul_of_nonneg_left hDn hC₀pos.le
          _ = n := by field_simp
    have hL1 : 2 * (Cf : ℝ) * C₁ * L ≤ n := hn₁ n hn1
    have h2B : ((2 * Cf * B : ℕ) : ℝ) ≤ n := by
      push_cast
      calc 2 * (Cf : ℝ) * B ≤ 2 * Cf * (C₁ * max D L) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
        _ = max (2 * (Cf : ℝ) * C₁ * D) (2 * (Cf : ℝ) * C₁ * L) := by
            rw [← mul_assoc, mul_max_of_nonneg _ _ (by positivity)]
        _ ≤ n := max_le hD1 hL1
    have h2B' : 2 * Cf * B ≤ n := by exact_mod_cast h2B
    have hCfB : Cf * B ≤ n := by nlinarith
    have hFdeg : ∀ S : Finset (Fin n), S.card = r - 1 → Cf * (B + deg F S) ≤ n := by
      intro S hS
      have h1 := hF S (by omega)
      have h2 : 2 * Cf * deg F S ≤ C₀ * deg F S := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    obtain ⟨R', 𝒲', A, Qon, Qoff, hS', hR'F, hA, hAF, -, hdeg⟩ :=
      hasm n ends K Xl R 𝒲 B F hS hCfB hFdeg hnpos
    rw [hXl] at hS' hA
    have hCfC : ((Cf * C₁ : ℕ) : ℝ) ≤ C₀ := by exact_mod_cast (show Cf * C₁ ≤ C₀ by omega)
    have hbound : ∀ x : ℕ, x ≤ Cf * B → (x : ℝ) ≤ C₀ * max D L := by
      intro x hx
      calc (x : ℝ) ≤ ((Cf * B : ℕ) : ℝ) := by exact_mod_cast hx
        _ = Cf * B := by push_cast; ring
        _ ≤ Cf * (C₁ * max D L) := mul_le_mul_of_nonneg_left hB (by positivity)
        _ = ((Cf * C₁ : ℕ) : ℝ) * max D L := by push_cast; ring
        _ ≤ C₀ * max D L := mul_le_mul_of_nonneg_right hCfC hM0
    have hR := hS'.refiner
    refine ⟨R', 𝒲', A, Qon, Qoff, ⟨hR.mono (by omega), hS'.oneX, fun W hW => ?_, hR'F, hA,
      hAF, fun S hS'' => hbound _ (hS'.degR S (by omega)),
      fun S hS'' => hbound _ (hdeg S (by omega)),
      fun S hS'' => hbound _ (hS'.pieceDeg S (by omega))⟩⟩
    refine (card_vertexSet_le (fun e he => hR.rgraph e (hR.subset W hW he))
      (hR.card_le W hW)).trans ?_
    omega
  · have hlt : n < C₀ := by
      rcases not_and_or.1 hsmall with h | h
      · omega
      · rcases not_and_or.1 h with h | h <;> omega
    have hltR : (n : ℝ) < C₀ := by exact_mod_cast hlt
    have hD1 : D < 1 := hDn.trans_lt ((div_lt_one hC₀pos).2 hltR)
    have hX0 := eq_empty_of_maxDegLE_lt_one (by omega) hX hXD hD1
    subst hX0
    exact ⟨_, _, _, _, _, hostWitness_empty q r C₀ n F _ hM0⟩

end RefinedAbsorption.Original2024
