module
public import RequestProject.OmniFromRefiner

/-!
# Reductions for `RefinerWithAbsorbers`

Independent structural facts about the (still unproved) input `RefinerWithAbsorbers`:

* `refinerWithAbsorbers_iff_pairs`: the statement is the conjunction of its instances
  `RefinerAbsorbersFor q r` (definitional; the original `Prop` is unchanged);
* `IsRefinedRefiner.mono`: refinedness is monotone in the constant;
* `isAttachedAbsorbers_of_isAbsorber`: absorbers in the sense of Definition 1.5, pairwise
  edge-disjoint and edge-disjoint from `X ∪ R`, are attached absorbers;
* `isAttachedAbsorbers_empty`: if every member of the family already has a
  `K_q^r`-decomposition, empty absorbers can be attached;
* `refinerAbsorbersFor_of_eventually`: it suffices to construct refiners for all large `n`
  (small `n` force `X = ∅`, which is handled by the empty refiner).
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {V : Type*} [DecidableEq V]

/-- The instance of `RefinerWithAbsorbers` for a fixed pair `(q, r)`. -/
def RefinerAbsorbersFor (q r : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, ∀ X : Finset (Finset (Fin n)),
    ∀ D : ℝ, IsRGraph r X → MaxDegLE r X D → D ≤ n / C →
      ∃ (R : Finset (Finset (Fin n))) (𝒲 : Finset (Finset (Finset (Fin n))))
        (A Qon Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
        IsRefinedRefiner q r C X R 𝒲 ∧ IsAttachedAbsorbers q r X R 𝒲 A Qon Qoff ∧
          MaxDegLE r (R ∪ 𝒲.sup A) (C * max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n))

theorem refinerWithAbsorbers_iff_pairs :
    RefinerWithAbsorbers ↔ ∀ q r : ℕ, 1 ≤ r → r < q → RefinerAbsorbersFor q r :=
  Iff.rfl

/-- A `C`-refined refiner is `C'`-refined for every `C' ≥ C`. -/
theorem IsRefinedRefiner.mono {q r C C' : ℕ} {X R : Finset (Finset V)}
    {𝒲 : Finset (Finset (Finset V))} (h : IsRefinedRefiner q r C X R 𝒲) (hC : C ≤ C') :
    IsRefinedRefiner q r C' X R 𝒲 :=
  { rgraph := h.rgraph
    disjoint := h.disjoint
    divisible := h.divisible
    subset := h.subset
    card_le := fun W hW => (h.card_le W hW).trans hC
    mult_le := fun e he => (h.mult_le e he).trans hC
    decomp := h.decomp }

/-- Absorbers in the sense of Definition 1.5 for the members of the family, pairwise
edge-disjoint and edge-disjoint from `X ∪ R`, give attached absorbers. -/
theorem isAttachedAbsorbers_of_isAbsorber {q r : ℕ} {X R : Finset (Finset V)}
    {𝒲 : Finset (Finset (Finset V))} (A : Finset (Finset V) → Finset (Finset V))
    (hrg : ∀ W ∈ 𝒲, IsRGraph r (A W))
    (habs : ∀ W ∈ 𝒲, IsAbsorber q r W (A W))
    (hdisj : ∀ W ∈ 𝒲, Disjoint (A W) (X ∪ R))
    (hpair : ∀ W ∈ 𝒲, ∀ W' ∈ 𝒲, W ≠ W' → Disjoint (A W) (A W')) :
    ∃ Qon Qoff : Finset (Finset V) → Finset (Finset V),
      IsAttachedAbsorbers q r X R 𝒲 A Qon Qoff := by
  classical
  have hon : ∀ W, ∃ Q : Finset (Finset V), W ∈ 𝒲 → IsDecomposition q r (A W ∪ W) Q := by
    intro W
    by_cases hW : W ∈ 𝒲
    · obtain ⟨Q, hQ⟩ := (habs W hW).decomp_union
      exact ⟨Q, fun _ => hQ⟩
    · exact ⟨∅, fun h => absurd h hW⟩
  have hoff : ∀ W, ∃ Q : Finset (Finset V), W ∈ 𝒲 → IsDecomposition q r (A W) Q := by
    intro W
    by_cases hW : W ∈ 𝒲
    · obtain ⟨Q, hQ⟩ := (habs W hW).decomp
      exact ⟨Q, fun _ => hQ⟩
    · exact ⟨∅, fun h => absurd h hW⟩
  choose Qon hQon using hon
  choose Qoff hQoff using hoff
  exact ⟨Qon, Qoff, hrg, hdisj, hpair, fun W hW => hQon W hW, fun W hW => hQoff W hW⟩

/-- If every member of the family already has a `K_q^r`-decomposition, the empty absorbers are
attached absorbers. -/
theorem isAttachedAbsorbers_empty {q r : ℕ} {X R : Finset (Finset V)}
    {𝒲 : Finset (Finset (Finset V))} (hdec : ∀ W ∈ 𝒲, HasDecomposition q r W) :
    ∃ Qon : Finset (Finset V) → Finset (Finset V),
      IsAttachedAbsorbers q r X R 𝒲 (fun _ => ∅) Qon (fun _ => ∅) := by
  classical
  have h : ∀ W, ∃ Q : Finset (Finset V), W ∈ 𝒲 → IsDecomposition q r W Q := by
    intro W
    by_cases hW : W ∈ 𝒲
    · obtain ⟨Q, hQ⟩ := hdec W hW
      exact ⟨Q, fun _ => hQ⟩
    · exact ⟨∅, fun h => absurd h hW⟩
  choose Q hQ using h
  refine ⟨Q, fun _ _ e he => by simp at he, fun _ _ => disjoint_empty_left _,
    fun _ _ _ _ _ => disjoint_empty_left _, fun W hW => ?_, fun _ _ => ?_⟩
  · simpa using hQ W hW
  · exact ⟨fun e he => by simp at he, fun Q hQ => by simp at hQ,
      fun e _ => by simp [cliqueMult]⟩

/-- An `r`-graph (`r ≥ 1`) with maximum `(r-1)`-degree `< 1` is empty. -/
theorem eq_empty_of_maxDegLE_lt_one {n r : ℕ} (hr : 1 ≤ r) {X : Finset (Finset (Fin n))}
    {D : ℝ} (hX : IsRGraph r X) (hXD : MaxDegLE r X D) (hD : D < 1) : X = ∅ := by
  by_contra hne
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.2 hne
  obtain ⟨S, hSe, hS⟩ := Finset.exists_subset_card_eq (s := e) (n := r - 1)
    (by rw [hX e he]; omega)
  have h1 : 1 ≤ deg X S :=
    Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨he, hSe⟩⟩
  have h2 := hXD S (by omega)
  have : (1 : ℝ) ≤ deg X S := by exact_mod_cast h1
  linarith

/-- The empty refiner with no absorbers works for `X = ∅`. -/
theorem refinerAbsorbers_empty (q r C n : ℕ) (D : ℝ) :
    IsRefinedRefiner q r C (∅ : Finset (Finset (Fin n))) ∅ ∅ ∧
      IsAttachedAbsorbers q r (∅ : Finset (Finset (Fin n))) ∅ ∅
        (fun _ => ∅) (fun _ => ∅) (fun _ => ∅) ∧
      MaxDegLE r ((∅ : Finset (Finset (Fin n))) ∪ (∅ : Finset (Finset (Finset (Fin n)))).sup
        (fun _ => ∅)) (C * max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n)) := by
  refine ⟨⟨by simp [IsRGraph], by simp, by simp, by simp, by simp, by simp, ?_⟩,
    ⟨by simp, by simp, by simp, by simp, by simp⟩, ?_⟩
  · intro L hL _
    rw [Finset.subset_empty] at hL
    subst hL
    exact ⟨∅, by simp, by simp, by simp⟩
  · intro S _
    have hM : 0 ≤ max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n) :=
      le_max_of_le_right (mul_nonneg (by positivity) (Real.log_natCast_nonneg n))
    have h0 : deg ((∅ : Finset (Finset (Fin n))) ∪ (∅ : Finset (Finset (Finset (Fin n)))).sup
        (fun _ => ∅)) S = 0 := by simp [deg]
    rw [h0, Nat.cast_zero]
    positivity

/-- **It suffices to build refiners with absorbers for all large `n`.**  If some constant `C`
works for all `n ≥ n₀`, then `max C n₀ + 1` works for all `n` (for smaller `n` the degree bound
`D ≤ n / C'` forces `D < 1`, hence `X = ∅`). -/
theorem refinerAbsorbersFor_of_eventually {q r : ℕ} (hr : 1 ≤ r) (C n₀ : ℕ) (hC : 1 ≤ C)
    (h : ∀ n : ℕ, n₀ ≤ n → ∀ X : Finset (Finset (Fin n)),
      ∀ D : ℝ, IsRGraph r X → MaxDegLE r X D → D ≤ n / C →
        ∃ (R : Finset (Finset (Fin n))) (𝒲 : Finset (Finset (Finset (Fin n))))
          (A Qon Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
          IsRefinedRefiner q r C X R 𝒲 ∧ IsAttachedAbsorbers q r X R 𝒲 A Qon Qoff ∧
            MaxDegLE r (R ∪ 𝒲.sup A) (C * max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n))) :
    RefinerAbsorbersFor q r := by
  set C' := max C n₀ + 1 with hC'
  refine ⟨C', by omega, fun n X D hX hXD hDn => ?_⟩
  have hC'pos : (0 : ℝ) < C' := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hn : n₀ ≤ n
  · have hCC' : (C : ℝ) ≤ C' := by exact_mod_cast (show C ≤ C' by omega)
    have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
    have hDn' : D ≤ n / C := hDn.trans (div_le_div_of_nonneg_left hn0 hCpos hCC')
    obtain ⟨R, 𝒲, A, Qon, Qoff, hR, hA, hdeg⟩ := h n hn X D hX hXD hDn'
    refine ⟨R, 𝒲, A, Qon, Qoff, hR.mono (by omega), hA, fun S hS => (hdeg S hS).trans ?_⟩
    have hM : 0 ≤ max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n) :=
      le_max_of_le_right (mul_nonneg (by positivity) (Real.log_natCast_nonneg n))
    exact mul_le_mul_of_nonneg_right hCC' hM
  · have hlt : (n : ℝ) < C' := by exact_mod_cast (show n < C' by omega)
    have hD1 : D < 1 := hDn.trans_lt ((div_lt_one hC'pos).2 hlt)
    have hX0 := eq_empty_of_maxDegLE_lt_one hr hX hXD hD1
    subst hX0
    exact ⟨∅, ∅, _, _, _, refinerAbsorbers_empty q r C' n D⟩

end RefinedAbsorption
