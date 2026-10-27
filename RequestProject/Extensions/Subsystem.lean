module
public import RequestProject.Extensions.Embedding
public import RequestProject.Extensions.CountCore

/-!
# Steiner systems with prescribed subsystems (Doyen–Wilson type)

For `q > r ≥ 2` there are `ε > 0` and `n₀` such that whenever `n, m ≥ n₀` both satisfy the
divisibility conditions and `m ≤ ε n`, there is an `(n, q, r)`-Steiner system containing an
`(m, q, r)`-Steiner subsystem: a set `W` of `m` points such that the block through every
`r`-subset of `W` lies inside `W`.  Moreover the subsystem can be prescribed: **every**
`(m, q, r)`-Steiner system placed on any `m` of the `n` points extends
(`steiner_extends_subsystem`).

For Steiner triple systems the exact statement (every `n ≥ 2m + 1` admissible) is the
Doyen–Wilson theorem; here the result holds for all `q > r ≥ 2` in the range `m ≤ ε n`.
-/

@[expose] public section

namespace RefinedAbsorption.Extensions

open Finset RefinedAbsorption.Original2024

/-- `W` spans a subsystem of `𝒮`: the block through every `r`-subset of `W` lies inside `W`. -/
def IsSubsystemOn {n : ℕ} (r : ℕ) (𝒮 : Finset (Finset (Fin n))) (W : Finset (Fin n)) : Prop :=
  ∀ T ⊆ W, T.card = r → ∃ Q ∈ 𝒮, T ⊆ Q ∧ Q ⊆ W

/-- **Every small Steiner system extends.**  For `q > r ≥ 1` there are `ε > 0` and `n₀` such
that for every admissible `n ≥ n₀`, every `m ≤ ε n`, every injection `f : Fin m ↪ Fin n` and
every `(m, q, r)`-Steiner system `𝒯`, some `(n, q, r)`-Steiner system contains the image of
every block of `𝒯`; the image `W` of `f` then spans a subsystem. -/
theorem steiner_extends_subsystem {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∀ m : ℕ, (m : ℝ) ≤ ε * n → ∀ (f : Fin m ↪ Fin n) (𝒯 : Finset (Finset (Fin m))),
        IsSteinerSystem q r 𝒯 →
        ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮 ∧
          (∀ Q ∈ 𝒯, Q.map f ∈ 𝒮) ∧ IsSubsystemOn r 𝒮 (univ.map f) := by
  obtain ⟨ε, hε, n₀, hcomp⟩ := partialSteiner_completion (q := q) hr hrq
  refine ⟨ε, hε, n₀, fun n hn hdiv m hm f 𝒯 h𝒯 => ?_⟩
  set P := 𝒯.map (mapEmbedding f).toEmbedding
  have hP : IsPartialSteinerSystem q r P := (Extensions.IsSteinerSystem.isPartial h𝒯).map f
  have hdeg : MaxDegLE r (coveredEdges r P) (ε * n) := by
    intro S hS
    have h1 : deg (coveredEdges r P) S ≤ (univ.map f).card := by
      refine deg_le_card_of_edges_subset (fun e he => ?_) hS
      obtain ⟨Q, hQ, he⟩ := mem_biUnion.1 he
      obtain ⟨Q', -, rfl⟩ := mem_map.1 hQ
      refine ⟨(mem_powersetCard.1 he).1.trans ?_, (mem_powersetCard.1 he).2⟩
      intro x hx
      simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact mem_map_of_mem _ (mem_univ a)
    rw [card_map, card_univ, Fintype.card_fin] at h1
    exact le_trans (by exact_mod_cast h1) hm
  obtain ⟨𝒮, hP𝒮, h𝒮⟩ := hcomp n hn hdiv P hP hdeg
  refine ⟨𝒮, h𝒮, fun Q hQ => hP𝒮 (mem_map_of_mem _ hQ), fun T hTW hT => ?_⟩
  classical
  let T' : Finset (Fin m) := univ.filter (fun a => f a ∈ T)
  have hTT' : T'.map f = T := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, T']
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hx
      obtain ⟨a, -, rfl⟩ := mem_map.1 (hTW hx)
      exact ⟨a, hx, rfl⟩
  have hT'c : T'.card = r := by rw [← hT, ← hTT', card_map]
  have hm1 := h𝒯.mult_eq T' hT'c
  obtain ⟨Q', hQ'⟩ := card_pos.1 (show 0 < cliqueMult 𝒯 T' by omega)
  obtain ⟨hQ'𝒯, hTQ'⟩ := mem_filter.1 hQ'
  refine ⟨Q'.map f, hP𝒮 (mem_map_of_mem _ hQ'𝒯), ?_, map_subset_map.2 (subset_univ _)⟩
  rw [← hTT']
  exact map_subset_map.2 hTQ'

/-- **Steiner systems with Steiner subsystems.**  For `q > r ≥ 2` there are `ε > 0` and `n₀`
such that for all admissible `n, m ≥ n₀` with `m ≤ ε n` there is an `(n, q, r)`-Steiner system
with an `(m, q, r)`-Steiner subsystem on some set `W` of `m` points. -/
theorem steiner_with_subsystem {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀, (m : ℝ) ≤ ε * n →
      DesignDivisibility n q r 1 → DesignDivisibility m q r 1 →
      ∃ (𝒮 : Finset (Finset (Fin n))) (W : Finset (Fin n)),
        IsSteinerSystem q r 𝒮 ∧ W.card = m ∧ IsSubsystemOn r 𝒮 W := by
  obtain ⟨ε, hε, n₁, hext⟩ := steiner_extends_subsystem (q := q) (by omega) hrq
  obtain ⟨n₂, hex⟩ := theorem_1_1_steiner q r hr hrq
  refine ⟨min ε 1, by positivity, max n₁ n₂, fun n hn m hm hmn hdivn hdivm => ?_⟩
  have hmn' : m ≤ n := by
    have : (m : ℝ) ≤ n := le_trans hmn (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [min_le_right ε 1])
    exact_mod_cast this
  obtain ⟨𝒯, h𝒯⟩ := hex m (le_of_max_le_right hm) hdivm
  obtain ⟨𝒮, h𝒮, -, hsub⟩ := hext n (le_of_max_le_left hn) hdivn m
    (le_trans hmn (by nlinarith [min_le_left ε 1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
    (Fin.castLEEmb hmn') 𝒯 h𝒯
  exact ⟨𝒮, univ.map (Fin.castLEEmb hmn'), h𝒮, by simp, hsub⟩

end RefinedAbsorption.Extensions
