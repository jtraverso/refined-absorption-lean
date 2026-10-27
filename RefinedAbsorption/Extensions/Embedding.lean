module
public import RefinedAbsorption.Extensions.Completion

/-!
# Finite embedding theorem for partial Steiner systems

Every finite partial Steiner system `P` with parameters `(q, r)` (on any finite set of points)
can be embedded in an `(N, q, r)`-Steiner system, and in fact in one for **every** sufficiently
large `N` satisfying the divisibility conditions.  For Steiner triple systems this is Treash's
theorem (1971); for general `q > r` it follows here from the completion theorem
`partialSteiner_completion`, since a fixed partial system placed inside `N` points has
`(r-1)`-degrees bounded by its number of points, which is at most `ε N` for large `N`.

We also show that the divisibility conditions hold for infinitely many `N`
(`exists_designDivisibility_ge`), so that the embedding exists unconditionally
(`partialSteiner_embeds`).
-/

@[expose] public section

namespace RefinedAbsorption.Extensions

open Finset RefinedAbsorption.Original2024

/-! ### Admissible orders exist in every arithmetic progression `q + t·M` -/

theorem dvd_choose_of_factorial_dvd {c a j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (ha : c * k.factorial ∣ a) : c ∣ a.choose j := by
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; exact dvd_zero _
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have key := Nat.add_one_mul_choose_eq b i
  have h1 : c * (i + 1) ∣ (b + 1).choose (i + 1) * (i + 1) := by
    rw [← key]
    exact dvd_mul_of_dvd_left
      (dvd_trans (Nat.mul_dvd_mul_left c (Nat.dvd_factorial (by omega) hjk)) ha) _
  rw [mul_comm ((b + 1).choose (i + 1)), mul_comm c] at h1
  exact Nat.dvd_of_mul_dvd_mul_left (by omega) h1

/-- If `c ∣ binom(x, k)` and `c · k! ∣ a` then `c ∣ binom(x + a, k)`. -/
theorem dvd_choose_add {c x a k : ℕ} (hx : c ∣ x.choose k) (ha : c * k.factorial ∣ a) :
    c ∣ (x + a).choose k := by
  rw [Nat.add_choose_eq]
  refine Finset.dvd_sum fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rcases Nat.eq_zero_or_pos ij.2 with h0 | hpos
  · have : ij.1 = k := by omega
    rw [this]; exact dvd_mul_of_dvd_left hx _
  · exact dvd_mul_of_dvd_right (dvd_choose_of_factorial_dvd hpos (by omega) ha) _

/-- The modulus of the admissible progression. -/
def admModulus (q r : ℕ) : ℕ := r.factorial * ∏ i ∈ range r, (q - i).choose (r - i)

/-- Every `N = q + t · admModulus q r` satisfies the divisibility conditions. -/
theorem designDivisibility_progression {q r : ℕ} (hrq : r < q) (t : ℕ) :
    DesignDivisibility (q + t * admModulus q r) q r 1 := by
  intro i hi
  rw [one_mul, show q + t * admModulus q r - i = (q - i) + t * admModulus q r by omega]
  refine dvd_choose_add dvd_rfl (Dvd.dvd.mul_left ?_ t)
  unfold admModulus
  rw [mul_comm r.factorial]
  exact Nat.mul_dvd_mul (dvd_prod_of_mem _ (mem_range.2 hi))
    (Nat.factorial_dvd_factorial (by omega))

/-- **Admissible orders are unbounded.** -/
theorem exists_designDivisibility_ge {q r : ℕ} (hrq : r < q) (M : ℕ) :
    ∃ N ≥ M, DesignDivisibility N q r 1 := by
  have hpos : 0 < admModulus q r := by
    unfold admModulus
    refine Nat.mul_pos (Nat.factorial_pos _) (prod_pos fun i hi => Nat.choose_pos ?_)
    have := mem_range.1 hi; omega
  refine ⟨q + M * admModulus q r, ?_, designDivisibility_progression hrq M⟩
  nlinarith

/-! ### Degrees of graphs living on a small vertex set -/

/-- If all edges of the `r`-graph `H` lie inside `U`, every `(r-1)`-set has degree at most
`|U|` in `H`. -/
theorem deg_le_card_of_edges_subset {V : Type*} [DecidableEq V] {r : ℕ}
    {H : Finset (Finset V)} {U : Finset V} (hH : ∀ e ∈ H, e ⊆ U ∧ e.card = r)
    {S : Finset V} (hS : S.card + 1 = r) : deg H S ≤ U.card := by
  rw [deg, show U.card = (U.powersetCard 1).card by rw [card_powersetCard, Nat.choose_one_right]]
  refine card_le_card_of_injOn (fun e => e \ S) ?_ ?_
  · intro e he
    rw [mem_coe, mem_filter] at he
    rw [mem_coe, mem_powersetCard]
    refine ⟨sdiff_subset.trans (hH e he.1).1, ?_⟩
    rw [card_sdiff_of_subset he.2, (hH e he.1).2]; omega
  · intro e he f hf hef
    rw [mem_coe, mem_filter] at he hf
    simp only at hef
    rw [← sdiff_union_of_subset he.2, ← sdiff_union_of_subset hf.2, hef]

/-! ### The embedding theorem -/

/-- The image of a partial Steiner system under an injective map is a partial Steiner system. -/
theorem IsPartialSteinerSystem.map {q r : ℕ} {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Fintype α] {P : Finset (Finset α)} (hP : IsPartialSteinerSystem q r P) (f : α ↪ β) :
    IsPartialSteinerSystem q r (P.map (mapEmbedding f).toEmbedding) := by
  classical
  refine ⟨fun Q hQ => ?_, fun T hT => ?_⟩
  · obtain ⟨Q', hQ', rfl⟩ := mem_map.1 hQ
    rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, card_map, hP.1 Q' hQ']
  · let T' : Finset α := univ.filter (fun a => f a ∈ T)
    have hsub : (P.map (mapEmbedding f).toEmbedding).filter (fun Q => T ⊆ Q) ⊆
        (P.filter (fun Q => T' ⊆ Q)).map (mapEmbedding f).toEmbedding := by
      intro Q hQ
      obtain ⟨hQ1, hTQ⟩ := mem_filter.1 hQ
      obtain ⟨Q', hQ', rfl⟩ := mem_map.1 hQ1
      refine mem_map.2 ⟨Q', mem_filter.2 ⟨hQ', fun a ha => ?_⟩, rfl⟩
      have ha' : f a ∈ T := (mem_filter.1 ha).2
      have := hTQ ha'
      simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, mem_map] at this
      obtain ⟨b, hb, hfb⟩ := this
      rwa [← f.injective hfb]
    by_cases hTim : T ⊆ univ.map f
    · have hT'c : T'.card = r := by
        rw [← hT]
        have : T'.map f = T := by
          ext x
          simp only [mem_map, mem_filter, mem_univ, true_and, T']
          constructor
          · rintro ⟨a, ha, rfl⟩; exact ha
          · intro hx
            obtain ⟨a, -, rfl⟩ := mem_map.1 (hTim hx)
            exact ⟨a, hx, rfl⟩
        rw [← this, card_map]
      have := hP.2 T' hT'c
      unfold cliqueMult at this ⊢
      exact (card_le_card hsub).trans (by rw [card_map]; exact this)
    · unfold cliqueMult
      rw [card_eq_zero.2]
      · exact Nat.zero_le _
      refine filter_eq_empty_iff.2 fun Q hQ hTQ => hTim ?_
      obtain ⟨Q', -, rfl⟩ := mem_map.1 hQ
      refine hTQ.trans ?_
      intro x hx
      simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact mem_map_of_mem _ (mem_univ a)

/-- **Finite embedding theorem for partial Steiner systems.**  Let `q > r ≥ 1` and let `P` be a
partial Steiner system on a finite set `α`.  Then for every sufficiently large `N` satisfying
the divisibility conditions for `(N, q, r)`-Steiner systems, there is an injection `f : α ↪ Fin N`
and an `(N, q, r)`-Steiner system containing the image of every block of `P`. -/
theorem partialSteiner_embedding {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) {α : Type*}
    [Fintype α] [DecidableEq α] (P : Finset (Finset α)) (hP : IsPartialSteinerSystem q r P) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, DesignDivisibility N q r 1 →
      ∃ (f : α ↪ Fin N) (𝒮 : Finset (Finset (Fin N))),
        IsSteinerSystem q r 𝒮 ∧ ∀ Q ∈ P, Q.map f ∈ 𝒮 := by
  obtain ⟨ε, hε, n₀, hcomp⟩ := partialSteiner_completion (q := q) hr hrq
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt ((Fintype.card α : ℝ) / ε)
  refine ⟨max n₀ (max N₁ (Fintype.card α)), fun N hN hdiv => ?_⟩
  have hαN : Fintype.card α ≤ N := le_trans (le_max_right _ _) (le_of_max_le_right hN)
  let f : α ↪ Fin N := (Fintype.equivFin α).toEmbedding.trans (Fin.castLEEmb hαN)
  set P' := P.map (mapEmbedding f).toEmbedding
  have hP' : IsPartialSteinerSystem q r P' := hP.map f
  have hdeg : MaxDegLE r (coveredEdges r P') (ε * N) := by
    intro S hS
    have h1 : deg (coveredEdges r P') S ≤ (univ.map f).card := by
      refine deg_le_card_of_edges_subset (fun e he => ?_) hS
      obtain ⟨Q, hQ, he⟩ := mem_biUnion.1 he
      obtain ⟨Q', -, rfl⟩ := mem_map.1 hQ
      refine ⟨(mem_powersetCard.1 he).1.trans ?_, (mem_powersetCard.1 he).2⟩
      intro x hx
      simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact mem_map_of_mem _ (mem_univ a)
    rw [card_map, card_univ] at h1
    have h2 : (Fintype.card α : ℝ) ≤ ε * N := by
      have hN1 : (N₁ : ℝ) ≤ N := by
        exact_mod_cast le_trans (le_max_left _ _) (le_of_max_le_right hN)
      have := (div_lt_iff₀ hε).1 (lt_of_lt_of_le hN₁ hN1)
      linarith
    exact le_trans (by exact_mod_cast h1) h2
  obtain ⟨𝒮, hP'𝒮, h𝒮⟩ := hcomp N (le_of_max_le_left hN) hdiv P' hP' hdeg
  exact ⟨f, 𝒮, h𝒮, fun Q hQ => hP'𝒮 (mem_map_of_mem _ hQ)⟩

/-- **Every finite partial Steiner system embeds in a finite Steiner system.** -/
theorem partialSteiner_embeds {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) {α : Type*}
    [Fintype α] [DecidableEq α] (P : Finset (Finset α)) (hP : IsPartialSteinerSystem q r P) :
    ∃ (N : ℕ) (f : α ↪ Fin N) (𝒮 : Finset (Finset (Fin N))),
      IsSteinerSystem q r 𝒮 ∧ ∀ Q ∈ P, Q.map f ∈ 𝒮 := by
  obtain ⟨N₀, h⟩ := partialSteiner_embedding hr hrq P hP
  obtain ⟨N, hN, hdiv⟩ := exists_designDivisibility_ge hrq N₀
  obtain ⟨f, 𝒮, h1, h2⟩ := h N hN hdiv
  exact ⟨N, f, 𝒮, h1, h2⟩

end RefinedAbsorption.Extensions
