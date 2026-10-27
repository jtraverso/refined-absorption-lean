module
public import RefinedAbsorption.Counting

/-!
# Designs and Steiner systems (Section 1.1)

A design with parameters `(n, q, r, λ)` is a set `𝒟` of `q`-subsets of an `n`-set such that
every `r`-subset lies in exactly `λ` members of `𝒟`; an `(n, q, r)`-Steiner system is the case
`λ = 1`.  We prove:

* an `(n, q, r)`-Steiner system is the same as a `K_q^r`-decomposition of `K_n^r`;
* the divisibility conditions `binom(q-i, r-i) ∣ λ · binom(n-i, r-i)` are necessary;
* the necessary direction of Kirkman's theorem: Steiner triple systems on `n ≥ 1` points
  only exist when `n ≡ 1, 3 (mod 6)`; together with the arithmetic fact that the divisibility
  conditions for `(q, r) = (3, 2)` are equivalent to `n ≡ 1, 3 (mod 6)`;
* the case `r = 1` (Section 6): an `(n, q, 1)`-Steiner system exists iff `q ∣ n`;
* the Fano plane is a Steiner triple system on `7` points.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A design with parameters `(|V|, q, r, l)`: a set of `q`-subsets of `V` such that every
`r`-subset of `V` lies in exactly `l` of them. -/
structure IsDesign (q r l : ℕ) (𝒟 : Finset (Finset V)) : Prop where
  card_eq : ∀ B ∈ 𝒟, B.card = q
  mult_eq : ∀ T : Finset V, T.card = r → cliqueMult 𝒟 T = l

/-- A `(|V|, q, r)`-Steiner system: every `r`-subset lies in exactly one block. -/
abbrev IsSteinerSystem (q r : ℕ) (𝒮 : Finset (Finset V)) : Prop := IsDesign q r 1 𝒮

/-- An `(n, q, r)`-Steiner system is exactly a `K_q^r`-decomposition of `K_n^r`. -/
theorem isSteinerSystem_iff_isDecomposition {q r : ℕ} {𝒮 : Finset (Finset V)} :
    IsSteinerSystem q r 𝒮 ↔ IsDecomposition q r (completeRGraph V r) 𝒮 := by
  constructor
  · intro h
    refine ⟨fun e he => (mem_powersetCard.1 he).2, h.card_eq, fun e he => ?_⟩
    rw [h.mult_eq e he, if_pos (show e ∈ completeRGraph V r from
      mem_powersetCard.2 ⟨subset_univ _, he⟩)]
  · intro h
    refine ⟨h.card_eq, fun T hT => ?_⟩
    rw [h.mult_eq T hT, if_pos (show T ∈ completeRGraph V r from
      mem_powersetCard.2 ⟨subset_univ _, hT⟩)]

/-- The divisibility conditions for designs with parameters `(n, q, r, l)`:
`binom(q-i, r-i) ∣ l · binom(n-i, r-i)` for all `0 ≤ i ≤ r-1`. -/
def DesignDivisibility (n q r l : ℕ) : Prop :=
  ∀ i < r, (q - i).choose (r - i) ∣ l * (n - i).choose (r - i)

/-- **Necessity of the divisibility conditions for designs.**  If a design with parameters
`(n, q, r, l)` exists on an `n`-set, then `binom(q-i, r-i) ∣ l · binom(n-i, r-i)` for all
`0 ≤ i ≤ r - 1`. -/
theorem IsDesign.designDivisibility {q r l : ℕ} {𝒟 : Finset (Finset V)}
    (h : IsDesign q r l 𝒟) : DesignDivisibility (Fintype.card V) q r l := by
  intro i hi
  by_cases hiV : i ≤ Fintype.card V
  · obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset V)) (by simpa using hiV)
    have key := sum_weight_double_count q r 𝒟 h.card_eq (fun _ => (1 : ℕ)) S (by omega)
    simp only [sum_const, smul_eq_mul, mul_one] at key
    have hl : ∑ e ∈ (univ.powersetCard r).filter (fun e => S ⊆ e),
        (𝒟.filter (fun Q => e ⊆ Q)).card = l * (Fintype.card V - i).choose (r - i) := by
      have hm : ∀ e ∈ (univ.powersetCard r).filter (fun e => S ⊆ e),
          (𝒟.filter (fun Q => e ⊆ Q)).card = l :=
        fun e he => h.mult_eq e (mem_powersetCard.1 (mem_filter.1 he).1).2
      rw [sum_congr rfl hm, sum_const, smul_eq_mul, mul_comm, card_powersetCard_filter_superset (subset_univ _)
        (by omega), card_univ, hS]
    rw [← hl, key, hS]
    exact Dvd.intro _ rfl
  · rw [show Fintype.card V - i = 0 by omega, Nat.choose_eq_zero_of_lt (show 0 < r - i by omega), mul_zero]
    exact dvd_zero _

/-- The divisibility conditions for Steiner triple systems are equivalent to
`n ≡ 1, 3 (mod 6)` (for `n ≥ 1`). -/
theorem designDivisibility_three_two_iff {n : ℕ} (hn : 1 ≤ n) :
    DesignDivisibility n 3 2 1 ↔ n % 6 = 1 ∨ n % 6 = 3 := by
  have h2 : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  constructor
  · intro h
    have h0 := h 0 (by norm_num)
    have h1 := h 1 (by norm_num)
    simp only [Nat.sub_zero, one_mul] at h0 h1
    norm_num at h0 h1
    have h3 : 3 ∣ n * (n - 1) := h2 ▸ Dvd.dvd.mul_left h0 2
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h3 | h3 <;> omega
  · intro h i hi
    interval_cases i
    · simp only [Nat.sub_zero, one_mul]
      norm_num
      have : 3 ∣ 2 * n.choose 2 := by
        rw [h2]
        rcases h with h | h
        · exact Dvd.dvd.mul_left (by omega) _
        · exact Dvd.dvd.mul_right (by omega) _
      exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
    · simp only [one_mul]
      norm_num
      omega

/-- **Kirkman's theorem, necessary direction.**  If there is a Steiner triple system on a
nonempty `n`-set, then `n ≡ 1` or `3 (mod 6)`. -/
theorem IsSteinerSystem.mod_six {𝒮 : Finset (Finset V)} (h : IsSteinerSystem 3 2 𝒮)
    (hV : 1 ≤ Fintype.card V) : Fintype.card V % 6 = 1 ∨ Fintype.card V % 6 = 3 :=
  (designDivisibility_three_two_iff hV).1 h.designDivisibility

/-- The Fano plane: a Steiner triple system on `7` points. -/
def fanoPlane : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

/-- The Fano plane is a `(7, 3, 2)`-Steiner system. -/
theorem fanoPlane_isSteinerSystem : IsSteinerSystem 3 2 fanoPlane :=
  ⟨by unfold fanoPlane; decide +kernel, by unfold cliqueMult fanoPlane; decide +kernel⟩

end RefinedAbsorption

namespace RefinedAbsorption

open Finset

/-- The blocks `{x : x / q = k}` (for `k < n / q`) of the trivial `(n, q, 1)`-Steiner system. -/
def trivialBlocks (n q : ℕ) : Finset (Finset (Fin n)) :=
  (range (n / q)).image (fun k => univ.filter (fun x : Fin n => x.val / q = k))

/-- **Steiner systems with `r = 1`.**  For `q ≥ 1`, an `(n, q, 1)`-Steiner system exists if
and only if `q ∣ n`. -/
theorem exists_steinerSystem_r_one_iff (n q : ℕ) (hq : 1 ≤ q) :
    (∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q 1 𝒮) ↔ q ∣ n := by
  constructor
  · rintro ⟨𝒮, h⟩
    have := h.designDivisibility 0 (by norm_num)
    simpa using this
  · intro hdvd
    have hdiv : ∀ x k : ℕ, x / q = k ↔ k * q ≤ x ∧ x < k * q + q := by
      intro x k
      rw [le_antisymm_iff, Nat.le_div_iff_mul_le (by omega), ← Nat.lt_succ_iff,
        Nat.div_lt_iff_lt_mul (by omega)]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, by rw [Nat.succ_mul] at h1; exact h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨by rw [Nat.succ_mul]; exact h2, h1⟩
    refine ⟨trivialBlocks n q, ⟨?_, ?_⟩⟩
    · intro B hB
      simp only [trivialBlocks, mem_image, mem_range] at hB
      obtain ⟨k, hk, rfl⟩ := hB
      have hkn : k * q + q ≤ n := by
        have h1 := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hk)
        rw [Nat.div_mul_cancel hdvd, Nat.succ_mul] at h1
        exact h1
      have : (univ.filter (fun x : Fin n => x.val / q = k)).map Fin.valEmbedding
          = Ico (k * q) (k * q + q) := by
        ext y
        simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact (hdiv _ _).1 hx
        · intro hy; exact ⟨⟨y, by omega⟩, (hdiv _ _).2 hy, rfl⟩
      rw [← card_map Fin.valEmbedding, this, Nat.card_Ico]; omega
    · intro T hT
      obtain ⟨x, rfl⟩ := card_eq_one.1 hT
      rw [cliqueMult, card_eq_one]
      refine ⟨univ.filter (fun y : Fin n => y.val / q = x.val / q), ?_⟩
      ext B
      simp only [trivialBlocks, mem_filter, mem_image, mem_range, singleton_subset_iff,
        mem_singleton]
      constructor
      · rintro ⟨⟨k, hk, rfl⟩, hx⟩
        simp only [mem_filter, mem_univ, true_and] at hx
        rw [hx]
      · rintro rfl
        exact ⟨⟨x.val / q, Nat.div_lt_div_of_lt_of_dvd hdvd x.2, rfl⟩, by simp⟩

end RefinedAbsorption
