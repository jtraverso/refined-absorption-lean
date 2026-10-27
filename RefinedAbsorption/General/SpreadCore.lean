module
public import RefinedAbsorption.General.PermCount
public import RefinedAbsorption.General.GenSpread
public import RefinedAbsorption.Sharp.Descent

/-!
# Spreading set systems by independent random permutations

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Lemma 4.1 (Claim 4.1.1 and
the Chernoff bound).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

Every tag `T` (an `i`-set outside `Zo`) carries a system of sets `A T a ⊆ Z₁ ∪ P₀`, `a ∈ I T`;
the systems are moved by independent permutations `σ T` of the new vertices `P₀` (fixing `Z₁`).
**`exists_perm_spread`**: there are permutations such that every `(r-1)`-set `S` (`r = i + k`)
lies in `T ∪ σ_T (A T a)` for few pairs `(T, a)` altogether, provided the systems satisfy the
local conditions of the flat local refiners:

* `(k-1)`-sets lie in at most `D` sets of a system, and sets of size `≥ k` in at most `μ`;
* a `z`-set inside `Z₁` (`z ≤ k - 1`) lies in at most `D (c p)^(k-1-z)` sets of a system;
* `k`-sets inside `Z₁` are covered at most `b₃ |Ut|^(i-1-|J|)` times over the tags containing a
  given set `J`, and larger sets inside `Z₁` are never covered (small trace).
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.Sharp

variable {n : ℕ}

/-- Tags of size `i` inside `Ut` containing a given set. -/
theorem card_tags_containing_le (𝒯 : Finset (Finset (Fin n))) (Ut : Finset (Fin n)) {i : ℕ}
    (h𝒯 : ∀ T ∈ 𝒯, T ⊆ Ut ∧ T.card = i) (J : Finset (Fin n)) (hJ : J.card ≤ i) :
    (𝒯.filter fun T => J ⊆ T).card ≤ Ut.card ^ (i - J.card) := by
  classical
  refine le_trans ?_ ((Nat.choose_le_pow _ _).trans (le_of_eq rfl))
  rw [← card_powersetCard]
  refine card_le_card_of_injOn (fun T => T \ J) (fun T hT => ?_) ?_
  · obtain ⟨hT𝒯, hJT⟩ := mem_filter.1 hT
    obtain ⟨hTU, hTc⟩ := h𝒯 T hT𝒯
    refine mem_powersetCard.2 ⟨sdiff_subset.trans hTU, ?_⟩
    rw [card_sdiff_of_subset hJT, hTc]
  · intro T₁ h₁ T₂ h₂ heq
    have e₁ := sdiff_union_of_subset (mem_filter.1 h₁).2
    have e₂ := sdiff_union_of_subset (mem_filter.1 h₂).2
    simp only at heq
    rw [← e₁, ← e₂, heq]

/-- A set of fixed vertices covered by a moved set is covered by the set itself. -/
theorem subset_of_subset_image_perm {P₀ Z₁ : Finset (Fin n)} (hd : Disjoint Z₁ P₀)
    (σ : PermOn P₀) {A S : Finset (Fin n)} (hSZ : S ⊆ Z₁) (hS : S ⊆ A.image σ.1) : S ⊆ A := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := mem_image.1 (hS hx)
  have hxP : x ∉ P₀ := disjoint_left.1 hd (hSZ hx)
  have hyP : y ∉ P₀ := fun h => hxP (hyx ▸ permOn_mem σ h)
  rw [σ.2 y hyP] at hyx
  rw [← hyx]; exact hy

/-- Covering by a moved set is covering of the preimage. -/
theorem subset_image_perm_iff (σ : Equiv.Perm (Fin n)) (A S : Finset (Fin n)) :
    S ⊆ A.image σ ↔ S.image σ.symm ⊆ A := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    obtain ⟨z, hz, hzy⟩ := mem_image.1 (h hy)
    rw [← hzy, Equiv.symm_apply_apply]; exact hz
  · intro h x hx
    exact mem_image.2 ⟨σ.symm x, h (mem_image_of_mem _ hx), σ.apply_symm_apply x⟩

theorem card_image_perm (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    (S.image σ).card = S.card := card_image_of_injective _ σ.injective

/-- The logarithm of the number of events is dominated by the sharp cost. -/
theorem log_le_sharpCost {r c m N : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (hN : N ≤ (c * m) ^ (r - 1)) :
    Real.log ((N : ℝ) + 1) ≤ ((r : ℝ) * (c + 1)) * sharpCost r m := by
  set L := Nat.log 2 m with hL
  have hmL : m + 1 ≤ 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
  have hc : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
  have h1 : c * m + 1 ≤ 2 ^ (c + (L + 1)) := by
    rw [pow_add]
    calc c * m + 1 ≤ (c + 1) * (m + 1) := by nlinarith
      _ ≤ 2 ^ c * 2 ^ (L + 1) := Nat.mul_le_mul hc hmL
  have h2 : N + 1 ≤ 2 ^ ((c + (L + 1)) * (r - 1) + 1) := by
    rw [pow_succ, pow_mul]
    calc N + 1 ≤ (c * m) ^ (r - 1) + 1 := by omega
      _ ≤ (c * m + 1) ^ (r - 1) * 2 := by
          have : (c * m) ^ (r - 1) ≤ (c * m + 1) ^ (r - 1) := Nat.pow_le_pow_left (by omega) _
          have h1' : 1 ≤ (c * m + 1) ^ (r - 1) := Nat.one_le_pow _ _ (by omega)
          omega
      _ ≤ (2 ^ (c + (L + 1))) ^ (r - 1) * 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h1 _)
  have h3 : ((N : ℝ) + 1) ≤ (2 : ℝ) ^ ((c + (L + 1)) * (r - 1) + 1) := by exact_mod_cast h2
  have hcost : (L : ℝ) + 1 ≤ sharpCost r m := by
    have : L + 1 ≤ sharpCost r m := by
      unfold sharpCost
      exact Nat.le_mul_of_pos_left _ (RefinedAbsorption.Window.one_le_winCost r hm)
    exact_mod_cast this
  have hkey : (c + (L + 1)) * (r - 1) + 1 ≤ r * (c + 1) * (L + 1) := by
    have h0 : (c + (L + 1)) * (r - 1) + 1 ≤ (c + (L + 1)) * r := by
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp only [Nat.add_sub_cancel, mul_add, mul_one]; omega
    have : c + (L + 1) ≤ (c + 1) * (L + 1) := by nlinarith
    calc (c + (L + 1)) * (r - 1) + 1 ≤ (c + (L + 1)) * r := h0
      _ ≤ (c + 1) * (L + 1) * r := Nat.mul_le_mul_right _ this
      _ = r * (c + 1) * (L + 1) := by ring
  have hkeyR : (((c + (L + 1)) * (r - 1) + 1 : ℕ) : ℝ) ≤ (r : ℝ) * (c + 1) * ((L : ℝ) + 1) := by
    exact_mod_cast hkey
  calc Real.log ((N : ℝ) + 1) ≤ Real.log ((2 : ℝ) ^ ((c + (L + 1)) * (r - 1) + 1)) :=
        Real.log_le_log (by positivity) h3
    _ = ((c + (L + 1)) * (r - 1) + 1 : ℕ) * Real.log 2 := by rw [Real.log_pow]
    _ ≤ ((c + (L + 1)) * (r - 1) + 1 : ℕ) := by
        have := Real.log_two_lt_d9
        have h0 : (0 : ℝ) ≤ ((c + (L + 1)) * (r - 1) + 1 : ℕ) := Nat.cast_nonneg _
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    _ ≤ ((r : ℝ) * (c + 1)) * sharpCost r m := by
        refine hkeyR.trans ?_
        exact mul_le_mul_of_nonneg_left hcost (by positivity)

/-- A moved set stays inside `Z₁ ∪ P₀`. -/
theorem image_perm_subset {P₀ Z₁ : Finset (Fin n)} (σ : PermOn P₀) {A : Finset (Fin n)}
    (hA : A ⊆ Z₁ ∪ P₀) : A.image σ.1 ⊆ Z₁ ∪ P₀ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
  by_cases hyP : y ∈ P₀
  · exact mem_union_right _ (permOn_mem σ hyP)
  · rw [σ.2 y hyP]; exact hA hy

/-- **The mean over the permutations, for one system.** -/
theorem sum_perm_cover_le (P₀ Z₁ : Finset (Fin n)) {κ : Type*}
    (I : Finset κ) (A : κ → Finset (Fin n)) {s : ℕ} (hs : ∀ a ∈ I, (A a).card ≤ s)
    (Sin : Finset (Fin n)) :
    (∑ σ : PermOn P₀, (I.filter fun a => Sin ∩ Z₁ ⊆ A a ∧ Sin ∩ P₀ ⊆ (A a).image σ.1).card) *
        (P₀.card - (Sin ∩ P₀).card + 1) ^ (Sin ∩ P₀).card ≤
      (I.filter fun a => Sin ∩ Z₁ ⊆ A a).card * s ^ (Sin ∩ P₀).card *
        Fintype.card (PermOn P₀) := by
  classical
  have hswap : (∑ σ : PermOn P₀, (I.filter fun a => Sin ∩ Z₁ ⊆ A a ∧
      Sin ∩ P₀ ⊆ (A a).image σ.1).card) =
      ∑ a ∈ I.filter (fun a => Sin ∩ Z₁ ⊆ A a),
        (univ.filter fun σ : PermOn P₀ => Sin ∩ P₀ ⊆ (A a).image σ.1).card := by
    simp only [card_filter]
    rw [sum_comm, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases h : Sin ∩ Z₁ ⊆ A a
    · simp [h]
    · simp [h]
  rw [hswap, sum_mul]
  calc ∑ a ∈ I.filter (fun a => Sin ∩ Z₁ ⊆ A a),
        (univ.filter fun σ : PermOn P₀ => Sin ∩ P₀ ⊆ (A a).image σ.1).card *
          (P₀.card - (Sin ∩ P₀).card + 1) ^ (Sin ∩ P₀).card
      ≤ ∑ _a ∈ I.filter (fun a => Sin ∩ Z₁ ⊆ A a),
          s ^ (Sin ∩ P₀).card * Fintype.card (PermOn P₀) := by
        refine sum_le_sum fun a ha => ?_
        refine (card_perm_cover_mul_le P₀ (Sin ∩ P₀) (A a) inter_subset_right).trans ?_
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (hs a (mem_filter.1 ha).1) _)
    _ = _ := by rw [sum_const, smul_eq_mul, mul_assoc]

/-- The `(p - t + 1)^t` factor dominates `(p/2)^t`. -/
theorem pow_le_two_pow_mul {p t : ℕ} (hpt : 2 * t ≤ p) (c : ℕ) :
    (c * p) ^ t ≤ (2 * c) ^ t * (p - t + 1) ^ t := by
  rw [← mul_pow]
  apply Nat.pow_le_pow_left
  calc c * p ≤ c * (2 * (p - t + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * c * (p - t + 1) := by ring

end RefinedAbsorption.General
