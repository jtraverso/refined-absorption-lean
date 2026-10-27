module
public import RequestProject.GeneralEmbedding.Defs
public import Mathlib

/-!
# Counting lemmas for the General Embedding Lemma

* `card_fun_mem`: the number of maps `Fin m → Fin n` sending a set `B` into a set `T`;
* `mdeg_le`: lower-order degrees of a multi-`r`-graph from its `(r-1)`-degrees;
* `sum_card_filter_union_le`: a double count over the `b`-sets `T`;
* `Kseq`: the sequence of thresholds `K_0 = 0`, `K_{j+1} = Q (c + K_j)`.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

/-- The number of maps `Fin m → Fin n` sending `B` into `T`. -/
theorem card_fun_mem (m n : ℕ) (B : Finset (Fin m)) (T : Finset (Fin n)) :
    (univ.filter (fun f : Fin m → Fin n => ∀ i ∈ B, f i ∈ T)).card =
      T.card ^ B.card * n ^ (m - B.card) := by
  classical
  have h : univ.filter (fun f : Fin m → Fin n => ∀ i ∈ B, f i ∈ T) =
      Fintype.piFinset (fun i => if i ∈ B then T else univ) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hf i
      split_ifs with hi
      · exact hf i hi
      · exact mem_univ _
    · intro hf i hi
      have := hf i
      rwa [if_pos hi] at this
  rw [h, Fintype.card_piFinset]
  have h2 : ∀ i, (if i ∈ B then T else (univ : Finset (Fin n))).card =
      if i ∈ B then T.card else n := by
    intro i; split_ifs <;> simp
  simp_rw [h2]
  rw [prod_ite, prod_const, prod_const]
  congr 2
  · rw [filter_mem_eq_inter, univ_inter]
  · have : univ.filter (fun i : Fin m => i ∉ B) = Bᶜ := by ext; simp
    rw [this, card_compl, Fintype.card_fin]

/-- The number of `(r-1)`-sets containing a set `A` with `|A| ≤ r - 1`. -/
theorem card_supersets_le' {n : ℕ} (r : ℕ) (A : Finset (Fin n)) :
    ((univ.powersetCard (r - 1)).filter (fun S : Finset (Fin n) => A ⊆ S)).card ≤
      n ^ (r - 1 - A.card) := by
  classical
  have hinj : Set.InjOn (fun S : Finset (Fin n) => S \ A)
      (((univ.powersetCard (r - 1)).filter (fun S : Finset (Fin n) => A ⊆ S)) : Set _) := by
    intro S₁ h₁ S₂ h₂ heq
    simp only [coe_filter, Set.mem_setOf_eq] at h₁ h₂
    simp only at heq
    rw [← sdiff_union_of_subset h₁.2, ← sdiff_union_of_subset h₂.2, heq]
  have hmaps : ∀ S ∈ (univ.powersetCard (r - 1)).filter (fun S : Finset (Fin n) => A ⊆ S),
      S \ A ∈ (univ : Finset (Fin n)).powersetCard (r - 1 - A.card) := by
    intro S hS
    obtain ⟨hS1, hS2⟩ := mem_filter.1 hS
    rw [mem_powersetCard] at hS1 ⊢
    exact ⟨subset_univ _, by rw [card_sdiff_of_subset hS2, hS1.2]⟩
  calc _ ≤ ((univ : Finset (Fin n)).powersetCard (r - 1 - A.card)).card :=
        card_le_card_of_injOn _ (fun S hS => mem_coe.2 (hmaps S (mem_coe.1 hS))) hinj
    _ = n.choose (r - 1 - A.card) := by rw [card_powersetCard, card_univ, Fintype.card_fin]
    _ ≤ n ^ (r - 1 - A.card) := Nat.choose_le_pow _ _

/-- Lower-order degrees of a multi-`r`-graph: if every `(r-1)`-set lies in at most `D` edges,
then every set `A` with `|A| ≤ r - 1` lies in at most `n^{r-1-|A|} D` edges. -/
theorem mdeg_le {n r : ℕ} {ι : Type*} [Fintype ι] (ends : ι → Finset (Fin n))
    (hends : ∀ x, (ends x).card = r) {D : ℝ} (hD0 : 0 ≤ D)
    (hdeg : ∀ S : Finset (Fin n), S.card + 1 = r →
      ((univ.filter (fun x => S ⊆ ends x)).card : ℝ) ≤ D)
    (A : Finset (Fin n)) (hA : A.card + 1 ≤ r) :
    ((univ.filter (fun x => A ⊆ ends x)).card : ℝ) ≤ (n : ℝ) ^ (r - 1 - A.card) * D := by
  classical
  set 𝒮 := (univ.powersetCard (r - 1)).filter (fun S : Finset (Fin n) => A ⊆ S) with h𝒮
  have h1 : (univ.filter (fun x => A ⊆ ends x)).card ≤
      ∑ x ∈ univ.filter (fun x => A ⊆ ends x), (𝒮.filter (fun S => S ⊆ ends x)).card := by
    rw [card_eq_sum_ones (univ.filter (fun x => A ⊆ ends x))]
    refine sum_le_sum fun x hx => ?_
    obtain ⟨S, hAS, hSx, hSc⟩ := exists_subsuperset_card_eq (mem_filter.1 hx).2
      (show A.card ≤ r - 1 by omega) (by rw [hends x]; omega)
    exact card_pos.2 ⟨S, mem_filter.2 ⟨mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, hSc⟩,
      hAS⟩, hSx⟩⟩
  have h2 : ∑ x ∈ univ.filter (fun x => A ⊆ ends x), (𝒮.filter (fun S => S ⊆ ends x)).card =
      ∑ S ∈ 𝒮, (univ.filter (fun x => S ⊆ ends x)).card := by
    simp only [card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun S hS => ?_
    rw [sum_filter]
    refine sum_congr rfl fun x _ => ?_
    have hAS := (mem_filter.1 hS).2
    by_cases hx : S ⊆ ends x
    · simp [hx, hAS.trans hx]
    · simp [hx]
  have h3 : (∑ S ∈ 𝒮, ((univ.filter (fun x => S ⊆ ends x)).card : ℝ)) ≤ 𝒮.card * D := by
    calc (∑ S ∈ 𝒮, ((univ.filter (fun x => S ⊆ ends x)).card : ℝ)) ≤ ∑ S ∈ 𝒮, D := by
          refine sum_le_sum fun S hS => hdeg S ?_
          have := (mem_powersetCard.1 (mem_filter.1 hS).1).2
          omega
      _ = 𝒮.card * D := by rw [sum_const, nsmul_eq_mul]
  have h4 : (𝒮.card : ℝ) ≤ (n : ℝ) ^ (r - 1 - A.card) := by
    exact_mod_cast card_supersets_le' r A
  have h1' : ((univ.filter (fun x => A ⊆ ends x)).card : ℝ) ≤
      ∑ S ∈ 𝒮, ((univ.filter (fun x => S ⊆ ends x)).card : ℝ) := by
    have := h1.trans (le_of_eq h2)
    exact_mod_cast this
  calc _ ≤ _ := h1'
    _ ≤ 𝒮.card * D := h3
    _ ≤ (n : ℝ) ^ (r - 1 - A.card) * D := mul_le_mul_of_nonneg_right h4 hD0

/-- Double counting over the `b`-sets `T`. -/
theorem sum_card_filter_union_le {n : ℕ} {β : Type*} (P : Finset β) (g : β → Finset (Fin n))
    (r : ℕ) (hg : ∀ p ∈ P, (g p).card ≤ r) (A' : Finset (Fin n)) (b : ℕ) :
    ∑ T ∈ (univ : Finset (Fin n)).powersetCard b, (P.filter (fun p => A' ∪ T ⊆ g p)).card ≤
      2 ^ r * (P.filter (fun p => A' ⊆ g p)).card := by
  classical
  calc ∑ T ∈ (univ : Finset (Fin n)).powersetCard b, (P.filter (fun p => A' ∪ T ⊆ g p)).card
      = ∑ p ∈ P, (((univ : Finset (Fin n)).powersetCard b).filter
          (fun T => A' ∪ T ⊆ g p)).card := by
        simp only [card_filter]
        exact sum_comm
    _ ≤ ∑ p ∈ P, if A' ⊆ g p then 2 ^ r else 0 := by
        refine sum_le_sum fun p hp => ?_
        split_ifs with hA
        · calc _ ≤ (g p).powerset.card := by
                refine card_le_card fun T hT => ?_
                exact mem_powerset.2 (subset_union_right.trans (mem_filter.1 hT).2)
            _ = 2 ^ (g p).card := card_powerset _
            _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (hg p hp)
        · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
          intro T _ hT
          exact hA (subset_union_left.trans hT)
    _ = 2 ^ r * (P.filter (fun p => A' ⊆ g p)).card := by
        rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]

/-- The thresholds `K_0 = 0`, `K_{j+1} = Q (c + K_j)`. -/
noncomputable def Kseq (Q c : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => Q * (c + Kseq Q c j)

theorem Kseq_nonneg {Q c : ℝ} (hQ : 0 ≤ Q) (hc : 0 ≤ c) : ∀ j, 0 ≤ Kseq Q c j
  | 0 => le_rfl
  | j + 1 => mul_nonneg hQ (add_nonneg hc (Kseq_nonneg hQ hc j))

theorem Kseq_mono {Q c : ℝ} (hQ : 1 ≤ Q) (hc : 0 ≤ c) : Monotone (Kseq Q c) := by
  refine monotone_nat_of_le_succ fun j => ?_
  show Kseq Q c j ≤ Q * (c + Kseq Q c j)
  have := Kseq_nonneg (Q := Q) (c := c) (by linarith) hc j
  nlinarith

theorem Kseq_succ_ge {Q c : ℝ} (hQ : 1 ≤ Q) (hc : 0 ≤ c) (j : ℕ) : Q * c ≤ Kseq Q c (j + 1) := by
  show Q * c ≤ Q * (c + Kseq Q c j)
  have := Kseq_nonneg (Q := Q) (c := c) (by linarith) hc j
  nlinarith

end RefinedAbsorption
