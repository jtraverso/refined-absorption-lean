module
public import RequestProject.General.SpreadCore

/-!
# Spreading tagged set systems by independent random permutations

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Lemma 4.1 (Claim 4.1.1 and
the Chernoff bound).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

Every tag `T` (an `i`-set outside `Z₁ ∪ P₀`) carries a system of sets `A T a ⊆ Z₁ ∪ P₀`,
`a ∈ I T`; the systems are moved by independent permutations `σ T` of the new vertices `P₀`.
**`exists_perm_spread`**: if `(k-1)`-sets lie in at most `Δ` sets of a system, `k`-sets in at most
`μ`, and the summed covering counts of sets `J ∪ Q` (`J` in the tag, `Q ⊆ Z₁`) are
`≤ c₀ (c₁ |P₀|)^(r-1-|J|-|Q|) D`, then some choice of permutations covers every `(r-1)`-set
`S ⊆ T ∪ σ_T (A T a)` for at most `Δ + 2 c₀ (2 c₁ s + 1)^r D + μ r (c+1) sharpCost r m` pairs.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.Sharp

variable {n : ℕ}

/-- Vertices outside `P₀` are fixed. -/
theorem image_perm_of_disjoint {P₀ B : Finset (Fin n)} (σ : PermOn P₀) (hB : Disjoint B P₀) :
    B.image σ.1 = B := by
  conv_rhs => rw [← image_id (s := B)]
  exact image_congr fun x hx => σ.2 x (disjoint_left.1 hB hx)

/-- Splitting a covering by a tag and a moved set. -/
theorem cover_split {P₀ Z₁ T A e : Finset (Fin n)} (hd : Disjoint Z₁ P₀) (σ : PermOn P₀)
    (hA : A ⊆ Z₁ ∪ P₀) (hT : Disjoint T (Z₁ ∪ P₀)) (h : e ⊆ T ∪ A.image σ.1) :
    e \ (Z₁ ∪ P₀) ⊆ T ∧ e ∩ Z₁ ⊆ A ∧ e ∩ (Z₁ ∪ P₀) ⊆ A.image σ.1 := by
  have himg := image_perm_subset σ hA
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨hxe, hxZ⟩ := mem_sdiff.1 hx
    rcases mem_union.1 (h hxe) with h' | h'
    · exact h'
    · exact absurd (himg h') hxZ
  · obtain ⟨hxe, hxZ⟩ := mem_inter.1 hx
    rcases mem_union.1 (h hxe) with h' | h'
    · exact absurd (mem_union_left _ hxZ) (disjoint_left.1 hT h')
    · obtain ⟨y, hy, hyx⟩ := mem_image.1 h'
      by_cases hyP : y ∈ P₀
      · have := permOn_mem σ hyP
        rw [hyx] at this
        exact absurd this (disjoint_left.1 hd hxZ)
      · rw [σ.2 y hyP] at hyx; rw [← hyx]; exact hy
  · obtain ⟨hxe, hxZ⟩ := mem_inter.1 hx
    rcases mem_union.1 (h hxe) with h' | h'
    · exact absurd hxZ (disjoint_left.1 hT h')
    · exact h'

set_option maxHeartbeats 1600000 in
/-- **Spreading tagged set systems** (see the module docstring). -/
theorem exists_perm_spread {i k r : ℕ} (hr : r = i + k) (hk : 1 ≤ k) {P₀ Z₁ Ut : Finset (Fin n)}
    (hd : Disjoint Z₁ P₀) {ι : Type*} [Fintype ι] [DecidableEq ι] (tag : ι → Finset (Fin n))
    (htinj : Function.Injective tag) (htU : ∀ T, tag T ⊆ Ut) (htc : ∀ T, (tag T).card = i)
    (htZ : ∀ T, Disjoint (tag T) (Z₁ ∪ P₀)) {κ : ι → Type*} (I : ∀ T, Finset (κ T))
    (A : ∀ T, κ T → Finset (Fin n)) (hA : ∀ T, ∀ a ∈ I T, A T a ⊆ Z₁ ∪ P₀)
    {s Δ μ c₀ c₁ D c m : ℕ} (hs : ∀ T, ∀ a ∈ I T, (A T a).card ≤ s)
    (hΔ : ∀ T (U : Finset (Fin n)), U.card = k - 1 → ((I T).filter fun a => U ⊆ A T a).card ≤ Δ)
    (hμ : ∀ T (U : Finset (Fin n)), U.card = k → ((I T).filter fun a => U ⊆ A T a).card ≤ μ)
    (hμ1 : 1 ≤ μ)
    (hmean : ∀ J Q : Finset (Fin n), Q ⊆ Z₁ → J.card + Q.card ≤ r - 1 →
      ∑ T, ((I T).filter fun a => J ⊆ tag T ∧ Q ⊆ A T a ∧ (A T a).Nonempty).card ≤
        c₀ * (c₁ * P₀.card) ^ (r - 1 - J.card - Q.card) * D)
    (hp : 2 * r ≤ P₀.card) (hm : 1 ≤ m) (hU : (Ut ∪ (Z₁ ∪ P₀)).card ≤ c * m) :
    ∃ σ : ι → PermOn P₀, ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T, ((I T).filter fun a => S ⊆ tag T ∪ (A T a).image (σ T).1).card ≤
        Δ + 2 * (c₀ * (2 * c₁ * s + 1) ^ r * D) + μ * (r * (c + 1)) * sharpCost r m := by
  classical
  haveI : Nonempty (PermOn P₀) := ⟨⟨1, fun _ _ => rfl⟩⟩
  set Zo := Z₁ ∪ P₀ with hZo
  set p := P₀.card with hp_def
  set ev := ((Ut ∪ Zo).powersetCard (r - 1)).filter fun e => k ≤ (e ∩ Zo).card with hev
  set X : Finset (Fin n) → ι → PermOn P₀ → ℕ := fun e T σ =>
    ((I T).filter fun a => e ⊆ tag T ∪ (A T a).image σ.1).card with hX
  set Mn : ℝ := ((c₀ * (2 * c₁ * s + 1) ^ r * D : ℕ) : ℝ) with hMn
  -- a single count is at most `μ`
  have hXb : ∀ e ∈ ev, ∀ T σ, X e T σ ≤ μ := by
    intro e he T σ
    obtain ⟨U, hUe, hUc⟩ := exists_subset_card_eq (mem_filter.1 he).2
    refine le_trans (card_le_card fun a ha => ?_) (hμ T (U.image σ.1.symm)
      (by rw [card_image_perm, hUc]))
    obtain ⟨haI, hcov⟩ := mem_filter.1 ha
    refine mem_filter.2 ⟨haI, ?_⟩
    rw [← subset_image_perm_iff]
    exact hUe.trans (cover_split hd σ (hA T a haI) (htZ T) hcov).2.2
  -- the means
  have hM : ∀ e ∈ ev, ∑ T, (∑ σ, (X e T σ : ℝ)) / Fintype.card (PermOn P₀) ≤ Mn := by
    intro e he
    obtain ⟨heP, hek⟩ := mem_filter.1 he
    obtain ⟨-, hec⟩ := mem_powersetCard.1 heP
    set J := e \ Zo with hJ
    set Q := e ∩ Z₁ with hQ
    set t := (e ∩ P₀).card with ht
    have hsplit : e ∩ Zo = Q ∪ (e ∩ P₀) := by rw [hZo, inter_union_distrib_left]
    have hdisQ : Disjoint Q (e ∩ P₀) :=
      disjoint_of_subset_left inter_subset_right (disjoint_of_subset_right inter_subset_right hd)
    have hcard : J.card + Q.card + t = r - 1 := by
      have h1 := card_sdiff_add_card_inter e Zo
      rw [← hJ, hsplit, card_union_of_disjoint hdisQ] at h1
      omega
    have hne : (e ∩ Zo).Nonempty := card_pos.1 (lt_of_lt_of_le hk hek)
    set N : ι → ℕ := fun T =>
      ((I T).filter fun a => J ⊆ tag T ∧ Q ⊆ A T a ∧ (A T a).Nonempty).card with hN
    have hT : ∀ T, (∑ σ, X e T σ) * (p - t + 1) ^ t ≤ N T * s ^ t * Fintype.card (PermOn P₀) := by
      intro T
      set I' := (I T).filter fun a => J ⊆ tag T ∧ (A T a).Nonempty with hI'
      have h1 : ∑ σ, X e T σ ≤ ∑ σ : PermOn P₀,
          (I'.filter fun a => e ∩ Z₁ ⊆ A T a ∧ e ∩ P₀ ⊆ (A T a).image σ.1).card := by
        refine sum_le_sum fun σ _ => card_le_card fun a ha => ?_
        obtain ⟨haI, hcov⟩ := mem_filter.1 ha
        obtain ⟨h1, h2, h3⟩ := cover_split hd σ (hA T a haI) (htZ T) hcov
        obtain ⟨x, hx⟩ := hne
        obtain ⟨y, hy, -⟩ := mem_image.1 (h3 hx)
        refine mem_filter.2 ⟨mem_filter.2 ⟨haI, h1, ⟨y, hy⟩⟩, h2, ?_⟩
        exact (inter_subset_inter_left (subset_union_right)).trans h3
      have h2 := sum_perm_cover_le P₀ Z₁ I' (A T) (s := s)
        (fun a ha => hs T a (mem_filter.1 ha).1) e
      have h3 : (I'.filter fun a => e ∩ Z₁ ⊆ A T a).card = N T := by
        rw [hI', filter_filter]
        refine congrArg card (filter_congr fun a _ => ?_)
        tauto
      rw [h3] at h2
      exact (Nat.mul_le_mul_right _ h1).trans h2
    have hsum : (∑ T, ∑ σ, X e T σ) * (p - t + 1) ^ t ≤
        (∑ T, N T) * s ^ t * Fintype.card (PermOn P₀) := by
      rw [sum_mul, sum_mul, sum_mul]
      exact sum_le_sum fun T _ => hT T
    have hmean' : ∑ T, N T ≤ c₀ * (c₁ * p) ^ t * D := by
      have := hmean J Q inter_subset_right (by omega)
      rwa [show r - 1 - J.card - Q.card = t by omega] at this
    have htr : t ≤ r := by omega
    have hpow : (c₁ * p) ^ t * s ^ t ≤ (2 * c₁ * s + 1) ^ r * (p - t + 1) ^ t := by
      rw [← mul_pow, show c₁ * p * s = (c₁ * s) * p by ring]
      refine (pow_le_two_pow_mul (by omega) (c₁ * s)).trans (Nat.mul_le_mul_right _ ?_)
      calc (2 * (c₁ * s)) ^ t ≤ (2 * c₁ * s + 1) ^ t :=
            Nat.pow_le_pow_left (by rw [mul_assoc]; omega) _
        _ ≤ (2 * c₁ * s + 1) ^ r := Nat.pow_le_pow_right (by omega) htr
    have hfin : ∑ T, ∑ σ, X e T σ ≤ c₀ * (2 * c₁ * s + 1) ^ r * D * Fintype.card (PermOn P₀) := by
      have hpos : 0 < (p - t + 1) ^ t := by positivity
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      calc (∑ T, ∑ σ, X e T σ) * (p - t + 1) ^ t
          ≤ (∑ T, N T) * s ^ t * Fintype.card (PermOn P₀) := hsum
        _ ≤ c₀ * (c₁ * p) ^ t * D * s ^ t * Fintype.card (PermOn P₀) := by
            gcongr
        _ = c₀ * D * Fintype.card (PermOn P₀) * ((c₁ * p) ^ t * s ^ t) := by ring
        _ ≤ c₀ * D * Fintype.card (PermOn P₀) * ((2 * c₁ * s + 1) ^ r * (p - t + 1) ^ t) :=
            Nat.mul_le_mul_left _ hpow
        _ = _ := by ring
    have hΩ : (0 : ℝ) < Fintype.card (PermOn P₀) := by exact_mod_cast Fintype.card_pos
    rw [← sum_div, div_le_iff₀ hΩ, hMn]
    have : ((∑ T, ∑ σ, X e T σ : ℕ) : ℝ) ≤
        ((c₀ * (2 * c₁ * s + 1) ^ r * D * Fintype.card (PermOn P₀) : ℕ) : ℝ) := by
      exact_mod_cast hfin
    push_cast at this ⊢
    linarith
  obtain ⟨σ, hσ⟩ := exists_spread_choice ev X hμ1 hXb (fun _ => Mn) hM
  have hlog : Real.log ((ev.card : ℝ) + 1) ≤ ((r : ℝ) * (c + 1)) * sharpCost r m := by
    refine log_le_sharpCost (by omega) hm ?_
    refine (card_filter_le _ _).trans ?_
    rw [card_powersetCard]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hU _)
  refine ⟨σ, fun S hS => ?_⟩
  by_cases hSU : S ⊆ Ut ∪ Zo
  · by_cases hSk : k ≤ (S ∩ Zo).card
    · have hSev : S ∈ ev := mem_filter.2 ⟨mem_powersetCard.2 ⟨hSU, hS⟩, hSk⟩
      have h1 := hσ S hSev
      have he3 : Real.exp 1 - 1 ≤ 2 := by linarith [Real.exp_one_lt_d9]
      have hMn0 : (0 : ℝ) ≤ Mn := Nat.cast_nonneg _
      have hμ0 : (0 : ℝ) ≤ μ := Nat.cast_nonneg _
      have h2 : ((∑ T, X S T (σ T) : ℕ) : ℝ) ≤
          2 * Mn + μ * (((r : ℝ) * (c + 1)) * sharpCost r m) := by
        nlinarith [mul_le_mul_of_nonneg_left hlog hμ0, mul_le_mul_of_nonneg_right he3 hMn0]
      have h3 : ((∑ T, X S T (σ T) : ℕ) : ℝ) ≤
          ((Δ + 2 * (c₀ * (2 * c₁ * s + 1) ^ r * D) + μ * (r * (c + 1)) * sharpCost r m : ℕ) : ℝ) := by
        push_cast
        rw [hMn] at h2
        push_cast at h2
        nlinarith [(Nat.cast_nonneg Δ : (0 : ℝ) ≤ Δ)]
      exact_mod_cast h3
    · push_neg at hSk
      set J := S \ Zo with hJ
      have hJc : i ≤ J.card := by
        have := card_sdiff_add_card_inter S Zo
        rw [← hJ] at this
        omega
      have hterm : ∀ T, ((I T).filter fun a => S ⊆ tag T ∪ (A T a).image (σ T).1).card ≤
          if tag T = J then Δ else 0 := by
        intro T
        split_ifs with hTJ
        · have hSZc : (S ∩ Zo).card = k - 1 := by
            have := card_sdiff_add_card_inter S Zo
            rw [← hJ] at this
            have h2 : J.card = i := by rw [← hTJ, htc]
            omega
          refine le_trans (card_le_card fun a ha => ?_) (hΔ T ((S ∩ Zo).image (σ T).1.symm)
            (by rw [card_image_perm, hSZc]))
          obtain ⟨haI, hcov⟩ := mem_filter.1 ha
          refine mem_filter.2 ⟨haI, ?_⟩
          rw [← subset_image_perm_iff]
          exact (cover_split hd (σ T) (hA T a haI) (htZ T) hcov).2.2
        · refine le_of_eq (card_eq_zero.2 (filter_eq_empty_iff.2 fun a ha hcov => hTJ ?_))
          have h1 := (cover_split hd (σ T) (hA T a ha) (htZ T) hcov).1
          exact (eq_of_subset_of_card_le h1 (by rw [htc]; exact hJc)).symm
      refine (sum_le_sum fun T _ => hterm T).trans ?_
      rw [← sum_filter, sum_const, smul_eq_mul]
      have hone : (univ.filter fun T => tag T = J).card ≤ 1 :=
        card_le_one.2 fun T hT T' hT' => htinj ((mem_filter.1 hT).2.trans (mem_filter.1 hT').2.symm)
      calc (univ.filter fun T => tag T = J).card * Δ ≤ 1 * Δ := Nat.mul_le_mul_right _ hone
        _ ≤ _ := by omega
  · obtain ⟨x, hxS, hxU⟩ := not_subset.1 hSU
    have h0 : ∀ T, ((I T).filter fun a => S ⊆ tag T ∪ (A T a).image (σ T).1).card = 0 := by
      intro T
      refine card_eq_zero.2 (filter_eq_empty_iff.2 fun a ha hcov => hxU ?_)
      rcases mem_union.1 (hcov hxS) with h' | h'
      · exact mem_union_left _ (htU T h')
      · exact mem_union_right _ (image_perm_subset (σ T) (hA T a ha) h')
    rw [sum_congr rfl fun T _ => h0 T, sum_const_zero]
    exact Nat.zero_le _

end RefinedAbsorption.General
