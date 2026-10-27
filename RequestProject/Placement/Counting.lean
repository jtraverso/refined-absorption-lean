module
public import RequestProject.Placement.Defs

/-!
# Counting lemmas for the Partial Clique Embedding Lemma
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset

variable {n h : ℕ}

theorem card_template_le {r k : ℕ} {R : Finset (Fin n)} {T : Finset (Finset (Fin n ⊕ Fin h))}
    (hw : GadgetWF r k R T) : T.card ≤ 2 ^ (k + h) := by
  have hsub : T ⊆ (R.map Function.Embedding.inl ∪ (univ : Finset (Fin h)).map
      Function.Embedding.inr).powerset := by
    intro t ht
    rw [mem_powerset]
    intro x hx
    rcases x with a | p
    · exact mem_union_left _ (mem_map_of_mem _ (hw.edge_roots t ht a hx))
    · exact mem_union_right _ (mem_map_of_mem _ (mem_univ p))
  calc T.card ≤ _ := card_le_card hsub
    _ = 2 ^ (R.map Function.Embedding.inl ∪ (univ : Finset (Fin h)).map
          Function.Embedding.inr).card := card_powerset _
    _ ≤ 2 ^ (k + h) := by
        apply Nat.pow_le_pow_right (by norm_num)
        calc _ ≤ (R.map Function.Embedding.inl).card +
              ((univ : Finset (Fin h)).map Function.Embedding.inr).card := card_union_le _ _
          _ ≤ k + h := by simp [hw.roots_le]

theorem placeEdge_subset {r k : ℕ} {R : Finset (Fin n)} {T : Finset (Finset (Fin n ⊕ Fin h))}
    (hw : GadgetWF r k R T) (φ : Fin h → Fin n) {t} (ht : t ∈ T) :
    placeEdge φ t ⊆ R ∪ auxImage φ := by
  intro x hx
  simp only [placeEdge, mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rcases y with a | p
  · exact mem_union_left _ (hw.edge_roots t ht a hy)
  · exact mem_union_right _ (mem_image_of_mem _ (mem_univ p))

/-- `emb φ` is injective on a template edge when `φ` is injective on the auxiliary vertices of
the edge (given by `A`) and avoids the roots. -/
theorem emb_injOn {R : Finset (Fin n)} (φ : Fin h → Fin n) (A : Finset (Fin h))
    (hinj : Set.InjOn φ A) (hR : ∀ p ∈ A, φ p ∉ R) (s : Finset (Fin n ⊕ Fin h))
    (hsR : ∀ a, Sum.inl a ∈ s → a ∈ R) (hsA : ∀ p, Sum.inr p ∈ s → p ∈ A) :
    Set.InjOn (emb φ) s := by
  intro x hx y hy hxy
  rcases x with a | p <;> rcases y with b | p'
  · simpa [emb] using hxy
  · exfalso; simp only [emb, Sum.elim_inl, Sum.elim_inr] at hxy
    exact hR p' (hsA p' hy) (hxy ▸ hsR a hx)
  · exfalso; simp only [emb, Sum.elim_inl, Sum.elim_inr] at hxy
    exact hR p (hsA p hx) (hxy ▸ hsR b hy)
  · simp only [emb, Sum.elim_inr] at hxy
    rw [hinj (hsA p hx) (hsA p' hy) hxy]

/-- **Root incidence.**  If every `(r-1)`-set lies in at most `D` root sets and all root sets
have at least `r-1` vertices, a `j`-set `J` (`j ≤ r - 1`) lies in at most `D · n^(r-1-j)` root
sets. -/
theorem rootIncidence {ι : Type*} {r : ℕ} (I : Finset ι) (R : ι → Finset (Fin n)) (D : ℕ)
    (hR : ∀ i ∈ I, r - 1 ≤ (R i).card)
    (hD : ∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ R i).card ≤ D)
    (J : Finset (Fin n)) (hJ : J.card ≤ r - 1) :
    (I.filter fun i => J ⊆ R i).card ≤ D * n ^ (r - 1 - J.card) := by
  classical
  set 𝒮 := ((univ : Finset (Fin n)).powersetCard (r - 1)).filter (fun S => J ⊆ S)
  have hsub : (I.filter fun i => J ⊆ R i) ⊆ 𝒮.biUnion (fun S => I.filter fun i => S ⊆ R i) := by
    intro i hi
    rw [mem_filter] at hi
    obtain ⟨S, hJS, hSR, hS⟩ := exists_subsuperset_card_eq hi.2 hJ (hR i hi.1)
    rw [mem_biUnion]
    exact ⟨S, by simp [𝒮, hS, hJS], mem_filter.2 ⟨hi.1, hSR⟩⟩
  have h𝒮 : 𝒮.card ≤ n ^ (r - 1 - J.card) := by
    have : 𝒮.card ≤ ((univ : Finset (Fin n)).powersetCard (r - 1 - J.card)).card := by
      apply card_le_card_of_injOn (fun S => S \ J)
      · intro S hS
        simp only [𝒮, coe_filter, mem_powersetCard, Set.mem_setOf_eq] at hS
        rw [mem_coe, mem_powersetCard]
        exact ⟨subset_univ _, by rw [card_sdiff_of_subset hS.2, hS.1.2]⟩
      · intro S hS S' hS' hSS
        simp only [𝒮, coe_filter, mem_powersetCard, Set.mem_setOf_eq] at hS hS'
        have := congrArg (· ∪ J) hSS
        simpa [sdiff_union_of_subset hS.2, sdiff_union_of_subset hS'.2] using this
    rw [card_powersetCard, card_univ, Fintype.card_fin] at this
    exact this.trans (Nat.choose_le_pow _ _)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ S ∈ 𝒮, (I.filter fun i => S ⊆ R i).card := card_biUnion_le
    _ ≤ ∑ _S ∈ 𝒮, D := by
        apply sum_le_sum
        intro S hS
        exact hD S (by simp only [𝒮, mem_filter, mem_powersetCard] at hS; exact hS.1.2)
    _ = 𝒮.card * D := by rw [sum_const, smul_eq_mul]
    _ ≤ D * n ^ (r - 1 - J.card) := by rw [mul_comm]; exact Nat.mul_le_mul_left _ h𝒮

/-- Summing the loads of all one-vertex extensions of `U`. -/
theorem sum_load_insert_le {ι : Type*} (R : ι → Finset (Fin n)) (Φ : ι → Fin h → Fin n)
    (s : Finset ι) (J U : Finset (Fin n)) :
    ∑ v ∈ univ \ U, load R Φ s J (insert v U) ≤ h * load R Φ s J U := by
  classical
  unfold load
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro i _
  by_cases hJU : J ⊆ R i ∧ U ⊆ auxImage (Φ i)
  · rw [if_pos hJU, mul_one]
    calc ∑ v ∈ univ \ U, (if J ⊆ R i ∧ insert v U ⊆ auxImage (Φ i) then 1 else 0)
        ≤ ∑ v ∈ univ \ U, (if v ∈ auxImage (Φ i) then 1 else 0) := by
          apply sum_le_sum; intro v _
          split_ifs with h1 h2 <;> simp_all [insert_subset_iff]
      _ ≤ ∑ v, (if v ∈ auxImage (Φ i) then 1 else 0) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
      _ = (auxImage (Φ i)).card := by rw [← sum_filter, ← card_eq_sum_ones]; simp
      _ ≤ h := by
          unfold auxImage
          exact card_image_le.trans (by simp)
  · rw [if_neg hJU, mul_zero]
    apply le_of_eq
    apply sum_eq_zero
    intro v _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hJU ⟨h1, (subset_insert v U).trans h2⟩

/-- Few one-vertex extensions of `U` reach a given load `c`. -/
theorem card_heavy_mul_le {ι : Type*} (R : ι → Finset (Fin n)) (Φ : ι → Fin h → Fin n)
    (s : Finset ι) (J U : Finset (Fin n)) (c : ℕ) :
    ((univ \ U).filter fun v => c ≤ load R Φ s J (insert v U)).card * c ≤
      h * load R Φ s J U := by
  calc _ = ∑ _v ∈ (univ \ U).filter fun v => c ≤ load R Φ s J (insert v U), c := by
        rw [sum_const, smul_eq_mul]
    _ ≤ ∑ v ∈ (univ \ U).filter fun v => c ≤ load R Φ s J (insert v U),
          load R Φ s J (insert v U) := sum_le_sum fun v hv => (mem_filter.1 hv).2
    _ ≤ ∑ v ∈ univ \ U, load R Φ s J (insert v U) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    _ ≤ _ := sum_load_insert_le R Φ s J U

/-- The degree of the union of placed gadgets is controlled by the mixed loads. -/
theorem deg_biUnion_le_loads {ι : Type*} [DecidableEq ι] {r k : ℕ}
    (R : ι → Finset (Fin n)) (T : ι → Finset (Finset (Fin n ⊕ Fin h)))
    (Φ : ι → Fin h → Fin n) (s : Finset ι) (hw : ∀ i ∈ s, GadgetWF r k (R i) (T i))
    (S : Finset (Fin n)) :
    deg (s.biUnion fun i => newEdges (T i) (Φ i)) S ≤
      2 ^ (k + h) * ∑ J ∈ S.powerset, load R Φ s J (S \ J) := by
  classical
  unfold deg
  rw [filter_biUnion]
  calc _ ≤ ∑ i ∈ s, ((newEdges (T i) (Φ i)).filter (fun e => S ⊆ e)).card := card_biUnion_le
    _ ≤ ∑ i ∈ s, if S ⊆ R i ∪ auxImage (Φ i) then 2 ^ (k + h) else 0 := by
        apply sum_le_sum
        intro i hi
        split_ifs with hS
        · exact (card_le_card (filter_subset _ _)).trans
            (card_image_le.trans (card_template_le (hw i hi)))
        · apply le_of_eq
          rw [card_eq_zero, filter_eq_empty_iff]
          intro e he hSe
          simp only [newEdges, mem_image] at he
          obtain ⟨t, ht, rfl⟩ := he
          exact hS (hSe.trans (placeEdge_subset (hw i hi) (Φ i) ht))
    _ = 2 ^ (k + h) * (s.filter fun i => S ⊆ R i ∪ auxImage (Φ i)).card := by
        rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
    _ ≤ 2 ^ (k + h) * ∑ J ∈ S.powerset, load R Φ s J (S \ J) := by
        apply Nat.mul_le_mul_left
        unfold load
        refine (card_le_card ?_).trans card_biUnion_le
        intro i hi
        rw [mem_filter] at hi
        rw [mem_biUnion]
        refine ⟨S ∩ R i, mem_powerset.2 inter_subset_left, mem_filter.2 ⟨hi.1, inter_subset_right,
          ?_⟩⟩
        intro x hx
        rw [mem_sdiff, mem_inter, not_and] at hx
        rcases mem_union.1 (hi.2 hx.1) with h1 | h1
        · exact absurd h1 (hx.2 hx.1)
        · exact h1

end RefinedAbsorption.Placement
