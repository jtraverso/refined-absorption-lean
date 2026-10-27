module
public import RequestProject.Nibble.Hyper

/-!
# The random quantities of one nibble round

For the `p`-random set `S ⊆ E` of chosen edges we study

* `fdeg E v S`: the number of edges `e ∋ v` none of whose other vertices is covered by `S`
  (the new degree of `v` if `v` survives);
* `fcov X S`: the number of vertices of `X` not covered by `S`.

We compute their expectations, show they have bounded differences, and bound the variance
proxies `∑ c_a²`.
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset

variable {α : Type*} [DecidableEq α]

/-- The new degree of `v`: edges `e ∋ v` whose other vertices are all uncovered by `S`. -/
noncomputable def fdeg (E : Finset (Finset α)) (v : α) (S : Finset (Finset α)) : ℝ :=
  ((star E v).filter (fun e => Disjoint (e.erase v) (cov S))).card

/-- The number of vertices of `X` not covered by `S`. -/
noncomputable def fcov (X : Finset α) (S : Finset (Finset α)) : ℝ :=
  (X.filter (fun u => u ∉ cov S)).card

theorem nbhd_subset (E : Finset (Finset α)) (X : Finset α) : nbhd E X ⊆ E := by
  intro g hg
  obtain ⟨u, _, hgu⟩ := mem_biUnion.1 hg
  exact (mem_star.1 hgu).1

theorem Ex_fdeg (p : ℝ) (E : Finset (Finset α)) (v : α) :
    Ex p E (fdeg E v) = ∑ e ∈ star E v, (1 - p) ^ (nbhd E (e.erase v)).card := by
  have h1 : ∀ S ⊆ E, fdeg E v S =
      ∑ e ∈ star E v, if Disjoint S (nbhd E (e.erase v)) then (1 : ℝ) else 0 := by
    intro S hS
    unfold fdeg
    rw [card_filter]
    push_cast
    refine sum_congr rfl fun e _ => ?_
    simp only [disjoint_cov_iff hS]
  rw [Ex_congr p E h1, Ex_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [Ex_ite, Pr_disjoint p (nbhd_subset E _)]

theorem Ex_fcov (p : ℝ) (E : Finset (Finset α)) (X : Finset α) :
    Ex p E (fcov X) = ∑ u ∈ X, (1 - p) ^ (star E u).card := by
  have h1 : ∀ S ⊆ E, fcov X S =
      ∑ u ∈ X, if Disjoint S (star E u) then (1 : ℝ) else 0 := by
    intro S hS
    unfold fcov
    rw [card_filter]
    push_cast
    refine sum_congr rfl fun u _ => ?_
    simp only [mem_cov_iff hS, not_not]
  rw [Ex_congr p E h1, Ex_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [Ex_ite, Pr_disjoint p (show star E u ⊆ E from filter_subset _ _)]

/-- `cov S ⊆ a ∪ cov (S.erase a)`. -/
theorem cov_subset_insert_erase (a : Finset α) (S : Finset (Finset α)) :
    cov S ⊆ a ∪ cov (S.erase a) := by
  intro u hu
  obtain ⟨g, hg, hug⟩ := mem_cov.1 hu
  by_cases hga : g = a
  · exact mem_union_left _ (hga ▸ hug)
  · exact mem_union_right _ (mem_cov.2 ⟨g, mem_erase.2 ⟨hga, hg⟩, hug⟩)

theorem lip_fdeg (E : Finset (Finset α)) (v : α) :
    LipOn E (fdeg E v) (fun a => ∑ u ∈ a.erase v, (codeg E u v : ℝ)) := by
  intro a _ S _
  set X1 := (star E v).filter (fun e => Disjoint (e.erase v) (cov (insert a S)))
  set X0 := (star E v).filter (fun e => Disjoint (e.erase v) (cov (S.erase a)))
  have hsub : X1 ⊆ X0 := by
    intro e he
    rw [mem_filter] at he ⊢
    exact ⟨he.1, disjoint_of_subset_right
      (cov_mono ((erase_subset a S).trans (subset_insert a S))) he.2⟩
  have hdiff : X0 \ X1 ⊆ (a.erase v).biUnion
      (fun u => E.filter (fun e => u ∈ e ∧ v ∈ e)) := by
    intro e he
    rw [mem_sdiff, mem_filter, mem_filter] at he
    obtain ⟨⟨hev, h0⟩, h1⟩ := he
    have hnd : ¬ Disjoint (e.erase v) (cov (insert a S)) := fun h => h1 ⟨hev, h⟩
    rw [cov_insert, not_disjoint_iff] at hnd
    obtain ⟨u, hue, hu⟩ := hnd
    have hua : u ∈ a := by
      rcases mem_union.1 hu with h | h
      · exact h
      · rcases mem_union.1 (cov_subset_insert_erase a S h) with h' | h'
        · exact h'
        · exact absurd h' (disjoint_left.1 h0 hue)
    have huv : u ≠ v := ne_of_mem_erase hue
    refine mem_biUnion.2 ⟨u, mem_erase.2 ⟨huv, hua⟩, mem_filter.2 ⟨(mem_star.1 hev).1,
      mem_of_mem_erase hue, (mem_star.1 hev).2⟩⟩
  unfold fdeg
  have hc : (X0.card : ℝ) - X1.card = ((X0 \ X1).card : ℝ) := by
    rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
  rw [abs_sub_comm, abs_of_nonneg (by
    have := card_le_card hsub; rw [sub_nonneg]; exact_mod_cast this), hc]
  refine le_trans (Nat.cast_le.2 ((card_le_card hdiff).trans card_biUnion_le)) ?_
  push_cast
  rfl

theorem lip_fcov (E : Finset (Finset α)) (X : Finset α) :
    LipOn E (fcov X) (fun a => ((a ∩ X).card : ℝ)) := by
  intro a _ S _
  set X1 := X.filter (fun u => u ∉ cov (insert a S))
  set X0 := X.filter (fun u => u ∉ cov (S.erase a))
  have hsub : X1 ⊆ X0 := by
    intro u hu
    rw [mem_filter] at hu ⊢
    exact ⟨hu.1, fun h => hu.2
      (cov_mono ((erase_subset a S).trans (subset_insert a S)) h)⟩
  have hdiff : X0 \ X1 ⊆ a ∩ X := by
    intro u hu
    rw [mem_sdiff, mem_filter, mem_filter] at hu
    obtain ⟨⟨huX, h0⟩, h1⟩ := hu
    have : u ∈ cov (insert a S) := by
      by_contra h; exact h1 ⟨huX, h⟩
    rw [cov_insert] at this
    rcases mem_union.1 this with h | h
    · exact mem_inter.2 ⟨h, huX⟩
    · rcases mem_union.1 (cov_subset_insert_erase a S h) with h' | h'
      · exact mem_inter.2 ⟨h', huX⟩
      · exact absurd h' h0
  unfold fcov
  have hc : (X0.card : ℝ) - X1.card = ((X0 \ X1).card : ℝ) := by
    rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
  rw [abs_sub_comm, abs_of_nonneg (by
    have := card_le_card hsub; rw [sub_nonneg]; exact_mod_cast this), hc]
  show ((X0 \ X1).card : ℝ) ≤ ((a ∩ X).card : ℝ)
  exact_mod_cast card_le_card hdiff

/-- Variance proxy for the new degree. -/
theorem sum_sq_lip_fdeg_le {E : Finset (Finset α)} {V : Finset α} {k : ℕ} {Dmax C : ℝ}
    (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ u ∈ V, ((star E u).card : ℝ) ≤ Dmax)
    (hcod : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ C) (v : α) :
    ∑ a ∈ E, (∑ u ∈ a.erase v, (codeg E u v : ℝ)) ^ 2 ≤
      k * Dmax * C * ((k - 1) * (star E v).card) := by
  have hC0 : ∀ u, u ≠ v → (codeg E u v : ℝ) ^ 2 ≤ C * codeg E u v := fun u hu => by
    have := hcod u v hu
    nlinarith [(Nat.cast_nonneg (codeg E u v) : (0 : ℝ) ≤ codeg E u v)]
  have step1 : ∀ a ∈ E, (∑ u ∈ a.erase v, (codeg E u v : ℝ)) ^ 2 ≤
      k * ∑ u ∈ a ∩ V.erase v, (codeg E u v : ℝ) ^ 2 := by
    intro a ha
    have hae : a.erase v = a ∩ V.erase v := by
      ext u; simp only [mem_erase, mem_inter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, hEV a ha h2⟩
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    rw [hae]
    gcongr
    have : (a ∩ V.erase v).card ≤ k := (card_le_card inter_subset_left).trans (hk a ha).le
    exact_mod_cast this
  calc ∑ a ∈ E, (∑ u ∈ a.erase v, (codeg E u v : ℝ)) ^ 2
      ≤ ∑ a ∈ E, k * ∑ u ∈ a ∩ V.erase v, (codeg E u v : ℝ) ^ 2 := sum_le_sum step1
    _ = k * ∑ u ∈ V.erase v, ((star E u).card : ℝ) * (codeg E u v : ℝ) ^ 2 := by
        rw [← mul_sum, sum_sum_inter_eq]
    _ ≤ k * ∑ u ∈ V.erase v, Dmax * (C * codeg E u v) := by
        gcongr with u hu
        all_goals first
          | exact (Nat.cast_nonneg _).trans (hdeg u (mem_of_mem_erase hu))
          | exact hdeg u (mem_of_mem_erase hu)
          | exact hC0 u (ne_of_mem_erase hu)
    _ = k * Dmax * C * ∑ u ∈ V.erase v, (codeg E u v : ℝ) := by
        simp only [mul_sum]; exact sum_congr rfl fun u _ => by ring
    _ = k * Dmax * C * ((k - 1) * (star E v).card) := by
        congr 1
        have := sum_codeg_eq E (V.erase v) v
        have h2 : ∀ e ∈ star E v, (e ∩ V.erase v).card = k - 1 := by
          intro e he
          obtain ⟨heE, hve⟩ := mem_star.1 he
          have : e ∩ V.erase v = e.erase v := by
            ext u; simp only [mem_erase, mem_inter]
            constructor
            · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
            · rintro ⟨h1, h2⟩; exact ⟨h2, h1, hEV e heE h2⟩
          rw [this, card_erase_of_mem hve, hk e heE]
        rw [sum_congr rfl h2, sum_const, smul_eq_mul] at this
        have hk1 : 1 ≤ k ∨ star E v = ∅ := by
          by_cases h : star E v = ∅
          · exact Or.inr h
          · obtain ⟨e, he⟩ := nonempty_iff_ne_empty.2 h
            left
            have := hk e (mem_star.1 he).1
            have : 0 < e.card := card_pos.2 ⟨v, (mem_star.1 he).2⟩
            omega
        rw [← Nat.cast_sum, this]
        rcases hk1 with hk1 | h
        · push_cast [Nat.cast_sub hk1]; ring
        · simp [h]

/-- Variance proxy for the number of uncovered vertices. -/
theorem sum_sq_lip_fcov_le {E : Finset (Finset α)} {k : ℕ} (hk : ∀ F ∈ E, F.card = k)
    (X : Finset α) :
    ∑ a ∈ E, ((a ∩ X).card : ℝ) ^ 2 ≤ k * ∑ u ∈ X, ((star E u).card : ℝ) := by
  have : ∀ a ∈ E, ((a ∩ X).card : ℝ) ^ 2 ≤ k * (a ∩ X).card := by
    intro a ha
    have h1 : (a ∩ X).card ≤ k := (card_le_card inter_subset_left).trans (hk a ha).le
    have h1' : ((a ∩ X).card : ℝ) ≤ k := by exact_mod_cast h1
    nlinarith [(Nat.cast_nonneg (a ∩ X).card : (0 : ℝ) ≤ _)]
  refine (sum_le_sum this).trans (le_of_eq ?_)
  rw [← mul_sum]
  congr 1
  have := sum_card_inter_eq E X
  exact_mod_cast this

end RefinedAbsorption.Nibble
