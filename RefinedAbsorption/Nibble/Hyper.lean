module
public import RefinedAbsorption.Nibble.FiniteProb

/-!
# Hypergraph notions for one round of the nibble

A hypergraph is a finite set `E : Finset (Finset α)` of edges.  In one round of the nibble a
random set `S ⊆ E` of edges is chosen; `cov S` is the set of vertices covered by `S`, `iso S`
the set of chosen edges meeting no other chosen edge (these are added to the matching),
`nextE E S` the edges of `E` avoiding all covered vertices, and `waste S` the covered vertices
that are not covered by `iso S`.
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset

variable {α : Type*} [DecidableEq α]

/-- The edges of `E` containing `v`. -/
def star (E : Finset (Finset α)) (v : α) : Finset (Finset α) := E.filter (fun e => v ∈ e)

/-- The number of edges of `E` containing both `u` and `v`. -/
def codeg (E : Finset (Finset α)) (u v : α) : ℕ := (E.filter (fun e => u ∈ e ∧ v ∈ e)).card

/-- The vertices covered by a set of edges. -/
def cov (S : Finset (Finset α)) : Finset α := S.biUnion id

/-- The edges of `S` meeting no other edge of `S`. -/
def iso (S : Finset (Finset α)) : Finset (Finset α) :=
  S.filter (fun g => ∀ h ∈ S, h ≠ g → Disjoint g h)

/-- The edges of `E` avoiding every vertex covered by `S`. -/
def nextE (E S : Finset (Finset α)) : Finset (Finset α) := E.filter (fun e => Disjoint e (cov S))

/-- Covered vertices that are not covered by isolated chosen edges. -/
def waste (S : Finset (Finset α)) : Finset α := cov S \ cov (iso S)

/-- The edges of `E` meeting the set `X`. -/
def nbhd (E : Finset (Finset α)) (X : Finset α) : Finset (Finset α) := X.biUnion (star E)

theorem mem_star {E : Finset (Finset α)} {v : α} {e : Finset α} :
    e ∈ star E v ↔ e ∈ E ∧ v ∈ e := mem_filter

theorem mem_cov {S : Finset (Finset α)} {u : α} : u ∈ cov S ↔ ∃ g ∈ S, u ∈ g := by
  simp [cov]

theorem mem_cov_iff {E S : Finset (Finset α)} (hS : S ⊆ E) {u : α} :
    u ∈ cov S ↔ ¬ Disjoint S (star E u) := by
  rw [mem_cov, not_disjoint_iff]
  constructor
  · rintro ⟨g, hg, hu⟩; exact ⟨g, hg, mem_star.2 ⟨hS hg, hu⟩⟩
  · rintro ⟨g, hg, hg'⟩; exact ⟨g, hg, (mem_star.1 hg').2⟩

theorem disjoint_cov_iff {E S : Finset (Finset α)} (hS : S ⊆ E) {X : Finset α} :
    Disjoint X (cov S) ↔ Disjoint S (nbhd E X) := by
  constructor
  · intro h
    rw [disjoint_left]
    intro g hg hg'
    obtain ⟨u, hu, hgu⟩ := mem_biUnion.1 hg'
    exact disjoint_left.1 h hu (mem_cov.2 ⟨g, hg, (mem_star.1 hgu).2⟩)
  · intro h
    rw [disjoint_left]
    intro u hu hcov
    obtain ⟨g, hg, hug⟩ := mem_cov.1 hcov
    exact disjoint_left.1 h hg (mem_biUnion.2 ⟨u, hu, mem_star.2 ⟨hS hg, hug⟩⟩)

theorem cov_mono {S S' : Finset (Finset α)} (h : S ⊆ S') : cov S ⊆ cov S' :=
  biUnion_subset_biUnion_of_subset_left _ h

theorem cov_insert (a : Finset α) (S : Finset (Finset α)) : cov (insert a S) = a ∪ cov S := by
  simp [cov]

theorem cov_subset_of_subset {E S : Finset (Finset α)} {V : Finset α} (hS : S ⊆ E)
    (hEV : ∀ F ∈ E, F ⊆ V) : cov S ⊆ V := by
  intro u hu
  obtain ⟨g, hg, hug⟩ := mem_cov.1 hu
  exact hEV g (hS hg) hug

/-- Bonferroni lower bound for the size of a union. -/
theorem card_biUnion_ge {ι : Type*} [DecidableEq ι] (s : Finset ι) (A : ι → Finset α) :
    (∑ i ∈ s, ((A i).card : ℤ)) - ∑ i ∈ s, ∑ j ∈ s.erase i, ((A i ∩ A j).card : ℤ)
      ≤ ((s.biUnion A).card : ℤ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha, sum_insert ha, erase_insert ha]
    have hu := card_union_add_card_inter (A a) (s.biUnion A)
    have hint : ((A a ∩ s.biUnion A).card : ℤ) ≤ ∑ j ∈ s, ((A a ∩ A j).card : ℤ) := by
      rw [inter_biUnion]
      exact_mod_cast card_biUnion_le
    have hrest : ∑ i ∈ s, ∑ j ∈ s.erase i, ((A i ∩ A j).card : ℤ) ≤
        ∑ i ∈ s, ∑ j ∈ (insert a s).erase i, ((A i ∩ A j).card : ℤ) := by
      refine sum_le_sum fun i hi => ?_
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      rw [erase_insert_of_ne hia.symm]
      exact sum_le_sum_of_subset_of_nonneg (subset_insert _ _) fun _ _ _ => by positivity
    have hu' : ((A a ∪ s.biUnion A).card : ℤ) + ((A a ∩ s.biUnion A).card : ℤ) =
        ((A a).card : ℤ) + ((s.biUnion A).card : ℤ) := by exact_mod_cast hu
    linarith

/-- Double counting: `∑_{a ∈ E} |a ∩ X| = ∑_{u ∈ X} deg(u)`. -/
theorem sum_card_inter_eq (E : Finset (Finset α)) (X : Finset α) :
    ∑ a ∈ E, (a ∩ X).card = ∑ u ∈ X, (star E u).card := by
  have : ∀ a ∈ E, (a ∩ X).card = ∑ u ∈ X, if u ∈ a then 1 else 0 := by
    intro a _
    rw [← card_filter]; congr 1; ext u; simp [and_comm]
  rw [sum_congr rfl this, sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [← card_filter]; rfl

/-- Weighted double counting: `∑_{a ∈ E} ∑_{u ∈ a ∩ X} w u = ∑_{u ∈ X} deg(u) w(u)`. -/
theorem sum_sum_inter_eq (E : Finset (Finset α)) (X : Finset α) (w : α → ℝ) :
    ∑ a ∈ E, ∑ u ∈ a ∩ X, w u = ∑ u ∈ X, ((star E u).card : ℝ) * w u := by
  have : ∀ a ∈ E, ∑ u ∈ a ∩ X, w u = ∑ u ∈ X, if u ∈ a then w u else 0 := by
    intro a _
    rw [← sum_filter]; congr 1; ext u; simp [and_comm]
  rw [sum_congr rfl this, sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  rfl

/-- `∑_{u ∈ X} codeg(u, v) = ∑_{e ∋ v} |e ∩ X|`. -/
theorem sum_codeg_eq (E : Finset (Finset α)) (X : Finset α) (v : α) :
    ∑ u ∈ X, codeg E u v = ∑ e ∈ star E v, (e ∩ X).card := by
  have h1 : ∀ e ∈ star E v, (e ∩ X).card = ∑ u ∈ X, if u ∈ e then 1 else 0 := by
    intro e _
    rw [← card_filter]; congr 1; ext u; simp [and_comm]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [← card_filter]
  unfold codeg star
  rw [filter_filter]
  congr 1
  ext e; simp [and_comm]

end RefinedAbsorption.Nibble
