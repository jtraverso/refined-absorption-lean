module
public import RefinedAbsorption.Nibble.RoundProb

/-!
# Bounding the waste of a nibble round

A covered vertex is *wasted* if the chosen edge covering it meets another chosen edge.  We bound
the number of wasted vertices in a test set `X` deterministically in terms of

* the maximum number `L` of chosen edges through a vertex, and
* the maximum number of pairwise edge-disjoint chosen *witness pairs* `(g, h)` (two distinct
  intersecting chosen edges with `g` meeting `X`),

and we bound the probability that either of these quantities is large by union bounds over
sets of edges that must all be chosen.
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset

variable {α : Type*} [DecidableEq α]

/-- Witness pairs for the test set `X`: ordered pairs of distinct intersecting edges, the first
of which meets `X`. -/
def witPairs (E : Finset (Finset α)) (X : Finset α) : Finset (Finset α × Finset α) :=
  (E ×ˢ E).filter (fun gh => gh.1 ≠ gh.2 ∧ ¬ Disjoint gh.1 X ∧ ¬ Disjoint gh.1 gh.2)

/-- The two edges of a pair. -/
def pairSet (gh : Finset α × Finset α) : Finset (Finset α) := {gh.1, gh.2}

open Classical in
/-- Families of `s` witness pairs with pairwise disjoint edge sets. -/
noncomputable def witFam (E : Finset (Finset α)) (X : Finset α) (s : ℕ) :
    Finset (Finset (Finset α × Finset α)) :=
  ((witPairs E X).powersetCard s).filter
    (fun P => (P : Set (Finset α × Finset α)).PairwiseDisjoint pairSet)

theorem pairSet_subset {E : Finset (Finset α)} {X : Finset α} {gh : Finset α × Finset α}
    (h : gh ∈ witPairs E X) : pairSet gh ⊆ E := by
  unfold witPairs at h
  rw [mem_filter, mem_product] at h
  intro g hg
  rcases mem_insert.1 hg with h' | h'
  · exact h' ▸ h.1.1
  · exact (mem_singleton.1 h') ▸ h.1.2

theorem card_biUnion_pairSet {E : Finset (Finset α)} {X : Finset α} {s : ℕ}
    {P : Finset (Finset α × Finset α)} (hP : P ∈ witFam E X s) :
    (P.biUnion pairSet).card = 2 * s := by
  classical
  unfold witFam at hP
  rw [mem_filter, mem_powersetCard] at hP
  rw [card_biUnion (fun x hx y hy hxy => hP.2 hx hy hxy)]
  rw [← hP.1.2, card_eq_sum_ones, mul_sum, mul_one]
  refine sum_congr rfl fun gh hgh => ?_
  have := hP.1.1 hgh
  unfold witPairs at this
  rw [mem_filter] at this
  exact card_pair this.2.1

/-- Probability that some family of `s` disjoint witness pairs is entirely chosen. -/
theorem Pr_wit_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset (Finset α)) (X : Finset α)
    (s : ℕ) :
    Pr p E (fun S => ∃ P ∈ witFam E X s, P.biUnion pairSet ⊆ S) ≤
      ((witPairs E X).card.choose s : ℝ) * p ^ (2 * s) := by
  classical
  refine (Pr_exists_le hp0 hp1 E (witFam E X s) (fun P S => P.biUnion pairSet ⊆ S)).trans ?_
  have : ∀ P ∈ witFam E X s, Pr p E (fun S => P.biUnion pairSet ⊆ S) = p ^ (2 * s) := by
    intro P hP
    rw [Pr_subset p, card_biUnion_pairSet hP]
    intro g hg
    obtain ⟨gh, hgh, hg'⟩ := mem_biUnion.1 hg
    unfold witFam at hP
    rw [mem_filter, mem_powersetCard] at hP
    exact pairSet_subset (hP.1.1 hgh) hg'
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul]
  gcongr
  have : (witFam E X s).card ≤ ((witPairs E X).powersetCard s).card := card_filter_le _ _
  rw [card_powersetCard] at this
  exact_mod_cast this

/-- Probability that some vertex of `V` lies in `L` chosen edges. -/
theorem Pr_bad_vertex_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset (Finset α))
    (V : Finset α) (L : ℕ) :
    Pr p E (fun S => ∃ w ∈ V, ∃ F ∈ (star E w).powersetCard L, F ⊆ S) ≤
      ∑ w ∈ V, ((star E w).card.choose L : ℝ) * p ^ L := by
  refine (Pr_exists_le hp0 hp1 E V _).trans (sum_le_sum fun w _ => ?_)
  refine (Pr_exists_subset_le hp0 hp1 _ fun F hF => ?_).trans (le_of_eq ?_)
  · exact (mem_powersetCard.1 hF).1.trans (filter_subset _ _)
  · rw [sum_congr rfl fun F hF => by rw [(mem_powersetCard.1 hF).2], sum_const,
      card_powersetCard, nsmul_eq_mul]

theorem card_nbhd_le {E : Finset (Finset α)} {V X : Finset α} {Dmax : ℝ} (hXV : X ⊆ V)
    (hdeg : ∀ u ∈ V, ((star E u).card : ℝ) ≤ Dmax) :
    ((nbhd E X).card : ℝ) ≤ X.card * Dmax := by
  refine (Nat.cast_le.2 card_biUnion_le).trans ?_
  push_cast
  calc ∑ u ∈ X, ((star E u).card : ℝ) ≤ ∑ u ∈ X, Dmax := sum_le_sum fun u hu => hdeg u (hXV hu)
    _ = X.card * Dmax := by rw [sum_const, nsmul_eq_mul]

/-- Number of witness pairs. -/
theorem card_witPairs_le {E : Finset (Finset α)} {V X : Finset α} {k : ℕ} {Dmax : ℝ}
    (hD : 0 ≤ Dmax) (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V) (hXV : X ⊆ V)
    (hdeg : ∀ u ∈ V, ((star E u).card : ℝ) ≤ Dmax) :
    ((witPairs E X).card : ℝ) ≤ (X.card * Dmax) * (k * Dmax) := by
  have hsub : witPairs E X ⊆ (nbhd E X).biUnion
      (fun g => (nbhd E g).image (fun h => (g, h))) := by
    intro gh hgh
    unfold witPairs at hgh
    rw [mem_filter, mem_product] at hgh
    obtain ⟨⟨hg, hh⟩, _, hgX, hgh'⟩ := hgh
    rw [not_disjoint_iff] at hgX hgh'
    obtain ⟨u, hug, huX⟩ := hgX
    obtain ⟨w, hwg, hwh⟩ := hgh'
    refine mem_biUnion.2 ⟨gh.1, mem_biUnion.2 ⟨u, huX, mem_star.2 ⟨hg, hug⟩⟩,
      mem_image.2 ⟨gh.2, mem_biUnion.2 ⟨w, hwg, mem_star.2 ⟨hh, hwh⟩⟩, rfl⟩⟩
  have h2 : ∀ g ∈ nbhd E X, (((nbhd E g).image (fun h => (g, h))).card : ℝ) ≤ k * Dmax := by
    intro g hg
    have hgE := nbhd_subset E X hg
    refine (Nat.cast_le.2 card_image_le).trans ?_
    refine (card_nbhd_le (hEV g hgE) hdeg).trans ?_
    rw [hk g hgE]
  calc ((witPairs E X).card : ℝ)
      ≤ ((nbhd E X).biUnion (fun g => (nbhd E g).image (fun h => (g, h)))).card := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ g ∈ nbhd E X, (((nbhd E g).image (fun h => (g, h))).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ g ∈ nbhd E X, (k * Dmax : ℝ) := sum_le_sum h2
    _ = (nbhd E X).card * (k * Dmax) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (X.card * Dmax) * (k * Dmax) := by
        gcongr
        exact card_nbhd_le hXV hdeg

/-- **Deterministic waste bound.**  If every vertex lies in at most `L` chosen edges and there
is no family of `s ≥ 1` pairwise disjoint chosen witness pairs, then at most
`k (1 + k L) · 2 (s - 1)` vertices of `X` are wasted. -/
theorem card_waste_inter_le {E S : Finset (Finset α)} {V X : Finset α} {k L s : ℕ}
    (hS : S ⊆ E) (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hgood : ∀ w ∈ V, (S.filter (fun g => w ∈ g)).card ≤ L)
    (hno : ¬ ∃ P ∈ witFam E X s, P.biUnion pairSet ⊆ S) :
    (waste S ∩ X).card ≤ k * (1 + k * L) * (2 * (s - 1)) := by
  classical
  set Sp := (witPairs E X).filter (fun gh => gh.1 ∈ S ∧ gh.2 ∈ S)
  set cands := (Sp.powerset).filter (fun P : Finset (Finset α × Finset α) =>
    (↑P : Set (Finset α × Finset α)).PairwiseDisjoint pairSet)
  have hne : cands.Nonempty := ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by simp⟩⟩
  obtain ⟨P, hP, hmax⟩ := exists_max_image cands card hne
  rw [mem_filter, mem_powerset] at hP
  have hPs : P.card ≤ s - 1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨P', hP'P, hP'card⟩ := exists_subset_card_eq (show s ≤ P.card by omega)
    refine hno ⟨P', ?_, ?_⟩
    · unfold witFam
      rw [mem_filter, mem_powersetCard]
      exact ⟨⟨hP'P.trans (hP.1.trans (filter_subset _ _)), hP'card⟩,
        hP.2.subset (by exact_mod_cast hP'P)⟩
    · intro g hg
      obtain ⟨gh, hgh, hg'⟩ := mem_biUnion.1 hg
      have := (mem_filter.1 (hP.1 (hP'P hgh))).2
      rcases mem_insert.1 hg' with h | h
      · exact h ▸ this.1
      · exact (mem_singleton.1 h) ▸ this.2
  set F := P.biUnion pairSet
  have hFS : F ⊆ S := by
    intro g hg
    obtain ⟨gh, hgh, hg'⟩ := mem_biUnion.1 hg
    have := (mem_filter.1 (hP.1 hgh)).2
    rcases mem_insert.1 hg' with h | h
    · exact h ▸ this.1
    · exact (mem_singleton.1 h) ▸ this.2
  have hFcard : F.card ≤ 2 * P.card := by
    refine card_biUnion_le.trans ?_
    rw [card_eq_sum_ones P, mul_sum, mul_one]
    exact sum_le_sum fun gh _ => card_le_two
  set NI := S.filter (fun g => ¬ Disjoint g X ∧ ∃ h ∈ S, h ≠ g ∧ ¬ Disjoint g h)
  have hwaste : waste S ∩ X ⊆ NI.biUnion (fun g => g ∩ X) := by
    intro u hu
    rw [mem_inter] at hu
    obtain ⟨hw, huX⟩ := hu
    unfold waste at hw
    rw [mem_sdiff] at hw
    obtain ⟨g, hg, hug⟩ := mem_cov.1 hw.1
    have hgiso : g ∉ iso S := fun h => hw.2 (mem_cov.2 ⟨g, h, hug⟩)
    unfold iso at hgiso
    rw [mem_filter] at hgiso
    push_neg at hgiso
    obtain ⟨h, hh, hhg, hgh⟩ := hgiso hg
    refine mem_biUnion.2 ⟨g, mem_filter.2 ⟨hg, not_disjoint_iff.2 ⟨u, hug, huX⟩, h, hh, hhg, hgh⟩,
      mem_inter.2 ⟨hug, huX⟩⟩
  have hNI : NI ⊆ F ∪ F.biUnion (fun h => h.biUnion (fun w => S.filter (fun g => w ∈ g))) := by
    intro g hg
    rw [mem_filter] at hg
    obtain ⟨hgS, hgX, h, hhS, hhg, hgh⟩ := hg
    have hpair : (g, h) ∈ Sp := by
      refine mem_filter.2 ⟨?_, hgS, hhS⟩
      unfold witPairs
      exact mem_filter.2 ⟨mem_product.2 ⟨hS hgS, hS hhS⟩, fun e => hhg e.symm, hgX, hgh⟩
    by_cases hdisj : Disjoint (pairSet (g, h)) F
    · exfalso
      have hnotin : (g, h) ∉ P := by
        intro hin
        have : g ∈ F := mem_biUnion.2 ⟨(g, h), hin, mem_insert_self _ _⟩
        exact disjoint_left.1 hdisj (mem_insert_self _ _) this
      have hcand : insert (g, h) P ∈ cands := by
        refine mem_filter.2 ⟨mem_powerset.2 (insert_subset hpair hP.1), ?_⟩
        rw [coe_insert]
        refine hP.2.insert fun π hπ _ => ?_
        exact disjoint_of_subset_right (subset_biUnion_of_mem pairSet hπ) hdisj
      have := hmax _ hcand
      rw [card_insert_of_notMem hnotin] at this
      omega
    · rw [not_disjoint_iff] at hdisj
      obtain ⟨x, hx, hxF⟩ := hdisj
      rcases mem_insert.1 hx with hxg | hxh
      · have hxg' : x = g := hxg
        exact mem_union_left _ (hxg' ▸ hxF)
      · rw [mem_singleton] at hxh
        subst hxh
        rw [not_disjoint_iff] at hgh
        obtain ⟨w, hwg, hwh⟩ := hgh
        exact mem_union_right _ (mem_biUnion.2 ⟨x, hxF, mem_biUnion.2 ⟨w, hwh,
          mem_filter.2 ⟨hgS, hwg⟩⟩⟩)
  have hNIcard : NI.card ≤ (1 + k * L) * F.card := by
    refine (card_le_card hNI).trans ((card_union_le _ _).trans ?_)
    have : (F.biUnion (fun h => h.biUnion (fun w => S.filter (fun g => w ∈ g)))).card ≤
        F.card * (k * L) := by
      refine card_biUnion_le.trans ?_
      rw [card_eq_sum_ones F, sum_mul, one_mul]
      refine sum_le_sum fun h hh => card_biUnion_le.trans ?_
      have hhE := hS (hFS hh)
      calc ∑ w ∈ h, (S.filter (fun g => w ∈ g)).card ≤ ∑ w ∈ h, L :=
            sum_le_sum fun w hw => hgood w (hEV h hhE hw)
        _ = k * L := by rw [sum_const, smul_eq_mul, hk h hhE]
    nlinarith
  have hwcard : (waste S ∩ X).card ≤ k * NI.card := by
    refine (card_le_card hwaste).trans (card_biUnion_le.trans ?_)
    rw [card_eq_sum_ones NI, mul_sum, mul_one]
    exact sum_le_sum fun g hg =>
      (card_le_card inter_subset_left).trans (hk g (hS (mem_filter.1 hg).1)).le
  calc (waste S ∩ X).card ≤ k * NI.card := hwcard
    _ ≤ k * ((1 + k * L) * F.card) := Nat.mul_le_mul_left _ hNIcard
    _ ≤ k * ((1 + k * L) * (2 * (s - 1))) := by
        gcongr; omega
    _ = k * (1 + k * L) * (2 * (s - 1)) := by ring

end RefinedAbsorption.Nibble
