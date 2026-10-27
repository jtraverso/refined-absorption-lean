module
public import RefinedAbsorption.Original2024.Core
public import RefinedAbsorption.ExistenceProof

/-!
# Theorems 1.11 and 1.7 of the original article for `r ≥ 2`

The host `G` enters only through the forbidden graph `F = K_n^r \ G`: if
`δ_{r-1}(G) ≥ (1 - 1/C) n` then `C · Δ(F) ≤ n`, so `hostCore` produces a refiner and absorbers
avoiding `F`, i.e. inside `G`.

* `theorem_1_11_strong_two_le`, `theorem_1_11_two_le`: Theorem 1.11 (with, in the strong form,
  one `X`-edge per piece and the family degree bound).
* `theorem_1_7_strong_two_le`, `theorem_1_7_two_le`: Theorem 1.7 (with, in the strong form,
  one `X`-edge per clique of the decomposition family).
-/

@[expose] public section

namespace RefinedAbsorption.Original2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Absorber17 RefinedAbsorption.Placement

/-- The complement `K_n^r \ G` of a host with `δ_{r-1}(G) ≥ (1 - 1/C) n` has `C · Δ ≤ n`. -/
theorem mul_deg_compl_le {n r C : ℕ} (hC : 1 ≤ C) {G : Finset (Finset (Fin n))}
    (hG : IsRGraph r G) (hδ : MinDegGE r G ((1 - 1 / (C : ℝ)) * n)) (S : Finset (Fin n))
    (hS : S.card + 1 = r) : C * deg (completeRGraph (Fin n) r \ G) S ≤ n := by
  have hsub : G ⊆ completeRGraph (Fin n) r := fun e he =>
    mem_powersetCard.2 ⟨subset_univ _, hG e he⟩
  have hsum : deg (completeRGraph (Fin n) r \ G) S + deg G S =
      deg (completeRGraph (Fin n) r) S := by
    rw [← deg_union_of_disjoint sdiff_disjoint, sdiff_union_of_subset hsub]
  have hfull : deg (completeRGraph (Fin n) r) S ≤ n := by
    rw [deg_completeRGraph (by omega), show r - S.card = 1 by omega, Nat.choose_one_right]
    omega
  have h1 := hδ S hS
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hreal : (deg (completeRGraph (Fin n) r \ G) S : ℝ) ≤ n / C := by
    have : ((deg (completeRGraph (Fin n) r \ G) S : ℕ) : ℝ) + deg G S ≤ n := by
      exact_mod_cast hsum ▸ hfull
    have e : (1 - 1 / (C : ℝ)) * n = n - n / C := by ring
    linarith
  have : (C : ℝ) * deg (completeRGraph (Fin n) r \ G) S ≤ n := by
    calc (C : ℝ) * deg (completeRGraph (Fin n) r \ G) S ≤ C * (n / C) :=
          mul_le_mul_of_nonneg_left hreal hCpos.le
      _ = n := by field_simp
  exact_mod_cast this

/-- An `r`-graph avoiding `K_n^r \ G` lies in `G`. -/
theorem subset_of_disjoint_compl {n r : ℕ} {G R : Finset (Finset (Fin n))}
    (hR : ∀ e ∈ R, e.card = r) (hd : Disjoint R (completeRGraph (Fin n) r \ G)) : R ⊆ G := by
  intro e he
  by_contra hG
  exact disjoint_left.1 hd he (mem_sdiff.2 ⟨mem_powersetCard.2 ⟨subset_univ _, hR e he⟩, hG⟩)

open Classical in
/-- A decomposition function chosen from a refined refiner. -/
noncomputable def chosenQR {V : Type*} [DecidableEq V] {q r C : ℕ} {X R : Finset (Finset V)}
    {𝒲 : Finset (Finset (Finset V))} (hR : IsRefinedRefiner q r C X R 𝒲) :
    Finset (Finset V) → Finset (Finset (Finset V)) := fun L =>
  if h : L ⊆ X ∧ IsDivisible q r L then (hR.decomp L h.1 h.2).choose else ∅

theorem chosenQR_spec {V : Type*} [DecidableEq V] {q r C : ℕ} {X R : Finset (Finset V)}
    {𝒲 : Finset (Finset (Finset V))} (hR : IsRefinedRefiner q r C X R 𝒲) {L : Finset (Finset V)}
    (hL : L ⊆ X) (hd : IsDivisible q r L) :
    chosenQR hR L ⊆ 𝒲 ∧ (chosenQR hR L : Set (Finset (Finset V))).PairwiseDisjoint id ∧
      (chosenQR hR L).sup id = R ∪ L := by
  have h : L ⊆ X ∧ IsDivisible q r L := ⟨hL, hd⟩
  rw [chosenQR, dif_pos h]
  exact (hR.decomp L h.1 h.2).choose_spec

/-- **Theorem 1.11 (strong form), `r ≥ 2`.** -/
theorem theorem_1_11_strong_two_le {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    Theorem_1_11_strong_for q r := by
  obtain ⟨C, hC, hcore⟩ := hostCore (q := q) hr hrq
  refine ⟨C, hC, 1 / C, by positivity, ?_⟩
  intro n G X D hG hδ hXG hXD hDn
  have hX : IsRGraph r X := fun e he => hG e (hXG he)
  obtain ⟨R, 𝒲, A, Qon, Qoff, hW⟩ := hcore n X (completeRGraph (Fin n) r \ G) D hX hXD hDn
    (fun S hS => mul_deg_compl_le hC hG hδ S hS)
  have hR := hW.refiner
  have hRr : ∀ e ∈ R, e.card = r := fun e he => hR.rgraph e (mem_union_right _ he)
  refine ⟨R, 𝒲, chosenQR hR, ⟨fun e he => ⟨hX e he, subset_univ _⟩,
    fun e he => ⟨hRr e he, subset_univ _⟩, hR.disjoint,
    fun H hH => ⟨hR.subset H hH, hR.divisible H hH⟩,
    fun L hL hd => (chosenQR_spec hR hL hd).1, fun L hL hd => (chosenQR_spec hR hL hd).2.1,
    fun L hL hd => (chosenQR_spec hR hL hd).2.2⟩,
    subset_of_disjoint_compl hRr hW.avoidR, ⟨hR.mult_le, hR.card_le, hW.vert_le⟩, hW.degR,
    hW.oneX, hW.pieceDeg⟩

/-- **Theorem 1.11, `r ≥ 2`.** -/
theorem theorem_1_11_two_le {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) : Theorem_1_11_for q r := by
  obtain ⟨C, hC, ε, hε, h⟩ := theorem_1_11_strong_two_le (q := q) hr hrq
  refine ⟨C, hC, ε, hε, fun n G X D hG hδ hXG hXD hDn => ?_⟩
  obtain ⟨R, F, QR, h1, h2, h3, h4, -⟩ := h n G X D hG hδ hXG hXD hDn
  exact ⟨R, F, QR, h1, h2, h3, h4⟩

/-- **Theorem 1.7 (strong form), `r ≥ 2`.** -/
theorem theorem_1_7_strong_two_le {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    Theorem_1_7_strong_for q r := by
  obtain ⟨C, hC, hcore⟩ := hostCore (q := q) hr hrq
  refine ⟨2 * C, by omega, 1 / C, by positivity, ?_⟩
  intro n G X D hG hδ hXG hXD hDn
  have hX : IsRGraph r X := fun e he => hG e (hXG he)
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hDn' : D ≤ n / C := hDn.trans (div_le_div_of_nonneg_left hn0 hCpos (by push_cast; linarith))
  obtain ⟨R, 𝒲, A, Qon, Qoff, hW⟩ := hcore n X (completeRGraph (Fin n) r \ G) D hX hXD hDn'
    (fun S hS => mul_deg_compl_le hC hG hδ S hS)
  have hR := hW.refiner
  have hA := hW.absorbers
  obtain ⟨QA, hQA, href⟩ := omniAbsorber_of_refiner_absorbers hrq.le hC hR hA
  have hRr : ∀ e ∈ R, e.card = r := fun e he => hR.rgraph e (mem_union_right _ he)
  have hAr : ∀ e ∈ R ∪ 𝒲.sup A, e.card = r := by
    intro e he
    rcases mem_union.1 he with h | h
    · exact hRr e h
    · obtain ⟨W, hW', heW⟩ := mem_sup.1 h
      exact hA.rgraph W hW' e heW
  have hAF : Disjoint (R ∪ 𝒲.sup A) (completeRGraph (Fin n) r \ G) := by
    rw [disjoint_union_left]
    exact ⟨hW.avoidR, Finset.disjoint_sup_left.2 hW.avoidA⟩
  -- cliques of the family
  have hfam : ∀ Q ∈ 𝒲.sup (fun W => Qon W ∪ Qoff W), ∃ W ∈ 𝒲,
      (Q ∈ Qon W ∧ cliqueEdges r Q ⊆ A W ∪ W) ∨ (Q ∈ Qoff W ∧ cliqueEdges r Q ⊆ A W) := by
    intro Q hQ
    obtain ⟨W, hW', hQW⟩ := mem_sup.1 hQ
    refine ⟨W, hW', ?_⟩
    rcases mem_union.1 hQW with h | h
    · exact Or.inl ⟨h, (hA.on W hW').cliqueEdges_subset h⟩
    · exact Or.inr ⟨h, (hA.off W hW').cliqueEdges_subset h⟩
  refine ⟨R ∪ 𝒲.sup A, 𝒲.sup (fun W => Qon W ∪ Qoff W), QA,
    ⟨fun e he => ⟨hX e he, subset_univ _⟩, fun e he => ⟨hAr e he, subset_univ _⟩,
      hQA.disjoint, fun Q hQ => ?_, hQA.subset_family, hQA.decomp⟩,
    subset_of_disjoint_compl hAr hAF, href, fun S hS => ?_, fun Q hQ => ?_⟩
  · obtain ⟨W, hW', h | h⟩ := hfam Q hQ
    · refine ⟨(hA.on W hW').card_eq Q h.1, h.2.trans ?_⟩
      intro e he
      rcases mem_union.1 he with h' | h'
      · exact mem_union_right _ (mem_union_right _ (mem_sup.2 ⟨W, hW', h'⟩))
      · rcases mem_union.1 (hR.subset W hW' h') with h'' | h''
        · exact mem_union_left _ h''
        · exact mem_union_right _ (mem_union_left _ h'')
    · refine ⟨(hA.off W hW').card_eq Q h.1, h.2.trans ?_⟩
      intro e he
      exact mem_union_right _ (mem_union_right _ (mem_sup.2 ⟨W, hW', he⟩))
  · refine (hW.degRA S hS).trans ?_
    have hM : 0 ≤ max D (budget n r) := le_max_of_le_right (budget_nonneg n r)
    push_cast
    nlinarith
  · obtain ⟨W, hW', h | h⟩ := hfam Q hQ
    · refine le_trans (card_le_card ?_) (hW.oneX W hW')
      intro e he
      rw [mem_filter] at he ⊢
      refine ⟨?_, he.2⟩
      rcases mem_union.1 (h.2 he.1) with h' | h'
      · exact absurd (mem_union_left _ he.2) (disjoint_left.1 (hA.disjoint W hW') h')
      · exact h'
    · have : (cliqueEdges r Q).filter (· ∈ X) = ∅ := by
        rw [filter_eq_empty_iff]
        intro e he heX
        exact disjoint_left.1 (hA.disjoint W hW') (h.2 he) (mem_union_left _ heX)
      rw [this]; simp

/-- **Theorem 1.7, `r ≥ 2`.** -/
theorem theorem_1_7_two_le {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) : Theorem_1_7_for q r := by
  obtain ⟨C, hC, ε, hε, h⟩ := theorem_1_7_strong_two_le (q := q) hr hrq
  refine ⟨C, hC, ε, hε, fun n G X D hG hδ hXG hXD hDn => ?_⟩
  obtain ⟨A, F, QA, h1, h2, h3, h4, -⟩ := h n G X D hG hδ hXG hXD hDn
  exact ⟨A, F, QA, h1, h2, h3, h4⟩

end RefinedAbsorption.Original2024
