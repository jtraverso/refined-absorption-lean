module
public import RefinedAbsorption.NibbleReserves

/-!
# Omni-absorbers from refined refiners and absorbers

The refined absorption proof of Theorem 1.10 (refined efficient omni-absorbers) has two parts:

1. build a *refined refiner* `R` of `X`: an `r`-graph edge-disjoint from `X` together with a
   fixed family `𝒲` of `K_q^r`-divisible subgraphs of `X ∪ R`, each of size at most `C` and with
   every edge in at most `C` of them, such that for every `K_q^r`-divisible `L ⊆ X` the graph
   `R ∪ L` is the edge-disjoint union of some members of `𝒲` (a refined version of
   Definition 3.5);
2. attach to every `W ∈ 𝒲` a `K_q^r`-absorber `A_W` (Definition 1.5), the `A_W` being pairwise
   edge-disjoint and edge-disjoint from `X ∪ R`.

This file proves the deterministic step that combines the two: `R ∪ ⋃_W A_W` is a
`2C`-refined `K_q^r`-omni-absorber for `X` (`omniAbsorber_of_refiner_absorbers`).  Hence
Theorem 1.10 follows from the
existence of refined refiners with attached absorbers of the right maximum degree
(`refinedEfficientOmniAbsorber_of_refinerWithAbsorbers`).  The construction of such refiners
(the core of the Delcourt–Postle proof) is not formalised here.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {V : Type*} [DecidableEq V]

/-- **Refined refiner.**  `R` is a `C`-refined `K_q^r`-refiner of `X` with family `𝒲` if `X`
and `R` are edge-disjoint `r`-graphs, `𝒲` is a family of `K_q^r`-divisible subgraphs of
`X ∪ R` of size at most `C`, every edge of `X ∪ R` lies in at most `C` members of `𝒲`, and for
every `K_q^r`-divisible `L ⊆ X` the graph `R ∪ L` is the union of pairwise edge-disjoint members
of `𝒲`. -/
structure IsRefinedRefiner (q r C : ℕ) (X R : Finset (Finset V))
    (𝒲 : Finset (Finset (Finset V))) : Prop where
  rgraph : IsRGraph r (X ∪ R)
  disjoint : Disjoint X R
  divisible : ∀ W ∈ 𝒲, IsDivisible q r W
  subset : ∀ W ∈ 𝒲, W ⊆ X ∪ R
  card_le : ∀ W ∈ 𝒲, W.card ≤ C
  mult_le : ∀ e ∈ X ∪ R, (𝒲.filter (fun W => e ∈ W)).card ≤ C
  decomp : ∀ L ⊆ X, IsDivisible q r L → ∃ 𝒰 ⊆ 𝒲,
    (𝒰 : Set (Finset (Finset V))).PairwiseDisjoint id ∧ 𝒰.sup id = R ∪ L

/-- **Attached absorbers.**  For every `W ∈ 𝒲`, `A W` is an `r`-graph such that `A W ∪ W`
and `A W` have the `K_q^r`-decompositions `Qon W` and `Qoff W`; the `A W` are pairwise
edge-disjoint and edge-disjoint from `X ∪ R`. -/
structure IsAttachedAbsorbers (q r : ℕ) (X R : Finset (Finset V))
    (𝒲 : Finset (Finset (Finset V))) (A Qon Qoff : Finset (Finset V) → Finset (Finset V)) :
    Prop where
  rgraph : ∀ W ∈ 𝒲, IsRGraph r (A W)
  disjoint : ∀ W ∈ 𝒲, Disjoint (A W) (X ∪ R)
  pairwise : ∀ W ∈ 𝒲, ∀ W' ∈ 𝒲, W ≠ W' → Disjoint (A W) (A W')
  on : ∀ W ∈ 𝒲, IsDecomposition q r (A W ∪ W) (Qon W)
  off : ∀ W ∈ 𝒲, IsDecomposition q r (A W) (Qoff W)

/-- The union of decompositions of pairwise edge-disjoint `r`-graphs is a decomposition of
their union (for `r ≤ q`). -/
theorem IsDecomposition.sup {q r : ℕ} (hrq : r ≤ q) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (G 𝒬 : ι → Finset (Finset V)) (hdisj : (s : Set ι).PairwiseDisjoint G)
    (h : ∀ i ∈ s, IsDecomposition q r (G i) (𝒬 i)) :
    IsDecomposition q r (s.sup G) (s.sup 𝒬) := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨fun e he => by simp at he, fun Q hQ => by simp at hQ, fun e _ => by simp [cliqueMult]⟩
  | insert a s has ih =>
    rw [sup_insert, sup_insert]
    have hdisj' : (s : Set ι).PairwiseDisjoint G :=
      hdisj.subset (by simp [Set.subset_insert])
    refine IsDecomposition.union hrq ?_ (h a (mem_insert_self _ _))
      (ih hdisj' fun i hi => h i (mem_insert_of_mem hi))
    rw [Finset.disjoint_sup_right]
    intro i hi
    exact hdisj (by simp) (by simp [hi]) (fun hai => has (hai ▸ hi))

/-- The number of cliques of `s.sup 𝒬` containing `e` is at most the sum over `i ∈ s`. -/
theorem cliqueMult_sup_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (𝒬 : ι → Finset (Finset V)) (e : Finset V) :
    cliqueMult (s.sup 𝒬) e ≤ ∑ i ∈ s, cliqueMult (𝒬 i) e := by
  induction s using Finset.induction_on with
  | empty => simp [cliqueMult]
  | insert a s has ih =>
    rw [sup_insert, sum_insert has]
    refine le_trans ?_ (Nat.add_le_add_left ih _)
    unfold cliqueMult
    rw [show (𝒬 a ⊔ s.sup 𝒬) = 𝒬 a ∪ s.sup 𝒬 from rfl, filter_union]
    exact card_union_le _ _

/-- **Refined refiner + attached absorbers ⇒ refined omni-absorber.**  If `R` is a
`C`-refined refiner of `X` with family `𝒲` (`C ≥ 1`) and `A W` are attached absorbers, then
`R ∪ ⋃_{W ∈ 𝒲} A W` is a `2C`-refined `K_q^r`-omni-absorber for `X`, with decomposition family
`⋃_{W ∈ 𝒲} (Qon W ∪ Qoff W)`. -/
theorem omniAbsorber_of_refiner_absorbers {q r C : ℕ} (hrq : r ≤ q) (hC : 1 ≤ C)
    {X R : Finset (Finset V)} {𝒲 : Finset (Finset (Finset V))}
    {A Qon Qoff : Finset (Finset V) → Finset (Finset V)}
    (hR : IsRefinedRefiner q r C X R 𝒲) (hA : IsAttachedAbsorbers q r X R 𝒲 A Qon Qoff) :
    ∃ QA, IsOmniAbsorber q r X (R ∪ 𝒲.sup A) (𝒲.sup (fun W => Qon W ∪ Qoff W)) QA ∧
      IsCRefined (2 * C) X (R ∪ 𝒲.sup A) (𝒲.sup (fun W => Qon W ∪ Qoff W)) := by
  have hU : ∀ L : Finset (Finset V), ∃ 𝒰 : Finset (Finset (Finset V)), L ⊆ X →
      IsDivisible q r L →
      𝒰 ⊆ 𝒲 ∧ (𝒰 : Set (Finset (Finset V))).PairwiseDisjoint id ∧ 𝒰.sup id = R ∪ L := by
    intro L
    by_cases h : L ⊆ X ∧ IsDivisible q r L
    · obtain ⟨𝒰, h1, h2, h3⟩ := hR.decomp L h.1 h.2
      exact ⟨𝒰, fun _ _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose 𝒰 h𝒰 using hU
  have hAW : ∀ W ∈ 𝒲, ∀ W' ∈ 𝒲, Disjoint (A W) W' := fun W hW W' hW' =>
    disjoint_of_subset_right (hR.subset W' hW') (hA.disjoint W hW)
  refine ⟨fun L => 𝒲.sup (fun W => if W ∈ 𝒰 L then Qon W else Qoff W), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact fun e he => hR.rgraph e (mem_union_left _ he)
  · rw [disjoint_union_right]
    refine ⟨hR.disjoint, ?_⟩
    rw [Finset.disjoint_sup_right]
    intro W hW
    exact (disjoint_of_subset_right subset_union_left (hA.disjoint W hW)).symm
  · intro L hL hdiv Q hQ
    obtain ⟨W, hW, hQW⟩ := mem_sup.1 hQ
    refine mem_sup.2 ⟨W, hW, ?_⟩
    split_ifs at hQW
    · exact mem_union_left _ hQW
    · exact mem_union_right _ hQW
  · intro L hL hdiv
    obtain ⟨h1, h2, h3⟩ := h𝒰 L hL hdiv
    have heq : 𝒲.sup (fun W => if W ∈ 𝒰 L then A W ∪ W else A W) = R ∪ 𝒲.sup A ∪ L := by
      ext e
      simp only [mem_sup, mem_union]
      constructor
      · rintro ⟨W, hW, he⟩
        split_ifs at he with hWU
        · rcases mem_union.1 he with he | he
          · exact Or.inl (Or.inr ⟨W, hW, he⟩)
          · have : e ∈ (𝒰 L).sup id := mem_sup.2 ⟨W, hWU, he⟩
            rw [h3] at this
            rcases mem_union.1 this with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
        · exact Or.inl (Or.inr ⟨W, hW, he⟩)
      · rintro ((he | ⟨W, hW, he⟩) | he)
        · have : e ∈ R ∪ L := mem_union_left _ he
          rw [← h3] at this
          obtain ⟨W, hW, he⟩ := mem_sup.1 this
          exact ⟨W, h1 hW, by rw [if_pos hW]; exact mem_union_right _ he⟩
        · exact ⟨W, hW, by split_ifs <;> simp [he]⟩
        · have : e ∈ R ∪ L := mem_union_right _ he
          rw [← h3] at this
          obtain ⟨W, hW, he⟩ := mem_sup.1 this
          exact ⟨W, h1 hW, by rw [if_pos hW]; exact mem_union_right _ he⟩
    rw [← heq]
    refine IsDecomposition.sup hrq 𝒲 _ _ ?_ ?_
    · intro W hW W' hW' hne
      simp only [Function.onFun]
      split_ifs with hU1 hU2 hU2
      · rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
        exact ⟨⟨hA.pairwise W hW W' hW' hne, hAW W hW W' hW'⟩,
          (hAW W' hW' W hW).symm, h2 hU1 hU2 hne⟩
      · rw [disjoint_union_left]
        exact ⟨hA.pairwise W hW W' hW' hne, (hAW W' hW' W hW).symm⟩
      · rw [disjoint_union_right]
        exact ⟨hA.pairwise W hW W' hW' hne, hAW W hW W' hW'⟩
      · exact hA.pairwise W hW W' hW' hne
    · intro W hW
      split_ifs
      · exact hA.on W hW
      · exact hA.off W hW
  · intro e he
    have hcard : e.card = r := by
      rcases mem_union.1 he with he | he
      · exact hR.rgraph e (mem_union_left _ he)
      rcases mem_union.1 he with he | he
      · exact hR.rgraph e (mem_union_right _ he)
      obtain ⟨W, hW, he⟩ := mem_sup.1 he
      exact hA.rgraph W hW e he
    have hterm : ∀ W ∈ 𝒲,
        cliqueMult (Qon W ∪ Qoff W) e ≤ 2 * (if e ∈ W ∪ A W then 1 else 0) := by
      intro W hW
      have h1 := (hA.on W hW).mult_eq e hcard
      have h2 := (hA.off W hW).mult_eq e hcard
      have hle : cliqueMult (Qon W ∪ Qoff W) e ≤
          cliqueMult (Qon W) e + cliqueMult (Qoff W) e := by
        unfold cliqueMult; rw [filter_union]; exact card_union_le _ _
      rw [h1, h2] at hle
      by_cases h : e ∈ W ∪ A W
      · rw [if_pos h]; split_ifs at hle <;> omega
      · rw [if_neg h]
        have : e ∉ A W ∪ W := by rw [union_comm]; exact h
        have h' : e ∉ A W := fun h'' => h (mem_union_right _ h'')
        rw [if_neg this, if_neg h'] at hle; omega
    have hsum : cliqueMult (𝒲.sup (fun W => Qon W ∪ Qoff W)) e ≤
        2 * (𝒲.filter (fun W => e ∈ W ∪ A W)).card := by
      refine (cliqueMult_sup_le 𝒲 _ e).trans ?_
      refine (sum_le_sum hterm).trans ?_
      rw [← mul_sum, card_filter]
    refine hsum.trans (Nat.mul_le_mul_left 2 ?_)
    by_cases hXR : e ∈ X ∪ R
    · refine le_trans (card_le_card ?_) (hR.mult_le e hXR)
      intro W hW
      rw [mem_filter] at hW ⊢
      refine ⟨hW.1, ?_⟩
      rcases mem_union.1 hW.2 with h | h
      · exact h
      · exact absurd hXR (disjoint_left.1 (hA.disjoint W hW.1) h)
    · have heA : e ∈ 𝒲.sup A := by
        rcases mem_union.1 he with h | h
        · exact absurd (mem_union_left _ h) hXR
        rcases mem_union.1 h with h | h
        · exact absurd (mem_union_right _ h) hXR
        · exact h
      obtain ⟨W₀, hW₀, heW₀⟩ := mem_sup.1 heA
      refine le_trans (card_le_card (t := {W₀}) ?_) (by simpa using hC)
      intro W hW
      rw [mem_filter] at hW
      rw [mem_singleton]
      by_contra hne
      rcases mem_union.1 hW.2 with h | h
      · exact hXR (hR.subset W hW.1 h)
      · exact disjoint_left.1 (hA.pairwise W hW.1 W₀ hW₀ hne) h heW₀

/-- **Refined refiners with attached absorbers** (the two constructive steps of the proof of
Theorem 1.10, stated here, not proved).  For `q > r ≥ 1` there is `C ≥ 1` such that: if
`X ⊆ K_n^r` has `Δ_{r-1}(X) ≤ D ≤ n / C`, then there are a `C`-refined `K_q^r`-refiner `R` of
`X` with family `𝒲` and attached absorbers `A W` (`W ∈ 𝒲`) such that
`R ∪ ⋃_W A W` has maximum `(r-1)`-degree at most `C · max(D, n^{1-1/r} log n)`. -/
def RefinerWithAbsorbers : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, ∀ X : Finset (Finset (Fin n)),
    ∀ D : ℝ, IsRGraph r X → MaxDegLE r X D → D ≤ n / C →
      ∃ (R : Finset (Finset (Fin n))) (𝒲 : Finset (Finset (Finset (Fin n))))
        (A Qon Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
        IsRefinedRefiner q r C X R 𝒲 ∧ IsAttachedAbsorbers q r X R 𝒲 A Qon Qoff ∧
          MaxDegLE r (R ∪ 𝒲.sup A) (C * max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n))

/-- **Theorem 1.10 from refined refiners with attached absorbers.** -/
theorem refinedEfficientOmniAbsorber_of_refinerWithAbsorbers (h : RefinerWithAbsorbers) :
    RefinedEfficientOmniAbsorber := by
  intro q r hr hrq
  obtain ⟨C, hC, hC'⟩ := h q r hr hrq
  refine ⟨2 * C, by omega, fun n X D hX hXD hDn => ?_⟩
  have hC0 : (0 : ℝ) < C := by exact_mod_cast hC
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hDn' : D ≤ n / C := by
    refine hDn.trans (div_le_div_of_nonneg_left hn0 hC0 ?_)
    push_cast; linarith
  obtain ⟨R, 𝒲, A, Qon, Qoff, hR, hA, hdeg⟩ := hC' n X D hX hXD hDn'
  obtain ⟨QA, hQA, href⟩ := omniAbsorber_of_refiner_absorbers hrq.le hC hR hA
  refine ⟨_, _, QA, hQA, href, fun S hS => (hdeg S hS).trans ?_⟩
  have hM : 0 ≤ max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n) :=
    le_max_of_le_right (mul_nonneg (by positivity) (Real.log_natCast_nonneg n))
  push_cast
  nlinarith

/-- **The Existence Conjecture for Steiner systems** from refined refiners with attached
absorbers (which give Theorem 1.10) and the nibble with leftover degree control (which gives
Corollary 2.4). -/
theorem steinerExistence_of_refinerWithAbsorbers_nibbleLeftoverDegree
    (hRef : RefinerWithAbsorbers) (hNib : NibbleLeftoverDegree) : SteinerExistenceConjecture :=
  steinerExistence_of_omniAbsorber_nibbleLeftoverDegree
    (refinedEfficientOmniAbsorber_of_refinerWithAbsorbers hRef) hNib

end RefinedAbsorption
