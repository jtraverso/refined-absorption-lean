module
public import RequestProject.Faithful2024.Transport
public import RequestProject.Original2024.Final

/-!
# Theorems 1.7 and 1.11 of arXiv:2402.17855v1, faithful form

**`theorem_1_7 : Theorem_1_7`** and **`theorem_1_11 : Theorem_1_11`** (statements in
`Faithful2024/Defs.lean`).  They are derived from the existing results
`Original2024.theorem_1_7_strong` and `Original2024.theorem_1_11_strong` by proved adapters:

1. `isCliqueDecomposition_of_isDecomposition`: a `K_q^r`-decomposition in the sense of the
   project (`IsDecomposition`: every edge in exactly one clique, no other `r`-set covered) is a set
   of pairwise edge-disjoint cliques whose union is the graph (the wording of Definition 1.5).
2. `theorem_1_7_fin`, `theorem_1_11_fin`: the faithful statements on the vertex type `Fin n` with
   `V(G) = Fin n`; here `Δ(X)` is the real maximum degree, so the `D`-form of the existing
   statements is used with `D = Δ(X)`.  The extra outputs `OneXEdgePerClique` (resp.
   `OneXEdgePerPiece`) of the strong forms are exactly the conditions `|H ∩ X| ≤ 1` of
   Definitions 1.5 and 1.8, and the family degree bound of `Theorem_1_11_strong_for` is the
   refinement degree `Δ(𝓗)` of Definition 1.10.
3. Transport (`Faithful2024/Transport.lean`) to an arbitrary vertex type: every hypergraph on `n`
   vertices is the image of one on `Fin n`.
-/

@[expose] public section

namespace RefinedAbsorption.Faithful2024

open Finset

section Adapters

variable {V : Type*} [DecidableEq V]

theorem isCliqueDecomposition_of_isDecomposition {q r : ℕ} {G 𝒬 : Finset (Finset V)}
    (h : IsDecomposition q r G 𝒬) : IsCliqueDecomposition q r G 𝒬 := by
  refine ⟨h.card_eq, ?_, ?_⟩
  · intro Q₁ hQ₁ Q₂ hQ₂ hne
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    rw [cliqueEdges, mem_powersetCard] at he₁ he₂
    have hm := h.mult_eq e he₁.2
    have h2 : 2 ≤ cliqueMult 𝒬 e := by
      unfold cliqueMult
      have : ({Q₁, Q₂} : Finset (Finset V)) ⊆ 𝒬.filter (fun Q => e ⊆ Q) := by
        intro Q hQ
        rcases mem_insert.1 hQ with rfl | hQ
        · exact mem_filter.2 ⟨hQ₁, he₁.1⟩
        · rw [mem_singleton.1 hQ]; exact mem_filter.2 ⟨hQ₂, he₂.1⟩
      have := card_le_card this
      rwa [card_pair hne] at this
    split_ifs at hm <;> omega
  · ext e
    rw [mem_biUnion]
    constructor
    · rintro ⟨Q, hQ, he⟩
      rw [cliqueEdges, mem_powersetCard] at he
      have hm := h.mult_eq e he.2
      have h1 : 1 ≤ cliqueMult 𝒬 e :=
        card_pos.2 ⟨Q, mem_filter.2 ⟨hQ, he.1⟩⟩
      split_ifs at hm with hG
      · exact hG
      · omega
    · intro he
      have hr := h.rgraph e he
      have hm := h.mult_eq e hr
      rw [if_pos he] at hm
      obtain ⟨Q, hQ⟩ := card_pos.1 (by rw [← cliqueMult]; omega : 0 < (𝒬.filter fun Q => e ⊆ Q).card)
      obtain ⟨hQ𝒬, heQ⟩ := mem_filter.1 hQ
      exact ⟨Q, hQ𝒬, by rw [cliqueEdges, mem_powersetCard]; exact ⟨heQ, hr⟩⟩

end Adapters

section FinN

variable {n : ℕ}

theorem le_maxDeg {r : ℕ} (hr : 1 ≤ r) (G : HGraph (Fin n)) (hG : G.verts = univ) :
    MaxDegLE r G.edges (G.maxDeg r) := by
  intro S hS
  have hS' : S ∈ G.verts.powersetCard (r - 1) := by
    rw [hG, mem_powersetCard]; exact ⟨subset_univ _, by omega⟩
  exact_mod_cast le_sup (f := deg G.edges) hS'

theorem maxDeg_le_of {r : ℕ} (hr : 1 ≤ r) (G : HGraph (Fin n)) {D : ℝ} (hD : 0 ≤ D)
    (h : MaxDegLE r G.edges D) : (G.maxDeg r : ℝ) ≤ D := by
  unfold HGraph.maxDeg
  rcases (G.verts.powersetCard (r - 1)).eq_empty_or_nonempty with he | hne
  · rw [he, sup_empty]; simpa using hD
  · obtain ⟨S, hS, hSeq⟩ := exists_mem_eq_sup _ hne (deg G.edges)
    rw [hSeq]
    exact h S (by rw [mem_powersetCard] at hS; omega)

theorem minDegGE_old {r : ℕ} (G : HGraph (Fin n)) (hG : G.verts = univ) {D : ℝ}
    (h : G.MinDegGE r D) : MinDegGE r G.edges D :=
  fun S hS => h S (by rw [hG]; exact subset_univ _) hS

theorem isRGraph_of_isUniform {r : ℕ} {G : HGraph (Fin n)} (h : G.IsUniform r) :
    IsRGraph r G.edges := fun e he => (h e he).1

/-- **Theorem 1.7 on `Fin n`** (faithful form, `V(G) = Fin n`). -/
theorem theorem_1_7_fin (q r : ℕ) (hr : 1 ≤ r) (hrq : r < q) :
    ∃ C : ℕ, 1 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ (n : ℕ) (G X : HGraph (Fin n)),
      G.verts = univ → G.IsUniform r → G.MinDegGE r ((1 - ε) * n) →
      X.IsSpanningSubgraph G → (X.maxDeg r : ℝ) ≤ n / C →
      ∃ (A : HGraph (Fin n)) (𝓗 : Finset (Finset (Fin n)))
        (QA : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
        IsOmniAbsorber q r X A 𝓗 QA ∧ IsCRefinedOmni r C X A 𝓗 ∧ A.IsSubgraph G ∧
        (A.maxDeg r : ℝ) ≤ C * max (X.maxDeg r : ℝ) (budget n r) := by
  obtain ⟨C, hC, ε, hε, h⟩ := Original2024.theorem_1_7_strong q r hr hrq
  refine ⟨C, hC, min ε (1 / 2), lt_min hε (by norm_num), by
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro n G X hGv hGu hδ hXG hXD
  have hXv : X.verts = univ := hXG.1.trans hGv
  have hδ' : MinDegGE r G.edges ((1 - ε) * n) := by
    intro S hS
    refine le_trans ?_ (minDegGE_old G hGv hδ S hS)
    have : min ε (1 / 2) ≤ ε := min_le_left _ _
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  obtain ⟨A, F, QA, hom, hAG, href, hdeg, hone⟩ := h n G.edges X.edges (X.maxDeg r)
    (isRGraph_of_isUniform hGu) hδ' hXG.2 (le_maxDeg hr X hXv) hXD
  refine ⟨⟨univ, A⟩, F, QA, ?_, ?_, ⟨by rw [hGv], hAG⟩, ?_⟩
  · refine ⟨fun e _ => by rw [hXv]; exact subset_univ _, fun e _ => subset_univ _,
      hXv, hom.disjoint, hom.family, hone, hom.subset_family, fun L hL hdiv => ?_⟩
    have := isCliqueDecomposition_of_isDecomposition (hom.decomp L hL hdiv)
    rwa [union_comm] at this
  · intro e he
    have her : e.card = r := by
      rcases mem_union.1 he with he | he
      · exact (hGu e (hXG.2 he)).1
      · exact (hGu e (hAG he)).1
    refine le_trans (le_of_eq ?_) (href e he)
    unfold cliqueMult
    congr 1
    apply filter_congr
    intro Q _
    rw [cliqueEdges, mem_powersetCard]
    exact ⟨fun h => h.1, fun h => ⟨h, her⟩⟩
  · refine maxDeg_le_of hr ⟨univ, A⟩ ?_ hdeg
    have : (0 : ℝ) ≤ X.maxDeg r := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ max (X.maxDeg r : ℝ) (budget n r) := le_max_of_le_left this
    positivity

theorem refDegree_le_of {r : ℕ} (hr : 1 ≤ r) (R : HGraph (Fin n))
    (𝓗 : Finset (Finset (Finset (Fin n)))) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ S : Finset (Fin n), S.card + 1 = r →
      ((𝓗.filter fun H => S ⊆ vertexSet H).card : ℝ) ≤ D) :
    (refDegree r R 𝓗 : ℝ) ≤ D := by
  unfold refDegree
  rcases (R.verts.powersetCard (r - 1)).eq_empty_or_nonempty with he | hne
  · rw [he, sup_empty]; simpa using hD
  · obtain ⟨S, hS, hSeq⟩ := exists_mem_eq_sup _ hne
      (fun S => (𝓗.filter fun H => S ⊆ vertexSet H).card)
    rw [hSeq]
    exact h S (by rw [mem_powersetCard] at hS; omega)

/-- **Theorem 1.11 on `Fin n`** (faithful form, `V(G) = Fin n`). -/
theorem theorem_1_11_fin (q r : ℕ) (hr : 1 ≤ r) (hrq : r < q) :
    ∃ C : ℕ, 1 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ (n : ℕ) (G X : HGraph (Fin n)),
      G.verts = univ → G.IsUniform r → G.MinDegGE r ((1 - ε) * n) →
      X.IsSpanningSubgraph G → (X.maxDeg r : ℝ) ≤ n / C →
      ∃ (R : HGraph (Fin n)) (𝓗 : Finset (Finset (Finset (Fin n))))
        (QR : Finset (Finset (Fin n)) → Finset (Finset (Finset (Fin n)))),
        IsRefiner q r X R 𝓗 QR ∧ IsCRefinedRefiner C X R 𝓗 ∧ R.IsSubgraph G ∧
        (refDegree r R 𝓗 : ℝ) ≤ C * max (X.maxDeg r : ℝ) (budget n r) := by
  obtain ⟨C, hC, ε, hε, h⟩ := Original2024.theorem_1_11_strong q r hr hrq
  refine ⟨C, hC, min ε (1 / 2), lt_min hε (by norm_num), by
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro n G X hGv hGu hδ hXG hXD
  have hXv : X.verts = univ := hXG.1.trans hGv
  have hδ' : MinDegGE r G.edges ((1 - ε) * n) := by
    intro S hS
    refine le_trans ?_ (minDegGE_old G hGv hδ S hS)
    have : min ε (1 / 2) ≤ ε := min_le_left _ _
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  obtain ⟨R, F, QR, href, hRG, hcr, -, hone, hfam⟩ := h n G.edges X.edges (X.maxDeg r)
    (isRGraph_of_isUniform hGu) hδ' hXG.2 (le_maxDeg hr X hXv) hXD
  refine ⟨⟨univ, R⟩, F, QR, ?_, ⟨hcr.mult_le, hcr.vert_le, hcr.card_le⟩, ⟨by rw [hGv], hRG⟩, ?_⟩
  · refine ⟨fun e he => ⟨(hGu e (hXG.2 he)).1, by rw [hXv]; exact subset_univ _⟩,
      fun e he => ⟨(hGu e (hRG he)).1, subset_univ _⟩, hXv, href.disjoint, href.family, hone,
      href.subset_family, href.pairwise, fun L hL hd => by rw [href.cover L hL hd, union_comm]⟩
  · refine refDegree_le_of hr ⟨univ, R⟩ F ?_ hfam
    have : (0 : ℝ) ≤ X.maxDeg r := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ max (X.maxDeg r : ℝ) (budget n r) := le_max_of_le_left this
    positivity

end FinN

/-! ### Arbitrary vertex type -/

section General

variable {α : Type} [DecidableEq α]

theorem HGraph.wf_of_isUniform {r : ℕ} {G : HGraph α} (h : G.IsUniform r) : G.WF :=
  fun e he => (h e he).2

theorem HGraph.wf_of_spanning {r : ℕ} {X G : HGraph α} (hG : G.IsUniform r)
    (h : X.IsSpanningSubgraph G) : X.WF :=
  fun e he => h.1 ▸ (hG e (h.2 he)).2

/-- **Theorem 1.7 of arXiv:2402.17855v1 (Refined Omni-Absorber Theorem)**, faithful form. -/
theorem theorem_1_7 : Theorem_1_7 := by
  intro q r hr hrq
  obtain ⟨C, hC, ε, hε, hε1, h⟩ := theorem_1_7_fin q r hr hrq
  refine ⟨C, hC, ε, hε, hε1, ?_⟩
  intro α _ G X hGu hδ hXG hXD
  set s := G.verts with hs
  have hGm : (pullback s G).map (finEmb s) = G := pullback_map (HGraph.wf_of_isUniform hGu) rfl
  have hXm : (pullback s X).map (finEmb s) = X :=
    pullback_map (HGraph.wf_of_spanning hGu hXG) hXG.1
  have hcard : (pullback s G).verts.card = s.card := pullback_card s G
  rw [← hGm] at hGu hδ
  rw [← hGm, ← hXm] at hXG
  rw [← hXm] at hXD
  rw [HGraph.isUniform_map_iff] at hGu
  rw [HGraph.minDegGE_map_iff] at hδ
  rw [HGraph.isSpanningSubgraph_map_iff] at hXG
  rw [HGraph.maxDeg_map] at hXD
  obtain ⟨A, 𝓗, QA, h1, h2, h3, h4⟩ := h s.card (pullback s G) (pullback s X) rfl hGu hδ hXG hXD
  refine ⟨A.map (finEmb s), 𝓗.map (mf (finEmb s)),
    fun L => (QA (pullFam (finEmb s) (pullback s X).edges L)).map (mf (finEmb s)), ?_, ?_, ?_, ?_⟩
  · have := isOmniAbsorber_map (finEmb s) h1; rwa [hXm] at this
  · have := isCRefinedOmni_map (finEmb s) h2; rwa [hXm] at this
  · have := HGraph.isSubgraph_map (finEmb s) h3; rwa [hGm] at this
  · rw [HGraph.maxDeg_map, ← hXm, HGraph.maxDeg_map]
    exact h4

/-- **Theorem 1.11 of arXiv:2402.17855v1 (Refiner Theorem)**, faithful form: the bound is on the
refinement degree `Δ(𝓗)` of the family. -/
theorem theorem_1_11 : Theorem_1_11 := by
  intro q r hr hrq
  obtain ⟨C, hC, ε, hε, hε1, h⟩ := theorem_1_11_fin q r hr hrq
  refine ⟨C, hC, ε, hε, hε1, ?_⟩
  intro α _ G X hGu hδ hXG hXD
  set s := G.verts with hs
  have hGm : (pullback s G).map (finEmb s) = G := pullback_map (HGraph.wf_of_isUniform hGu) rfl
  have hXm : (pullback s X).map (finEmb s) = X :=
    pullback_map (HGraph.wf_of_spanning hGu hXG) hXG.1
  have hcard : (pullback s G).verts.card = s.card := pullback_card s G
  rw [← hGm] at hGu hδ
  rw [← hGm, ← hXm] at hXG
  rw [← hXm] at hXD
  rw [HGraph.isUniform_map_iff] at hGu
  rw [HGraph.minDegGE_map_iff] at hδ
  rw [HGraph.isSpanningSubgraph_map_iff] at hXG
  rw [HGraph.maxDeg_map] at hXD
  obtain ⟨R, 𝓗, QR, h1, h2, h3, h4⟩ := h s.card (pullback s G) (pullback s X) rfl hGu hδ hXG hXD
  refine ⟨R.map (finEmb s), 𝓗.map (mf2 (finEmb s)),
    fun L => (QR (pullFam (finEmb s) (pullback s X).edges L)).map (mf2 (finEmb s)), ?_, ?_, ?_, ?_⟩
  · have := isRefiner_map (finEmb s) h1; rwa [hXm] at this
  · unfold IsCRefinedRefiner at h2 ⊢
    have := isCRefinedFamily_map (finEmb s) h2
    rw [map_union] at this
    rw [← hXm]
    exact this
  · have := HGraph.isSubgraph_map (finEmb s) h3; rwa [hGm] at this
  · rw [refDegree_map, ← hXm, HGraph.maxDeg_map]
    exact h4

end General

end RefinedAbsorption.Faithful2024
