module
public import RequestProject.MultiRefiner.Reduction

/-!
# The anti-edge refine-down step

This is the basic move of the refine-down construction (mathematics: M. Delcourt and
L. Postle, arXiv:2402.17855).  For every copy `e` of a labelled multigraph `X` we take

* an anti-edge `A_e = K_q^r(e ∪ T_e) - e` on `q - r` new vertices `T_e`, and
* a fake edge `F_e` (`N - 1` further anti-edges on new vertices), which behaves like `e` for
  divisibility (`fakeEdge_deg_cast`).

The pieces are `P_e = {e} ∪ A_e` (a `q`-clique) and `Q_e = A_e ∪ F_e` (divisible since
`A_e ≡ -e` and `F_e ≡ e`).  For a divisible `L ⊆ X` we use `P_e` for `e ∈ L` and `Q_e` for
`e ∉ L`; what is left is the residue `⋃_{e ∈ L} F_e`, which is divisible because `F_e ≡ e`.
Hence `R = ⋃_e (A_e ∪ F_e)` is a residual multi-refiner of `X` with residue in `Y = ⋃_e F_e`
(`antiEdgeStep`).  Every piece contains at most one copy of `X`, every copy lies in at most two
pieces, and every new edge carries a new vertex tagged by its copy (`antiE_tag`, `fakeE_tag`).

The new vertices are abstract here (tagged by the copy); placing them inside `K_n^r` is the job of
the Partial Clique Embedding Lemma.
-/

@[expose] public section

namespace RefinedAbsorption.RefineDown

open Finset RefinedAbsorption.MultiRefiner

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- The vertex type of the step: old vertices and new vertices tagged by `inl e` (the anti-edge
of `e`) or `inr e` (the fake edge of `e`). -/
abbrev SV (V E : Type*) (q r : ℕ) := XV V (E ⊕ E) q r

/-- The copy-label type of the step: the copies of `X`, and the new edges. -/
abbrev SC (V E : Type*) (q r : ℕ) := E ⊕ Finset (SV V E q r)

instance instDecidableEqSC (q r : ℕ) : DecidableEq (SC V E q r) :=
  @instDecidableEqSum _ _ _ (inferInstance : DecidableEq (Finset (SV V E q r)))

variable (q r : ℕ) (ends : E → Finset V)

/-- Both tags of a copy have the same root edge. -/
def ends2 : E ⊕ E → Finset V := Sum.elim ends ends

/-- The lift of the copy `i`. -/
def liftE (i : E) : Finset (SV V E q r) := lift q r (ends2 ends) (Sum.inl i)

/-- The ends of the copies of the step. -/
def sends : SC V E q r → Finset (SV V E q r) := Sum.elim (liftE q r ends) id

/-- The anti-edge `A_e` (index `j₀`). -/
def antiE (j₀ : Fin (fakeCount q r)) (i : E) : Finset (Finset (SV V E q r)) :=
  antiPiece q r (ends2 ends) (Sum.inl i) j₀

/-- The fake edge `F_e`. -/
def fakeE (i : E) : Finset (Finset (SV V E q r)) :=
  fakeEdge q r (ends2 ends) (Sum.inr i)

/-- The piece `P_e = {e} ∪ A_e`. -/
def pieceP (j₀ : Fin (fakeCount q r)) (i : E) : Finset (SC V E q r) :=
  insert (Sum.inl i : SC V E q r) ((antiE q r ends j₀ i).map Function.Embedding.inr)

/-- The piece `Q_e = A_e ∪ F_e`. -/
def pieceQ (j₀ : Fin (fakeCount q r)) (i : E) : Finset (SC V E q r) :=
  (antiE q r ends j₀ i ∪ fakeE q r ends i).map Function.Embedding.inr

/-- The refiner of the step. -/
def stepR (j₀ : Fin (fakeCount q r)) (X : Finset E) : Finset (SC V E q r) :=
  (X.biUnion fun i => antiE q r ends j₀ i ∪ fakeE q r ends i).map Function.Embedding.inr

/-- The residue set of the step. -/
def stepY (X : Finset E) : Finset (SC V E q r) :=
  (X.biUnion fun i => fakeE q r ends i).map Function.Embedding.inr

/-- The family of pieces of the step. -/
def stepW (j₀ : Fin (fakeCount q r)) (X : Finset E) : Finset (Finset (SC V E q r)) :=
  X.image (pieceP q r ends j₀) ∪ X.image (pieceQ q r ends j₀)

variable {q r ends}

omit [DecidableEq V] [DecidableEq E] in
theorem liftE_eq_inr (i : E) : liftE q r ends i = lift q r (ends2 ends) (Sum.inr i) := rfl

omit [DecidableEq V] [DecidableEq E] in
theorem card_liftE (i : E) : (liftE q r ends i).card = (ends i).card := card_map _

theorem mdeg_map_inr (G : Finset (Finset (SV V E q r))) (S : Finset (SV V E q r)) :
    mdeg (sends q r ends) (G.map Function.Embedding.inr) S = deg G S := by
  unfold mdeg deg
  rw [filter_map, card_map]
  rfl

theorem mdeg_map_inl (L : Finset E) (S : Finset (SV V E q r)) :
    mdeg (sends q r ends) (L.map Function.Embedding.inl) S =
      (L.filter fun i => S ⊆ liftE q r ends i).card := by
  unfold mdeg
  rw [filter_map, card_map]
  rfl

/-- New edges carry their tag. -/
theorem antiE_tag {j₀ : Fin (fakeCount q r)} {i : E} (hi : (ends i).card = r)
    {f : Finset (SV V E q r)} (hf : f ∈ antiE q r ends j₀ i) :
    ∃ t, (Sum.inr (Sum.inl i, j₀, t) : SV V E q r) ∈ f :=
  antiPiece_exists_fresh (ends := ends2 ends) (i := Sum.inl i) hi hf

theorem fakeE_tag {i : E} (hi : (ends i).card = r) {f : Finset (SV V E q r)}
    (hf : f ∈ fakeE q r ends i) : ∃ j t, (Sum.inr (Sum.inr i, j, t) : SV V E q r) ∈ f :=
  fakeEdge_exists_fresh (ends := ends2 ends) (i := Sum.inr i) hi hf

theorem antiE_disj_fakeE (j₀ : Fin (fakeCount q r)) {i : E} (hi : (ends i).card = r) (i' : E) :
    Disjoint (antiE q r ends j₀ i) (fakeE q r ends i') := by
  rw [disjoint_left]
  intro f hf hf'
  obtain ⟨t, ht⟩ := antiE_tag hi hf
  have := fakeEdge_fresh_tag (ends := ends2 ends) hf' ht
  exact Sum.inl_ne_inr this

theorem antiE_disj_antiE (j₀ : Fin (fakeCount q r)) {i i' : E} (hi : (ends i).card = r)
    (hne : i ≠ i') : Disjoint (antiE q r ends j₀ i) (antiE q r ends j₀ i') := by
  rw [disjoint_left]
  intro f hf hf'
  obtain ⟨t, ht⟩ := antiE_tag hi hf
  have := (antiPiece_fresh_tag (ends := ends2 ends) hf' ht).1
  exact hne (Sum.inl_injective this)

theorem fakeE_disj_fakeE {i i' : E} (hi : (ends i).card = r) (hne : i ≠ i') :
    Disjoint (fakeE q r ends i) (fakeE q r ends i') := by
  rw [disjoint_left]
  intro f hf hf'
  obtain ⟨j, t, ht⟩ := fakeE_tag hi hf
  have := fakeEdge_fresh_tag (ends := ends2 ends) hf' ht
  exact hne (Sum.inr_injective this)

theorem antiE_card_edge {j₀ : Fin (fakeCount q r)} {i : E} {f : Finset (SV V E q r)}
    (hf : f ∈ antiE q r ends j₀ i) : f.card = r :=
  (mem_powersetCard.1 (mem_sdiff.1 hf).1).2

/-- `P_e` is divisible: it is a `q`-clique. -/
theorem divisible_pieceP (hrq : r ≤ q) (j₀ : Fin (fakeCount q r)) {i : E}
    (hi : (ends i).card = r) : MIsDivisible q r (sends q r ends) (pieceP q r ends j₀ i) := by
  intro S hS
  have hnot : (Sum.inl i : SC V E q r) ∉ (antiE q r ends j₀ i).map Function.Embedding.inr := by
    simp
  rw [pieceP, mdeg, filter_insert]
  have key := deg_antiPiece_add (q := q) (ends := ends2 ends) (i := Sum.inl i) hi j₀ S
  have hclique := choose_dvd_deg_cliqueEdges (q := q) (r := r)
    (Q := fakeClique q r (ends2 ends) (Sum.inl i) j₀) (S := S)
    (card_fakeClique (ends := ends2 ends) (i := Sum.inl i) hrq hi j₀) hS.le
  have hm : ((antiE q r ends j₀ i).map Function.Embedding.inr).filter
      (fun c => S ⊆ sends q r ends c) = ((antiE q r ends j₀ i).filter (S ⊆ ·)).map
        Function.Embedding.inr := by
    rw [filter_map]; rfl
  split_ifs with hS'
  · rw [card_insert_of_notMem (fun h => hnot (mem_filter.1 h).1), hm, card_map]
    have : S ⊆ lift q r (ends2 ends) (Sum.inl i) := hS'
    rw [if_pos this] at key
    rw [← key] at hclique
    exact hclique
  · rw [hm, card_map]
    have : ¬ S ⊆ lift q r (ends2 ends) (Sum.inl i) := hS'
    rw [if_neg this, add_zero] at key
    rw [← key] at hclique
    exact hclique

/-- `Q_e` is divisible: `A_e ≡ -e` and `F_e ≡ e`. -/
theorem divisible_pieceQ (hrq : r ≤ q) (j₀ : Fin (fakeCount q r)) {i : E}
    (hi : (ends i).card = r) : MIsDivisible q r (sends q r ends) (pieceQ q r ends j₀ i) := by
  intro S hS
  rw [pieceQ, mdeg_map_inr, ← ZMod.natCast_eq_zero_iff]
  have hdisj := antiE_disj_fakeE (ends := ends) j₀ hi i
  have hdeg : deg (antiE q r ends j₀ i ∪ fakeE q r ends i) S =
      deg (antiE q r ends j₀ i) S + deg (fakeE q r ends i) S := by
    unfold deg; rw [filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj)]
  have key := congrArg (fun n : ℕ => (n : ZMod ((q - S.card).choose (r - S.card))))
    (deg_antiPiece_add (q := q) (ends := ends2 ends) (i := Sum.inl i) hi j₀ S)
  have hcl : ((deg (cliqueEdges r (fakeClique q r (ends2 ends) (Sum.inl i) j₀)) S : ℕ) :
      ZMod ((q - S.card).choose (r - S.card))) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (choose_dvd_deg_cliqueEdges (card_fakeClique (ends := ends2 ends) (i := Sum.inl i) hrq hi j₀) hS.le)
  have hF := fakeEdge_deg_cast (ends := ends2 ends) (i := Sum.inr i) hrq hi hS
  simp only [Nat.cast_add, hcl] at key
  rw [hdeg, Nat.cast_add]
  unfold antiE fakeE
  rw [hF]
  change ((deg (antiPiece q r (ends2 ends) (Sum.inl i) j₀) S : ℕ) :
      ZMod ((q - S.card).choose (r - S.card))) +
      (if S ⊆ lift q r (ends2 ends) (Sum.inl i) then 1 else 0) = 0
  split_ifs at key ⊢ <;> push_cast at key ⊢ <;> linear_combination key

theorem card_antiE_le (hrq : r ≤ q) (j₀ : Fin (fakeCount q r)) {i : E} (hi : (ends i).card = r) :
    (antiE q r ends j₀ i).card ≤ q.choose r := by
  refine (card_le_card sdiff_subset).trans ?_
  rw [cliqueEdges, card_powersetCard,
    card_fakeClique (ends := ends2 ends) (i := Sum.inl i) hrq hi j₀]

theorem mem_pieceP_inr {j₀ : Fin (fakeCount q r)} {i : E} {f : Finset (SV V E q r)} :
    (Sum.inr f : SC V E q r) ∈ pieceP q r ends j₀ i ↔ f ∈ antiE q r ends j₀ i := by
  simp [pieceP]

theorem mem_pieceP_inl {j₀ : Fin (fakeCount q r)} {i i' : E} :
    (Sum.inl i' : SC V E q r) ∈ pieceP q r ends j₀ i ↔ i' = i := by
  simp [pieceP]

theorem mem_pieceQ_inr {j₀ : Fin (fakeCount q r)} {i : E} {f : Finset (SV V E q r)} :
    (Sum.inr f : SC V E q r) ∈ pieceQ q r ends j₀ i ↔
      f ∈ antiE q r ends j₀ i ∨ f ∈ fakeE q r ends i := by
  simp [pieceQ]

theorem not_mem_pieceQ_inl {j₀ : Fin (fakeCount q r)} {i i' : E} :
    (Sum.inl i' : SC V E q r) ∉ pieceQ q r ends j₀ i := by
  simp [pieceQ]

/-- The new edges of different copies are different. -/
theorem eq_of_mem_new {j₀ : Fin (fakeCount q r)} {i i' : E} (hi : (ends i).card = r)
    (hi' : (ends i').card = r) {f : Finset (SV V E q r)}
    (hf : f ∈ antiE q r ends j₀ i ∨ f ∈ fakeE q r ends i)
    (hf' : f ∈ antiE q r ends j₀ i' ∨ f ∈ fakeE q r ends i') : i = i' := by
  by_contra hne
  rcases hf with hf | hf <;> rcases hf' with hf' | hf'
  · exact disjoint_left.1 (antiE_disj_antiE j₀ hi hne) hf hf'
  · exact disjoint_left.1 (antiE_disj_fakeE j₀ hi i') hf hf'
  · exact disjoint_left.1 (antiE_disj_fakeE j₀ hi' i) hf' hf
  · exact disjoint_left.1 (fakeE_disj_fakeE hi hne) hf hf'

/-- The decomposition property of the anti-edge step: for a divisible `L ⊆ X` use `P_e` on
`L`, `Q_e` off `L`, and the residue `⋃_{e ∈ L} F_e`. -/
theorem antiEdgeStep_decomp (hrq : r < q) (j₀ : Fin (fakeCount q r)) (X : Finset E)
    (hX : ∀ i ∈ X, (ends i).card = r) :
    ∀ L ⊆ X.map Function.Embedding.inl, MIsDivisible q r (sends q r ends) L →
      ∃ 𝒰 ⊆ stepW q r ends j₀ X, ∃ Res ⊆ stepY q r ends X,
        MIsDivisible q r (sends q r ends) Res ∧ (𝒰 : Set (Finset (SC V E q r))).PairwiseDisjoint id ∧
          Disjoint (𝒰.sup id) Res ∧ 𝒰.sup id ∪ Res = stepR q r ends j₀ X ∪ L := by
  classical
  intro L hL hLdiv
  set L' := X.filter fun i => (Sum.inl i : SC V E q r) ∈ L with hL'
  have hL'X : L' ⊆ X := filter_subset _ _
  have hinlL : ∀ i, (Sum.inl i : SC V E q r) ∈ L ↔ i ∈ L' := by
    intro i
    constructor
    · intro h
      obtain ⟨i', hi', he⟩ := mem_map.1 (hL h)
      have : i' = i := Sum.inl_injective he
      subst this
      exact mem_filter.2 ⟨hi', h⟩
    · intro h; exact (mem_filter.1 h).2
  have hinrL : ∀ f, (Sum.inr f : SC V E q r) ∉ L := by
    intro f h
    obtain ⟨i', -, he⟩ := mem_map.1 (hL h)
    simp at he
  refine ⟨L'.image (pieceP q r ends j₀) ∪ (X \ L').image (pieceQ q r ends j₀), ?_,
    (L'.biUnion fun i => fakeE q r ends i).map Function.Embedding.inr, ?_, ?_, ?_, ?_, ?_⟩
  · exact union_subset_union (image_subset_image hL'X) (image_subset_image sdiff_subset)
  · exact map_subset_map.2 (biUnion_subset_biUnion_of_subset_left _ hL'X)
  · -- divisibility of the residue
    intro S hS
    rw [mdeg_map_inr, ← ZMod.natCast_eq_zero_iff]
    have hdeg : deg (L'.biUnion fun i => fakeE q r ends i) S =
        ∑ i ∈ L', deg (fakeE q r ends i) S := by
      rw [deg, filter_biUnion, card_biUnion]
      · rfl
      · intro i hi i' hi' hne
        exact disjoint_filter_filter (fakeE_disj_fakeE (hX i (hL'X hi)) hne)
    have hL0 := (ZMod.natCast_eq_zero_iff _ _).2 (hLdiv S hS)
    have hLdeg : mdeg (sends q r ends) L S = (L'.filter fun i => S ⊆ liftE q r ends i).card := by
      have hLeq : L = L'.map Function.Embedding.inl := by
        ext c
        rcases c with i | f
        · simp [hinlL]
        · simp [hinrL]
      rw [hLeq, mdeg_map_inl]
    rw [hdeg, Nat.cast_sum]
    rw [hLdeg, card_filter, Nat.cast_sum] at hL0
    rw [← hL0]
    refine sum_congr rfl fun i hi => ?_
    unfold fakeE
    rw [fakeEdge_deg_cast (ends := ends2 ends) (i := Sum.inr i) hrq.le (hX i (hL'X hi)) hS]
    rw [← liftE_eq_inr]
    split_ifs <;> simp
  · -- pairwise disjointness
    intro W₁ hW₁ W₂ hW₂ hne
    simp only [coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe] at hW₁ hW₂
    rw [Function.onFun, id, id, disjoint_left]
    intro c hc₁ hc₂
    apply hne
    rcases hW₁ with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
      rcases hW₂ with ⟨i', hi', rfl⟩ | ⟨i', hi', rfl⟩
    · rcases c with a | f
      · rw [mem_pieceP_inl] at hc₁ hc₂; rw [← hc₁, ← hc₂]
      · rw [mem_pieceP_inr] at hc₁ hc₂
        rw [eq_of_mem_new (hX i (hL'X hi)) (hX i' (hL'X hi')) (Or.inl hc₁) (Or.inl hc₂)]
    · exfalso
      rcases c with a | f
      · exact not_mem_pieceQ_inl hc₂
      · rw [mem_pieceP_inr] at hc₁; rw [mem_pieceQ_inr] at hc₂
        have := eq_of_mem_new (hX i (hL'X hi)) (hX i' (mem_sdiff.1 hi').1) (Or.inl hc₁) hc₂
        subst this; exact (mem_sdiff.1 hi').2 hi
    · exfalso
      rcases c with a | f
      · exact not_mem_pieceQ_inl hc₁
      · rw [mem_pieceQ_inr] at hc₁; rw [mem_pieceP_inr] at hc₂
        have := eq_of_mem_new (hX i (mem_sdiff.1 hi).1) (hX i' (hL'X hi')) hc₁ (Or.inl hc₂)
        subst this; exact (mem_sdiff.1 hi).2 hi'
    · rcases c with a | f
      · exact absurd hc₁ not_mem_pieceQ_inl
      · rw [mem_pieceQ_inr] at hc₁ hc₂
        rw [eq_of_mem_new (hX i (mem_sdiff.1 hi).1) (hX i' (mem_sdiff.1 hi').1) hc₁ hc₂]
  · -- the residue is disjoint from the pieces
    rw [disjoint_left]
    intro c hc hc'
    obtain ⟨f, hf, rfl⟩ := mem_map.1 hc'
    obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
    obtain ⟨W, hW, hcW⟩ := mem_sup.1 hc
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨i', hi', rfl⟩ := mem_image.1 hW
      have hc2 : f ∈ antiE q r ends j₀ i' := mem_pieceP_inr.1 hcW
      exact disjoint_left.1 (antiE_disj_fakeE j₀ (hX i' (hL'X hi')) i) hc2 hfi
    · obtain ⟨i', hi', rfl⟩ := mem_image.1 hW
      have hc2 := mem_pieceQ_inr.1 hcW
      have := eq_of_mem_new (hX i (hL'X hi)) (hX i' (mem_sdiff.1 hi').1) (Or.inr hfi) hc2
      subst this; exact (mem_sdiff.1 hi').2 hi
  · -- the union
    ext c
    rw [mem_union, mem_union, mem_sup]
    rcases c with i | f
    · rw [hinlL]
      constructor
      · rintro (⟨W, hW, hcW⟩ | h)
        · rcases mem_union.1 hW with hW | hW
          · obtain ⟨i', hi', rfl⟩ := mem_image.1 hW
            rw [mem_pieceP_inl.1 hcW]; exact Or.inr hi'
          · obtain ⟨i', hi', rfl⟩ := mem_image.1 hW
            exact absurd hcW not_mem_pieceQ_inl
        · simp at h
      · rintro (h | h)
        · simp [stepR] at h
        · exact Or.inl ⟨pieceP q r ends j₀ i, mem_union_left _ (mem_image_of_mem _ h),
            mem_pieceP_inl.2 rfl⟩
    · have hR : (Sum.inr f : SC V E q r) ∈ stepR q r ends j₀ X ↔
          ∃ i ∈ X, f ∈ antiE q r ends j₀ i ∨ f ∈ fakeE q r ends i := by
        simp [stepR]
      rw [hR]
      constructor
      · rintro (⟨W, hW, hcW⟩ | h)
        · rcases mem_union.1 hW with hW | hW
          · obtain ⟨i', hi', rfl⟩ := mem_image.1 hW
            exact Or.inl ⟨i', hL'X hi', Or.inl (mem_pieceP_inr.1 hcW)⟩
          · obtain ⟨i', hi', rfl⟩ := mem_image.1 hW
            exact Or.inl ⟨i', (mem_sdiff.1 hi').1, mem_pieceQ_inr.1 hcW⟩
        · obtain ⟨f', hf', he⟩ := mem_map.1 h
          cases he
          obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf'
          exact Or.inl ⟨i, hL'X hi, Or.inr hfi⟩
      · rintro (⟨i, hi, hf⟩ | h)
        · by_cases hiL : i ∈ L'
          · rcases hf with hf | hf
            · exact Or.inl ⟨pieceP q r ends j₀ i, mem_union_left _ (mem_image_of_mem _ hiL),
                mem_pieceP_inr.2 hf⟩
            · exact Or.inr (mem_map_of_mem _ (mem_biUnion.2 ⟨i, hiL, hf⟩))
          · exact Or.inl ⟨pieceQ q r ends j₀ i,
              mem_union_right _ (mem_image_of_mem _ (mem_sdiff.2 ⟨hi, hiL⟩)),
              mem_pieceQ_inr.2 hf⟩
        · exact absurd h (hinrL f)

/-- **The anti-edge refine-down step.**  For `r < q`, every labelled `r`-multigraph `X` has the
residual multi-refiner `stepR` with residue in `stepY` (the union of the fake edges) and family
`stepW`, with refinedness `(m + 1) · binom(q, r) + 2`. -/
theorem antiEdgeStep (hrq : r < q) (j₀ : Fin (fakeCount q r)) (X : Finset E)
    (hX : ∀ i ∈ X, (ends i).card = r) :
    IsResidualMultiRefiner q r ((fakeCount q r + 1) * q.choose r + 2) (sends q r ends)
      (X.map Function.Embedding.inl) (stepR q r ends j₀ X) (stepY q r ends X)
      (stepW q r ends j₀ X) := by
  classical
  have hnewX : ∀ f, (Sum.inr f : SC V E q r) ∈ stepR q r ends j₀ X ↔
      ∃ i ∈ X, f ∈ antiE q r ends j₀ i ∨ f ∈ fakeE q r ends i := by
    intro f; simp [stepR]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases c with i | f
    · have : i ∈ X := by
        rcases (by simpa using hc : i ∈ X ∨ (Sum.inl i : SC V E q r) ∈ stepR q r ends j₀ X)
          with h | h
        · exact h
        · simp [stepR] at h
      show (liftE q r ends i).card = r
      rw [card_liftE, hX i this]
    · have : (Sum.inr f : SC V E q r) ∈ stepR q r ends j₀ X := by simpa using hc
      obtain ⟨i, hi, hf⟩ := (hnewX f).1 this
      show f.card = r
      rcases hf with hf | hf
      · exact antiE_card_edge hf
      · exact fakeEdge_card_edge hf
  · rw [disjoint_left]
    intro c hc hc'
    obtain ⟨i, -, rfl⟩ := mem_map.1 hc
    obtain ⟨f, -, hf⟩ := mem_map.1 hc'
    simp at hf
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hW
      exact divisible_pieceP hrq.le j₀ (hX i hi)
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hW
      exact divisible_pieceQ hrq.le j₀ (hX i hi)
  · intro W hW c hc
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hW
      rcases c with i' | f
      · rw [mem_pieceP_inl] at hc; subst hc
        exact mem_union_left _ (mem_map_of_mem _ hi)
      · rw [mem_pieceP_inr] at hc
        exact mem_union_right _ ((hnewX f).2 ⟨i, hi, Or.inl hc⟩)
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hW
      rcases c with i' | f
      · exact absurd hc not_mem_pieceQ_inl
      · rw [mem_pieceQ_inr] at hc
        exact mem_union_right _ ((hnewX f).2 ⟨i, hi, hc⟩)
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hW
      refine (card_insert_le _ _).trans ?_
      rw [card_map]
      have := card_antiE_le hrq.le j₀ (hX i hi)
      have : 0 ≤ fakeCount q r * q.choose r := Nat.zero_le _
      nlinarith
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 hW
      rw [pieceQ, card_map]
      refine (card_union_le _ _).trans ?_
      have h1 := card_antiE_le hrq.le j₀ (hX i hi)
      have h2 := card_fakeEdge_le (ends := ends2 ends) (i := Sum.inr i) hrq.le (hX i hi)
      have : (fakeE q r ends i).card ≤ fakeCount q r * q.choose r := h2
      nlinarith
  · intro c hc
    have hc' : ∀ i ∈ X, ∀ i' ∈ X, c ∈ pieceP q r ends j₀ i → c ∈ pieceP q r ends j₀ i' →
        i = i' := by
      intro i hi i' hi' h1 h2
      rcases c with a | f
      · rw [mem_pieceP_inl] at h1 h2; rw [← h1, ← h2]
      · rw [mem_pieceP_inr] at h1 h2
        exact eq_of_mem_new (hX i hi) (hX i' hi') (Or.inl h1) (Or.inl h2)
    have hq' : ∀ i ∈ X, ∀ i' ∈ X, c ∈ pieceQ q r ends j₀ i → c ∈ pieceQ q r ends j₀ i' →
        i = i' := by
      intro i hi i' hi' h1 h2
      rcases c with a | f
      · exact absurd h1 not_mem_pieceQ_inl
      · rw [mem_pieceQ_inr] at h1 h2
        exact eq_of_mem_new (hX i hi) (hX i' hi') h1 h2
    have e1 : ((X.image (pieceP q r ends j₀)).filter (c ∈ ·)).card ≤ 1 := by
      rw [card_le_one]
      intro W₁ hW₁ W₂ hW₂
      obtain ⟨hW₁m, hc₁⟩ := mem_filter.1 hW₁
      obtain ⟨hW₂m, hc₂⟩ := mem_filter.1 hW₂
      obtain ⟨i₁, hi₁, rfl⟩ := mem_image.1 hW₁m
      obtain ⟨i₂, hi₂, rfl⟩ := mem_image.1 hW₂m
      rw [hc' i₁ hi₁ i₂ hi₂ hc₁ hc₂]
    have e2 : ((X.image (pieceQ q r ends j₀)).filter (c ∈ ·)).card ≤ 1 := by
      rw [card_le_one]
      intro W₁ hW₁ W₂ hW₂
      obtain ⟨hW₁m, hc₁⟩ := mem_filter.1 hW₁
      obtain ⟨hW₂m, hc₂⟩ := mem_filter.1 hW₂
      obtain ⟨i₁, hi₁, rfl⟩ := mem_image.1 hW₁m
      obtain ⟨i₂, hi₂, rfl⟩ := mem_image.1 hW₂m
      rw [hq' i₁ hi₁ i₂ hi₂ hc₁ hc₂]
    unfold stepW
    rw [filter_union]
    refine (card_union_le _ _).trans ?_
    omega
  · exact antiEdgeStep_decomp hrq j₀ X hX


end RefinedAbsorption.RefineDown
