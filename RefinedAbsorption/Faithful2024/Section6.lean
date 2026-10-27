module
public import RefinedAbsorption.Faithful2024.MultiGadget

/-!
# Section 6.3 of arXiv:2402.17855v1: Theorems 6.2, 6.3 and Lemma 6.4

* `Theorem_6_2` (statement): absorbers with two decompositions `Q₁` of `A` and `Q₂` of `A ∪ L` such
  that `|V(Q₁) ∩ V(Q₂)| ≤ r` for **all** `Q₁ ∈ Q₁`, `Q₂ ∈ Q₂`.  **Open here** (not proved).
* `Theorem_6_3` (statement): minimum-degree Existence Conjecture avoiding a given packing in the
  same sense.  The article only sketches its proof ("We omit the details").  **Open here.**
* `Lemma_6_4` (statement) and **`lemma_6_4 : Lemma_6_4` (proved)**: absorbers `A` for `L` such that
  `A ∪ L` has a decomposition `Q` with `|V(Q) ∩ V(L)| ≤ r` for all `Q ∈ Q`, and equality only if
  `V(Q) ∩ V(L) = V(e)` for some edge `e ∈ L`.  Here `V(L)` is the whole ambient vertex set
  `Fin m` of `L` (isolated vertices included), which is the strongest reading.

Proof of Lemma 6.4 (a variant of the article's proof, using the same idea of private partial
cliques on every edge): every edge `e ∈ L` gets `q - r` private new vertices `N_e`; the cliques
`K_e` on `e ∪ N_e` move `L` to the simple divisible graph `L' = ⋃_e (K_e - e)`; a library absorber
`A'` for `L'` on further new vertices completes `A = A' ∪ L'`.  Then `A` decomposes by the
on-mode of `A'` (a decomposition of `A' ∪ L'`), and `A ∪ L` decomposes into the off-mode of `A'`
(a decomposition of `A'`) together with the cliques `K_e`.  A clique `K_e` meets the old vertices
exactly in `e`; a clique of the decomposition of `A'` meets them in at most `r - 1` vertices,
since every edge of `A'` contains a new vertex of the library.
-/

@[expose] public section

namespace RefinedAbsorption.Faithful2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.Absorber17

/-- **Theorem 6.2 of arXiv:2402.17855v1** (statement).  For `q > r ≥ 1`, every `K_q^r`-divisible
`r`-graph `L` (on `Fin m`) has a `K_q^r`-absorber `A` (on `Fin m` plus `h` new vertices) with
`K_q^r`-decompositions `Q₁` of `A` and `Q₂` of `A ∪ L` such that `|V(Q₁) ∩ V(Q₂)| ≤ r` for all
`Q₁ ∈ Q₁` and `Q₂ ∈ Q₂`. -/
def Theorem_6_2 : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∀ (m : ℕ) (L : Finset (Finset (Fin m))), IsRGraph r L →
    IsDivisible q r L → ∃ (h : ℕ) (A Q₁ Q₂ : Finset (Finset (Fin m ⊕ Fin h))),
      IsAbsorber q r (RefinedAbsorption.gmap Function.Embedding.inl L) A ∧
      IsDecomposition q r A Q₁ ∧
      IsDecomposition q r (A ∪ RefinedAbsorption.gmap Function.Embedding.inl L) Q₂ ∧
      ∀ P₁ ∈ Q₁, ∀ P₂ ∈ Q₂, (P₁ ∩ P₂).card ≤ r

/-- **Theorem 6.3 of arXiv:2402.17855v1** (statement).  For `q > r ≥ 1` there are `n₀` and
`ε > 0` such that every `K_q^r`-divisible `r`-graph `G` on `v(G) = n ≥ n₀` vertices with
`δ(G) ≥ (1 - ε) n`, and every `K_q^r`-packing `Q₁` of `G`, admit a `K_q^r`-decomposition `Q₂` of `G`
with `|V(Q₁) ∩ V(Q₂)| ≤ r` for all `Q₁ ∈ Q₁`, `Q₂ ∈ Q₂`. -/
def Theorem_6_3 : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∃ (n₀ : ℕ) (ε : ℝ), 0 < ε ∧ ∀ n ≥ n₀,
    ∀ G : Finset (Finset (Fin n)), IsRGraph r G → IsDivisible q r G →
      MinDegGE r G ((1 - ε) * n) → ∀ Q₁ : Finset (Finset (Fin n)), IsPacking q r G Q₁ →
        ∃ Q₂ : Finset (Finset (Fin n)), IsDecomposition q r G Q₂ ∧
          ∀ P₁ ∈ Q₁, ∀ P₂ ∈ Q₂, (P₁ ∩ P₂).card ≤ r

/-- **Lemma 6.4 of arXiv:2402.17855v1** (statement).  For `q > r ≥ 1`, every `K_q^r`-divisible
`r`-graph `L` on `Fin m` has a `K_q^r`-absorber `A` (on `Fin m` plus `h` new vertices) such that
`A ∪ L` admits a `K_q^r`-decomposition `Q` with `|V(Q) ∩ V(L)| ≤ r` for every `Q ∈ Q`, with
equality only if `V(Q) ∩ V(L) = V(e)` for some `e ∈ L`.  (`V(L)` is the ambient vertex set
`Fin m`.) -/
def Lemma_6_4 : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∀ (m : ℕ) (L : Finset (Finset (Fin m))), IsRGraph r L →
    IsDivisible q r L → ∃ (h : ℕ) (A Q : Finset (Finset (Fin m ⊕ Fin h))),
      IsAbsorber q r (RefinedAbsorption.gmap Function.Embedding.inl L) A ∧
      IsDecomposition q r (A ∪ RefinedAbsorption.gmap Function.Embedding.inl L) Q ∧
      ∀ P ∈ Q, (P ∩ univ.map Function.Embedding.inl).card ≤ r ∧
        ((P ∩ univ.map Function.Embedding.inl).card = r →
          ∃ e ∈ L, P ∩ univ.map Function.Embedding.inl = e.map Function.Embedding.inl)

section MoverDecomp

variable {n h : ℕ} {E : Type*} [DecidableEq E] {q r : ℕ} {ends : E → Finset (Fin n)}
  {nv : E → Fin (q - r) → Fin h} {W : Finset E}

theorem subset_moverSet_iff_mem {c : E} (hc : (ends c).card = r) {t : Finset (Fin n ⊕ Fin h)}
    (ht : t.card = r) :
    t ⊆ moverSet q r ends nv c ↔
      t ∈ moverEdges q r ends nv c ∨ t = (ends c).map Function.Embedding.inl := by
  constructor
  · intro hsub
    by_cases he : t = (ends c).map Function.Embedding.inl
    · exact Or.inr he
    · exact Or.inl (mem_erase.2 ⟨he, mem_powersetCard.2 ⟨hsub, ht⟩⟩)
  · rintro (h' | rfl)
    · exact (mem_powersetCard.1 (mem_of_mem_erase h')).1
    · exact subset_union_left

/-- **The moving cliques decompose `L' ∪ L`.** -/
theorem isDecomposition_movers (hrq : r ≤ q) (hW : ∀ c ∈ W, (ends c).card = r)
    (hinj : ∀ c ∈ W, Function.Injective (nv c))
    (hsep : ∀ c ∈ W, ∀ c' ∈ W, c ≠ c' → ∀ j j', nv c j ≠ nv c' j')
    (hends : Set.InjOn ends W) :
    IsDecomposition q r (moverGraph q r ends nv W ∪
      W.image fun c => (ends c).map Function.Embedding.inl) (W.image (moverSet q r ends nv)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rcases mem_union.1 ht with ht | ht
    · exact isRGraph_moverGraph t ht
    · obtain ⟨c, hc, rfl⟩ := mem_image.1 ht
      rw [card_map, hW c hc]
  · intro Q hQ
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hQ
    exact card_moverSet hrq (hW c hc) (hinj c hc)
  · intro t ht
    -- the movers containing `t`
    have hfilt : ∀ c ∈ W, t ⊆ moverSet q r ends nv c → ∀ c' ∈ W,
        t ⊆ moverSet q r ends nv c' → c = c' := by
      intro c hc htc c' hc' htc'
      rcases (subset_moverSet_iff_mem (hW c hc) ht).1 htc with h1 | h1 <;>
        rcases (subset_moverSet_iff_mem (hW c' hc') ht).1 htc' with h2 | h2
      · obtain ⟨j, hj⟩ := exists_inr_of_mem_moverEdges (hW c hc) h1
        obtain ⟨j', hj'⟩ := inr_mem_moverEdges h2 hj
        by_contra hne
        exact hsep c hc c' hc' hne j j' hj'.symm
      · obtain ⟨j, hj⟩ := exists_inr_of_mem_moverEdges (hW c hc) h1
        rw [h2] at hj
        obtain ⟨a, -, ha⟩ := mem_map.1 hj
        exact absurd ha Sum.inl_ne_inr
      · obtain ⟨j, hj⟩ := exists_inr_of_mem_moverEdges (hW c' hc') h2
        rw [h1] at hj
        obtain ⟨a, -, ha⟩ := mem_map.1 hj
        exact absurd ha Sum.inl_ne_inr
      · exact hends hc hc' (map_injective _ (h1.symm.trans h2))
    split_ifs with hmem
    · rcases mem_union.1 hmem with h' | h'
      · obtain ⟨c, hc, htc⟩ := mem_biUnion.1 h'
        rw [cliqueMult, card_eq_one]
        refine ⟨moverSet q r ends nv c, eq_singleton_iff_unique_mem.2 ⟨mem_filter.2
          ⟨mem_image_of_mem _ hc, (mem_powersetCard.1 (mem_of_mem_erase htc)).1⟩, ?_⟩⟩
        intro Q hQ
        obtain ⟨hQ, htQ⟩ := mem_filter.1 hQ
        obtain ⟨c', hc', rfl⟩ := mem_image.1 hQ
        rw [hfilt c' hc' htQ c hc (mem_powersetCard.1 (mem_of_mem_erase htc)).1]
      · obtain ⟨c, hc, rfl⟩ := mem_image.1 h'
        rw [cliqueMult, card_eq_one]
        refine ⟨moverSet q r ends nv c, eq_singleton_iff_unique_mem.2 ⟨mem_filter.2
          ⟨mem_image_of_mem _ hc, subset_union_left⟩, ?_⟩⟩
        intro Q hQ
        obtain ⟨hQ, htQ⟩ := mem_filter.1 hQ
        obtain ⟨c', hc', rfl⟩ := mem_image.1 hQ
        rw [hfilt c' hc' htQ c hc subset_union_left]
    · rw [cliqueMult, card_eq_zero, filter_eq_empty_iff]
      intro Q hQ htQ
      obtain ⟨c, hc, rfl⟩ := mem_image.1 hQ
      apply hmem
      rcases (subset_moverSet_iff_mem (hW c hc) ht).1 htQ with h' | h'
      · exact mem_union_left _ (mem_biUnion.2 ⟨c, hc, h'⟩)
      · exact mem_union_right _ (mem_image.2 ⟨c, hc, h'.symm⟩)

end MoverDecomp

/-- **Lemma 6.4 of arXiv:2402.17855v1**, proved. -/
theorem lemma_6_4 : Lemma_6_4 := by
  intro q r hr hrq m L hLr hdiv
  classical
  set c := L.card with hc
  obtain ⟨B, hB⟩ := absorberLibrary hr hrq (c * q.choose r)
  set h := c * (q - r) + B with hh
  -- the private new vertices of the edges
  let idx : Finset (Fin m) → ℕ := fun x => if hx : x ∈ L then (L.equivFin ⟨x, hx⟩ : ℕ) else 0
  have hidxL : ∀ x ∈ L, idx x < c := by
    intro x hx
    simp only [idx, dif_pos hx]
    exact (L.equivFin ⟨x, hx⟩).2
  have hidxW : ∀ x ∈ L, ∀ y ∈ L, idx x = idx y → x = y := by
    intro x hx y hy hxy
    simp only [idx, dif_pos hx, dif_pos hy] at hxy
    have := L.equivFin.injective (Fin.ext hxy)
    exact congrArg Subtype.val this
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · -- `L = ∅`: the empty absorber
    have hL0 : L = ∅ := card_eq_zero.1 (by rw [← hc]; exact hc0)
    subst hL0
    refine ⟨0, ∅, ∅, ?_, ?_, ?_⟩
    · have := (isBoundedAbsorber_empty (q := q) (r := r) (B := 0)
        (V := Fin m ⊕ Fin 0)).absorber
      simpa [RefinedAbsorption.gmap] using this
    · simpa [RefinedAbsorption.gmap] using
        (isBoundedAbsorber_empty (q := q) (r := r) (B := 0) (V := Fin m ⊕ Fin 0)).off
    · simp
  have hidx : ∀ x, idx x < c := by
    intro x
    by_cases hx : x ∈ L
    · exact hidxL x hx
    · simp only [idx, dif_neg hx]; omega
  have hbound : ∀ x (j : Fin (q - r)), idx x * (q - r) + j < h := by
    intro x j
    have h1 : (idx x + 1) * (q - r) ≤ c * (q - r) := Nat.mul_le_mul_right _ (hidx x)
    have h2 := j.2
    rw [add_mul, one_mul] at h1
    omega
  let nv : Finset (Fin m) → Fin (q - r) → Fin h := fun x j => ⟨idx x * (q - r) + j, hbound x j⟩
  have hnv_lt : ∀ x j, (nv x j : ℕ) < c * (q - r) := by
    intro x j
    have h1 : (idx x + 1) * (q - r) ≤ c * (q - r) := Nat.mul_le_mul_right _ (hidx x)
    have h2 := j.2
    rw [add_mul, one_mul] at h1
    show idx x * (q - r) + j < c * (q - r)
    omega
  have hinj : ∀ x ∈ L, Function.Injective (nv x) := by
    intro x _ j j' hjj
    have := congrArg Fin.val hjj
    simp only [nv] at this
    exact Fin.ext (by omega)
  have hsep : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → ∀ j j', nv x j ≠ nv y j' := by
    intro x hx y hy hxy j j' hjj
    have := congrArg Fin.val hjj
    simp only [nv] at this
    exact hxy (hidxW x hx y hy (nat_mul_add_inj j.2 j'.2 this).1)
  have hWr : ∀ x ∈ L, (id x : Finset (Fin m)).card = r := fun x hx => hLr x hx
  have hdivM : MIsDivisible q r (id : Finset (Fin m) → Finset (Fin m)) L := fun S hS => hdiv S hS
  set L' := moverGraph q r (id : Finset (Fin m) → Finset (Fin m)) nv L with hL'
  let sv : Fin B ↪ Fin m ⊕ Fin h :=
    ⟨fun p => Sum.inr ⟨c * (q - r) + p, by omega⟩, fun p p' hpp => by
      have := congrArg Fin.val (Sum.inr_injective hpp)
      simp only at this
      exact Fin.ext (by omega)⟩
  set S := (univ : Finset (Fin B)).map sv with hS
  have hSdisj : Disjoint S (vertexSet L') := by
    rw [disjoint_left]
    intro x hxS hxL
    obtain ⟨p, -, rfl⟩ := mem_map.1 hxS
    rcases mem_vertexSet_moverGraph hxL with ⟨a, -, ha⟩ | ⟨y, -, j, hj⟩
    · exact Sum.inr_ne_inl ha
    · have := congrArg Fin.val (Sum.inr_injective hj)
      have h1 := hnv_lt y j
      simp only at this
      omega
  have hL'c : L'.card ≤ c * q.choose r := card_moverGraph_le hrq.le hWr hinj
  obtain ⟨A', Qon', Qoff', hbd, hvert⟩ := hB (Fin m ⊕ Fin h) L' isRGraph_moverGraph
    (isDivisible_moverGraph hrq hWr hinj hsep hdivM) hL'c S hSdisj
    (by rw [hS, card_map, card_univ, Fintype.card_fin])
  -- facts
  set Lι := RefinedAbsorption.gmap (Function.Embedding.inl : Fin m ↪ Fin m ⊕ Fin h) L with hLι
  have hLιimg : Lι = L.image fun x => (id x : Finset (Fin m)).map Function.Embedding.inl := by
    ext e
    rw [hLι, mem_gmap, mem_image]
    rfl
  have hA'inr : ∀ t ∈ A', ∃ p, Sum.inr p ∈ t := by
    intro t ht
    obtain ⟨x, hxt, hxS⟩ := IsAbsorber.exists_mem_of_subset hbd.absorber hvert ht
    obtain ⟨p, -, rfl⟩ := mem_map.1 hxS
    exact ⟨_, hxt⟩
  have hL'inr : ∀ t ∈ L', ∃ p, Sum.inr p ∈ t := by
    intro t ht
    obtain ⟨x, hx, htx⟩ := mem_biUnion.1 ht
    obtain ⟨j, hj⟩ := exists_inr_of_mem_moverEdges (hWr x hx) htx
    exact ⟨_, hj⟩
  have hLιinl : ∀ t ∈ Lι, ∀ y ∈ t, ∃ a, y = Sum.inl a := by
    intro t ht y hy
    obtain ⟨e, -, rfl⟩ := mem_gmap.1 ht
    obtain ⟨a, -, rfl⟩ := mem_map.1 hy
    exact ⟨a, rfl⟩
  have hAL : Disjoint A' L' := by
    rw [disjoint_left]
    intro t htA htL
    exact hbd.absorber.independent t htA (subset_vertexSet htL)
  have hALι : Disjoint (A' ∪ L') Lι := by
    rw [disjoint_left]
    intro t ht htL
    obtain ⟨p, hp⟩ : ∃ p, Sum.inr p ∈ t := by
      rcases mem_union.1 ht with h' | h'
      · exact hA'inr t h'
      · exact hL'inr t h'
    obtain ⟨a, ha⟩ := hLιinl t htL _ hp
    exact Sum.inr_ne_inl ha
  have hmov := isDecomposition_movers (q := q) hrq.le hWr hinj hsep (Set.injOn_id _)
  rw [← hLιimg] at hmov
  have hdecU : IsDecomposition q r (A' ∪ (L' ∪ Lι))
      (Qoff' ∪ L.image (moverSet q r (id : Finset (Fin m) → Finset (Fin m)) nv)) := by
    refine IsDecomposition.union hrq.le ?_ hbd.off hmov
    rw [disjoint_union_right]
    exact ⟨hAL, disjoint_of_subset_left subset_union_left hALι⟩
  refine ⟨h, A' ∪ L', Qoff' ∪ L.image (moverSet q r (id : Finset (Fin m) → Finset (Fin m)) nv),
    ⟨hdiv.gmap _, ?_, ⟨Qon', hbd.on⟩, ?_⟩, ?_, ?_⟩
  · -- independence of the old vertices
    intro t ht hsub
    obtain ⟨p, hp⟩ : ∃ p, Sum.inr p ∈ t := by
      rcases mem_union.1 ht with h' | h'
      · exact hA'inr t h'
      · exact hL'inr t h'
    have := hsub hp
    rw [vertexSet_gmap] at this
    obtain ⟨a, -, ha⟩ := mem_map.1 this
    exact Sum.inl_ne_inr ha
  · exact ⟨_, by rw [union_assoc]; exact hdecU⟩
  · rw [union_assoc]; exact hdecU
  · -- intersections with the old vertices
    intro P hP
    rcases mem_union.1 hP with hP | hP
    · -- a clique of the decomposition of `A'`: at most `r - 1` old vertices
      have hlt : (P ∩ univ.map Function.Embedding.inl).card < r := by
        by_contra hge
        push_neg at hge
        obtain ⟨t, htP, htc⟩ := exists_subset_card_eq hge
        have htA : t ∈ A' := hbd.off.cliqueEdges_subset hP
          (mem_powersetCard.2 ⟨htP.trans inter_subset_left, htc⟩)
        obtain ⟨p, hp⟩ := hA'inr t htA
        obtain ⟨a, -, ha⟩ := mem_map.1 (mem_inter.1 (htP hp)).2
        exact Sum.inl_ne_inr ha
      exact ⟨hlt.le, fun h' => absurd h' hlt.ne⟩
    · -- a moving clique: exactly the edge
      obtain ⟨e, he, rfl⟩ := mem_image.1 hP
      have hinter : moverSet q r (id : Finset (Fin m) → Finset (Fin m)) nv e ∩
          univ.map Function.Embedding.inl = e.map Function.Embedding.inl := by
        ext y
        simp only [moverSet, id, mem_inter, mem_union, mem_map, mem_image, mem_univ, true_and,
          Function.Embedding.inl_apply]
        constructor
        · rintro ⟨h1 | ⟨j, rfl⟩, a, ha⟩
          · exact h1
          · exact absurd ha Sum.inl_ne_inr
        · rintro ⟨a, ha, rfl⟩
          exact ⟨Or.inl ⟨a, ha, rfl⟩, a, rfl⟩
      rw [hinter, card_map, hLr e he]
      exact ⟨le_rfl, fun _ => ⟨e, he, rfl⟩⟩

end RefinedAbsorption.Faithful2024
