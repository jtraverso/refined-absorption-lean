module
public import RefinedAbsorption.Faithful2024.Theorem37Aux
public import RefinedAbsorption.Faithful2024.Theorem38One

/-!
# Theorem 3.7 of arXiv:2402.17855v1 (Refined Multi-Omni-Absorber Theorem), faithful form

`theorem_3_7_for_all : ∀ q r, 1 ≤ r → r < q → Theorem_3_7_for q r`, i.e. **`theorem_3_7 :
Theorem_3_7`**.

The proof follows §5.1 of the article:

1. Theorem 3.8 (`theorem_3_8_conclusion`) applied to `X` and `Y` gives a `C'`-refined
   `K_q^r`-multi-refiner `R` of `X` with refinement family `𝒲`, `Δ(𝒲) ≤ C' Δ` and `R` flat to `Y`.
2. To every nonempty member `H ∈ 𝒲` (a divisible multigraph with at most `C'` copies) we attach a
   multi-absorber gadget (`exists_multiGadget`, the role of Theorem 1.4).
3. The auxiliary vertices of all gadgets are placed inside `Y` (`multiCliqueEmbedding`, Claim 3.7.1:
   parallel edges are allowed, so no bound `Δ ≤ n/C` is needed), with every `(r-1)`-set in at most
   `C · Δ(𝒲)` new edges.
4. `A = R ∪ ⋃_H A_H`; for a divisible `L ⊆ X` the decomposition takes the on-mode of the gadget of
   every `H ∈ Q_R(L)` and the off-mode of every other gadget.
-/

@[expose] public section

namespace RefinedAbsorption.Faithful2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement

/-- Relabelling the local labels of the gadget of `W` into the final label type. -/
def liftLab {E' : Type*} {n h : ℕ} (W : Finset E') :
    E' ⊕ Finset (Fin n ⊕ Fin h) → E' ⊕ (Finset E' × Finset (Fin n ⊕ Fin h)) :=
  Sum.elim Sum.inl fun t => Sum.inr (W, t)

theorem liftLab_injective {E' : Type*} {n h : ℕ} (W : Finset E') :
    Function.Injective (liftLab (n := n) (h := h) W) := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;> simp_all [liftLab]

theorem image_inl_endsL {n h : ℕ} {φ : Fin h → Fin n} (s : Finset (Fin n)) :
    (s.map (Function.Embedding.inl : Fin n ↪ Fin n ⊕ Fin h)).image (emb φ) = s := by
  ext a
  simp [emb]

set_option maxHeartbeats 4000000 in
/-- **Theorem 3.7 of arXiv:2402.17855v1 (Refined Multi-Omni-Absorber Theorem)**, faithful
statement, for every `q > r ≥ 1`. -/
theorem theorem_3_7_for_all {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) : Theorem_3_7_for q r := by
  obtain ⟨C', hC', h38⟩ := theorem_3_8_conclusion q r hr hrq
  obtain ⟨hg, hgad⟩ := exists_multiGadget hr hrq C'
  obtain ⟨Ce, hCe, hemb⟩ := multiCliqueEmbedding r hg (r * C')
  refine ⟨(C' + Ce * 3 ^ r) * C' + 3 * Ce + C' + 2, by omega, ?_⟩
  intro n E _ ends X hX hmult hCn Y hY
  obtain ⟨E', _, g, ends', R, 𝒲, hginj, hends, hRef, hFam, hdeg, hflat⟩ :=
    h38 n ends X hX hmult (by omega) Y hY
  classical
  set D0 := mrefDeg r ends' 𝒲 with hD0
  set I := 𝒲.filter fun W => W.Nonempty with hI
  have hD0S : ∀ S : Finset (Fin n), S.card = r - 1 →
      (𝒲.filter fun W => S ⊆ W.biUnion ends').card ≤ D0 := by
    intro S hS
    exact le_sup (f := mrefDegAt ends' 𝒲) (mem_filter.2 ⟨mem_univ _, by omega⟩)
  have hgW : ∀ W ∈ I, ∃ (T : Finset (Finset (Fin n ⊕ Fin hg)))
      (Qon Qoff : Finset (Finset (E' ⊕ Finset (Fin n ⊕ Fin hg)))),
      IsMultiGadget q r (r * C') ends' W T Qon Qoff := by
    intro W hW
    obtain ⟨hW𝒲, hne⟩ := mem_filter.1 hW
    exact hgad n ends' W hne (fun c hc => hRef.rgraph c (hRef.family_sub W hW𝒲 hc))
      (hRef.family_div W hW𝒲) (hFam.card_le W hW𝒲)
  choose! T Qon Qoff hT using hgW
  have hY3 : n ≤ 3 * Y.card := by
    have : (n : ℝ) ≤ 3 * Y.card := by linarith
    exact_mod_cast this
  have hYCe : Ce ≤ Y.card := by omega
  have hRoot : ∀ J : Finset (Fin n), J.card ≤ r - 1 →
      (I.filter fun W => J ⊆ W.biUnion ends').card ≤
        (3 ^ r * D0) * Y.card ^ (r - 1 - J.card) := by
    intro J hJ
    have h1 := rootIncidence_of_subset (r := r) I (fun W => W.biUnion ends') univ D0
      (fun _ _ => subset_univ _) (fun W hW => (hT W hW).wf.roots_ge)
      (fun S hS => (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans
        (hD0S S hS)) J hJ
    rw [card_univ, Fintype.card_fin] at h1
    refine h1.trans ?_
    have h2 : n ^ (r - 1 - J.card) ≤ 3 ^ r * Y.card ^ (r - 1 - J.card) := by
      calc n ^ (r - 1 - J.card) ≤ (3 * Y.card) ^ (r - 1 - J.card) := Nat.pow_le_pow_left hY3 _
        _ = 3 ^ (r - 1 - J.card) * Y.card ^ (r - 1 - J.card) := mul_pow _ _ _
        _ ≤ 3 ^ r * Y.card ^ (r - 1 - J.card) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc D0 * n ^ (r - 1 - J.card) ≤ D0 * (3 ^ r * Y.card ^ (r - 1 - J.card)) :=
          Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  obtain ⟨Φ, hvalid, hrange, -, hsum⟩ := hemb n I (fun W => W.biUnion ends') T Y (3 ^ r * D0)
    (fun W hW => (hT W hW).wf) hYCe hRoot
  -- the final labels
  let ends'' : E' ⊕ (Finset E' × Finset (Fin n ⊕ Fin hg)) → Finset (Fin n) :=
    Sum.elim ends' fun p => placeEdge (Φ p.1) p.2
  let g'' : E → E' ⊕ (Finset E' × Finset (Fin n ⊕ Fin hg)) := fun c => Sum.inl (g c)
  set Xg := X.image g with hXg
  set Gad : Finset (E' ⊕ (Finset E' × Finset (Fin n ⊕ Fin hg))) :=
    I.biUnion (fun W => (T W).image fun t => Sum.inr (W, t)) with hGad
  set A : Finset (E' ⊕ (Finset E' × Finset (Fin n ⊕ Fin hg))) := R.image Sum.inl ∪ Gad with hA
  set 𝒬 : Finset (Finset (E' ⊕ (Finset E' × Finset (Fin n ⊕ Fin hg)))) :=
    I.biUnion (fun W => (Qon W ∪ Qoff W).image (image (liftLab W))) with h𝒬
  have hXg'' : X.image g'' = Xg.image Sum.inl := by rw [hXg, image_image]; rfl
  -- basic facts on the gadgets
  have hoffsub : ∀ W ∈ I, ∀ K ∈ Qoff W, K ⊆ (T W).map Function.Embedding.inr := by
    intro W hW K hK
    rw [← (hT W hW).off_sup]
    exact le_sup (f := id) hK
  have honsub : ∀ W ∈ I, ∀ K ∈ Qon W,
      K ⊆ W.map Function.Embedding.inl ∪ (T W).map Function.Embedding.inr := by
    intro W hW K hK
    rw [← (hT W hW).on_sup]
    exact le_sup (f := id) hK
  have hKsub : ∀ W ∈ I, ∀ K ∈ Qon W ∪ Qoff W,
      K ⊆ W.map Function.Embedding.inl ∪ (T W).map Function.Embedding.inr := by
    intro W hW K hK
    rcases mem_union.1 hK with hK | hK
    · exact honsub W hW K hK
    · exact (hoffsub W hW K hK).trans subset_union_right
  have hcomp : ∀ W ∈ I, ∀ k ∈ W.map Function.Embedding.inl ∪ (T W).map Function.Embedding.inr,
      ends'' (liftLab W k) = (endsL ends' k).image (emb (Φ W)) := by
    intro W _ k _
    rcases k with c | t
    · exact (image_inl_endsL (ends' c)).symm
    · rfl
  have hGv : ∀ W ∈ I, ∀ k ∈ W.map Function.Embedding.inl ∪ (T W).map Function.Embedding.inr,
      (endsL ends' k : Set (Fin n ⊕ Fin hg)) ⊆ gadgetVerts (W.biUnion ends') := by
    intro W hW k hk x hx a hxa
    subst hxa
    rcases mem_union.1 hk with hk | hk
    · obtain ⟨c, hc, rfl⟩ := mem_map.1 hk
      have : Sum.inl a ∈ (ends' c).map Function.Embedding.inl := hx
      obtain ⟨b, hb, hba⟩ := mem_map.1 this
      rw [Function.Embedding.inl_apply, Sum.inl.injEq] at hba
      exact mem_biUnion.2 ⟨c, hc, hba ▸ hb⟩
    · obtain ⟨t, ht, rfl⟩ := mem_map.1 hk
      exact (hT W hW).wf.edge_roots t ht a hx
  have hclique : ∀ W ∈ I, ∀ K ∈ Qon W ∪ Qoff W, IsCliqueCopy q r ends'' (K.image (liftLab W)) := by
    intro W hW K hK
    have hKc : IsCliqueCopy q r (endsL ends') K := by
      rcases mem_union.1 hK with hK | hK
      · exact (hT W hW).on_clique K hK
      · exact (hT W hW).off_clique K hK
    exact isCliqueCopy_image hr hrq.le (injOn_emb (hvalid W hW)) hKc
      (fun k hk => hGv W hW k (hKsub W hW K hK hk))
      (fun k hk => hcomp W hW k (hKsub W hW K hK hk))
  have hTG : ∀ W ∈ I, ∀ t ∈ T W, (t : Set (Fin n ⊕ Fin hg)) ⊆ gadgetVerts (W.biUnion ends') := by
    intro W hW t ht x hx a hxa
    subst hxa
    exact (hT W hW).wf.edge_roots t ht a hx
  have hplace_card : ∀ W ∈ I, ∀ t ∈ T W, (placeEdge (Φ W) t).card = r := by
    intro W hW t ht
    rw [placeEdge, card_image_of_injOn ((injOn_emb (hvalid W hW)).mono (hTG W hW t ht))]
    exact (hT W hW).wf.edge_card t ht
  have hRsub : ∀ c ∈ R, ∃ W ∈ 𝒲, c ∈ W := by
    obtain ⟨𝒟, h𝒟, -, h𝒟u⟩ := hRef.decomp ∅ (empty_subset _) (fun S _ => by simp [mdeg])
    intro c hc
    have : c ∈ 𝒟.sup id := by rw [h𝒟u]; exact mem_union_right _ hc
    obtain ⟨W, hW, hcW⟩ := mem_sup.1 this
    exact ⟨W, h𝒟 hW, hcW⟩
  have hmemI : ∀ W ∈ 𝒲, ∀ c ∈ W, W ∈ I := fun W hW c hc => mem_filter.2 ⟨hW, ⟨c, hc⟩⟩
  -- membership in a lifted clique
  have hmem_lift : ∀ W (K : Finset (E' ⊕ Finset (Fin n ⊕ Fin hg))) x,
      x ∈ K.image (liftLab W) → (∃ c, x = Sum.inl c ∧ Sum.inl c ∈ K) ∨
        (∃ t, x = Sum.inr (W, t) ∧ Sum.inr t ∈ K) := by
    intro W K x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hx
    rcases k with c | t
    · exact Or.inl ⟨c, rfl, hk⟩
    · exact Or.inr ⟨t, rfl, hk⟩
  refine ⟨E' ⊕ (Finset E' × Finset (Fin n ⊕ Fin hg)), inferInstance, g'', ends'', A, 𝒬,
    Sum.inl_injective.comp hginj, fun c => hends c, ?_, ?_, ?_, ?_⟩
  · -- the multi-omni-absorber
    refine ⟨fun _ _ => subset_univ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
        show (ends' (g x)).card = r
        rw [hends]; exact hX x hx
      · rcases mem_union.1 hc with hc | hc
        · obtain ⟨c', hc', rfl⟩ := mem_image.1 hc
          exact hRef.rgraph c' (mem_union_right _ hc')
        · obtain ⟨W, hW, hcW⟩ := mem_biUnion.1 hc
          obtain ⟨t, ht, rfl⟩ := mem_image.1 hcW
          exact hplace_card W hW t ht
    · rw [hXg'', disjoint_left]
      intro c hc hcA
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
      rcases mem_union.1 hcA with h' | h'
      · obtain ⟨y, hy, hyx⟩ := mem_image.1 h'
        rw [Sum.inl.injEq] at hyx
        exact disjoint_left.1 hRef.disjoint hx (hyx ▸ hy)
      · obtain ⟨W, -, hW⟩ := mem_biUnion.1 h'
        obtain ⟨t, -, ht⟩ := mem_image.1 hW
        exact Sum.inr_ne_inl ht
    · intro K hK x hx
      obtain ⟨W, hW, hKW⟩ := mem_biUnion.1 hK
      obtain ⟨K0, hK0, rfl⟩ := mem_image.1 hKW
      have hsub := hKsub W hW K0 hK0
      rcases hmem_lift W K0 x hx with ⟨c, rfl, hc⟩ | ⟨t, rfl, ht⟩
      · rcases mem_union.1 (hsub hc) with h' | h'
        · obtain ⟨c', hc', hcc⟩ := mem_map.1 h'
          rw [Function.Embedding.inl_apply, Sum.inl.injEq] at hcc
          subst hcc
          have hc'XR := hRef.family_sub W (mem_filter.1 hW).1 hc'
          rcases mem_union.1 hc'XR with h'' | h''
          · exact mem_union_left _ (hXg'' ▸ mem_image_of_mem _ h'')
          · exact mem_union_right _ (mem_union_left _ (mem_image_of_mem _ h''))
        · obtain ⟨t, -, ht⟩ := mem_map.1 h'
          exact absurd ht Sum.inr_ne_inl
      · rcases mem_union.1 (hsub ht) with h' | h'
        · obtain ⟨c, -, hc⟩ := mem_map.1 h'
          exact absurd hc Sum.inl_ne_inr
        · obtain ⟨t', ht', htt⟩ := mem_map.1 h'
          rw [Function.Embedding.inr_apply, Sum.inr.injEq] at htt
          subst htt
          exact mem_union_right _ (mem_union_right _
            (mem_biUnion.2 ⟨W, hW, mem_image_of_mem _ ht'⟩))
    · intro K hK
      obtain ⟨W, hW, hKW⟩ := mem_biUnion.1 hK
      obtain ⟨K0, hK0, rfl⟩ := mem_image.1 hKW
      exact hclique W hW K0 hK0
    · -- one copy of `X` per clique
      intro K hK
      obtain ⟨W, hW, hKW⟩ := mem_biUnion.1 hK
      obtain ⟨K0, hK0, rfl⟩ := mem_image.1 hKW
      refine le_trans (card_le_card (t := (W ∩ Xg).image Sum.inl) ?_)
        (card_image_le.trans (hRef.oneX W (mem_filter.1 hW).1))
      intro x hx
      obtain ⟨hxK, hxX⟩ := mem_inter.1 hx
      rw [hXg''] at hxX
      obtain ⟨c, hc, rfl⟩ := mem_image.1 hxX
      rcases hmem_lift W K0 _ hxK with ⟨c', hcc, hc'⟩ | ⟨t, ht, -⟩
      · rw [Sum.inl.injEq] at hcc
        subst hcc
        rcases mem_union.1 (hKsub W hW K0 hK0 hc') with h' | h'
        · obtain ⟨c'', hc'', hcc⟩ := mem_map.1 h'
          rw [Function.Embedding.inl_apply, Sum.inl.injEq] at hcc
          subst hcc
          exact mem_image_of_mem _ (mem_inter.2 ⟨hc'', hc⟩)
        · obtain ⟨t, -, ht⟩ := mem_map.1 h'
          exact absurd ht Sum.inr_ne_inl
      · exact absurd ht Sum.inl_ne_inr
    · -- the decomposition function
      intro L hL hdivL
      set L0 := Xg.filter fun c => Sum.inl c ∈ L with hL0
      have hLL0 : L = L0.image Sum.inl := by
        ext x
        constructor
        · intro hx
          have := hL hx
          rw [hXg''] at this
          obtain ⟨c, hc, rfl⟩ := mem_image.1 this
          exact mem_image_of_mem _ (mem_filter.2 ⟨hc, hx⟩)
        · intro hx
          obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
          exact (mem_filter.1 hc).2
      have hdivL0 : MIsDivisible q r ends' L0 := by
        intro S hS
        have := hdivL S hS
        rwa [hLL0, mdeg, filter_image, card_image_of_injective _ Sum.inl_injective] at this
      obtain ⟨𝒟R, h𝒟R, h𝒟Rd, h𝒟Ru⟩ := hRef.decomp L0 (filter_subset _ _) hdivL0
      have hmem𝒟R : ∀ c ∈ L0 ∪ R, ∃ W ∈ 𝒟R, c ∈ W := by
        intro c hc
        rw [← h𝒟Ru] at hc
        obtain ⟨W, hW, hcW⟩ := mem_sup.1 hc
        exact ⟨W, hW, hcW⟩
      let pick : Finset E' → Finset (Finset (E' ⊕ Finset (Fin n ⊕ Fin hg))) := fun W =>
        if W ∈ 𝒟R then Qon W else Qoff W
      have hpick : ∀ W, pick W ⊆ Qon W ∪ Qoff W := by
        intro W
        simp only [pick]
        split_ifs
        · exact subset_union_left
        · exact subset_union_right
      have hpick_disj : ∀ W ∈ I,
          ((pick W : Set (Finset (E' ⊕ Finset (Fin n ⊕ Fin hg))))).PairwiseDisjoint id := by
        intro W hW
        simp only [pick]
        split_ifs
        · exact (hT W hW).on_disj
        · exact (hT W hW).off_disj
      refine ⟨I.biUnion fun W => (pick W).image (image (liftLab W)), ?_, ?_, ?_⟩
      · exact biUnion_subset_biUnion_of_subset_left _ (subset_refl _) |>.trans
          (fun K hK => by
            obtain ⟨W, hW, hKW⟩ := mem_biUnion.1 hK
            obtain ⟨K0, hK0, rfl⟩ := mem_image.1 hKW
            exact mem_biUnion.2 ⟨W, hW, mem_image_of_mem _ (hpick W hK0)⟩)
      · intro K hK K' hK' hne
        obtain ⟨W, hW, hKW⟩ := mem_biUnion.1 (mem_coe.1 hK)
        obtain ⟨K0, hK0, rfl⟩ := mem_image.1 hKW
        obtain ⟨W', hW', hKW'⟩ := mem_biUnion.1 (mem_coe.1 hK')
        obtain ⟨K0', hK0', rfl⟩ := mem_image.1 hKW'
        rw [Function.onFun, id, id, disjoint_left]
        intro x hx hx'
        by_cases hWW : W = W'
        · subst hWW
          have hK0ne : K0 ≠ K0' := fun h' => hne (h' ▸ rfl)
          have hd := hpick_disj W hW hK0 hK0' hK0ne
          obtain ⟨k, hk, rfl⟩ := mem_image.1 hx
          obtain ⟨k', hk', hkk⟩ := mem_image.1 hx'
          rw [liftLab_injective W hkk] at hk'
          exact disjoint_left.1 hd hk hk'
        · rcases hmem_lift W K0 x hx with ⟨c, rfl, hc⟩ | ⟨t, rfl, -⟩
          · rcases hmem_lift W' K0' _ hx' with ⟨c', hcc, hc'⟩ | ⟨t, ht, -⟩
            · rw [Sum.inl.injEq] at hcc
              subst hcc
              -- both pieces use their on-mode
              have hW𝒟 : W ∈ 𝒟R := by
                by_contra hno
                have : K0 ∈ Qoff W := by simpa [pick, hno] using hK0
                obtain ⟨t, -, ht⟩ := mem_map.1 (hoffsub W hW K0 this hc)
                exact Sum.inr_ne_inl ht
              have hW'𝒟 : W' ∈ 𝒟R := by
                by_contra hno
                have : K0' ∈ Qoff W' := by simpa [pick, hno] using hK0'
                obtain ⟨t, -, ht⟩ := mem_map.1 (hoffsub W' hW' K0' this hc')
                exact Sum.inr_ne_inl ht
              have hcW : c ∈ W := by
                rcases mem_union.1 (hKsub W hW K0 (hpick W hK0) hc) with h' | h'
                · obtain ⟨c'', hc'', hcc⟩ := mem_map.1 h'
                  rw [Function.Embedding.inl_apply, Sum.inl.injEq] at hcc
                  exact hcc ▸ hc''
                · obtain ⟨t, -, ht⟩ := mem_map.1 h'
                  exact absurd ht Sum.inr_ne_inl
              have hcW' : c ∈ W' := by
                rcases mem_union.1 (hKsub W' hW' K0' (hpick W' hK0') hc') with h' | h'
                · obtain ⟨c'', hc'', hcc⟩ := mem_map.1 h'
                  rw [Function.Embedding.inl_apply, Sum.inl.injEq] at hcc
                  exact hcc ▸ hc''
                · obtain ⟨t, -, ht⟩ := mem_map.1 h'
                  exact absurd ht Sum.inr_ne_inl
              exact disjoint_left.1 (h𝒟Rd hW𝒟 hW'𝒟 hWW) hcW hcW'
            · exact absurd ht Sum.inl_ne_inr
          · rcases hmem_lift W' K0' _ hx' with ⟨c', hcc, -⟩ | ⟨t', htt, -⟩
            · exact absurd hcc Sum.inr_ne_inl
            · rw [Sum.inr.injEq, Prod.mk.injEq] at htt
              exact hWW htt.1
      · -- the union is `L ∪ A`
        ext x
        rw [mem_sup]
        constructor
        · rintro ⟨K, hK, hxK⟩
          obtain ⟨W, hW, hKW⟩ := mem_biUnion.1 hK
          obtain ⟨K0, hK0, rfl⟩ := mem_image.1 hKW
          rcases hmem_lift W K0 x hxK with ⟨c, rfl, hc⟩ | ⟨t, rfl, ht⟩
          · have hW𝒟 : W ∈ 𝒟R := by
              by_contra hno
              have : K0 ∈ Qoff W := by simpa [pick, hno] using hK0
              obtain ⟨t, -, ht⟩ := mem_map.1 (hoffsub W hW K0 this hc)
              exact Sum.inr_ne_inl ht
            have hcW : c ∈ W := by
              rcases mem_union.1 (hKsub W hW K0 (hpick W hK0) hc) with h' | h'
              · obtain ⟨c'', hc'', hcc⟩ := mem_map.1 h'
                rw [Function.Embedding.inl_apply, Sum.inl.injEq] at hcc
                exact hcc ▸ hc''
              · obtain ⟨t, -, ht⟩ := mem_map.1 h'
                exact absurd ht Sum.inr_ne_inl
            have : c ∈ L0 ∪ R := by
              rw [← h𝒟Ru]; exact mem_sup.2 ⟨W, hW𝒟, hcW⟩
            rcases mem_union.1 this with h' | h'
            · exact mem_union_left _ (hLL0 ▸ mem_image_of_mem _ h')
            · exact mem_union_right _ (mem_union_left _ (mem_image_of_mem _ h'))
          · rcases mem_union.1 (hKsub W hW K0 (hpick W hK0) ht) with h' | h'
            · obtain ⟨c, -, hc⟩ := mem_map.1 h'
              exact absurd hc Sum.inl_ne_inr
            · obtain ⟨t', ht', htt⟩ := mem_map.1 h'
              rw [Function.Embedding.inr_apply, Sum.inr.injEq] at htt
              subst htt
              exact mem_union_right _ (mem_union_right _
                (mem_biUnion.2 ⟨W, hW, mem_image_of_mem _ ht'⟩))
        · intro hx
          -- a copy of `L ∪ R` lies in an on-mode clique; a gadget copy in a clique of its gadget
          have hcopy : ∀ c ∈ L0 ∪ R, ∃ K ∈ I.biUnion (fun W => (pick W).image (image (liftLab W))),
              Sum.inl c ∈ id K := by
            intro c hc
            obtain ⟨W, hW𝒟, hcW⟩ := hmem𝒟R c hc
            have hWI : W ∈ I := hmemI W (h𝒟R hW𝒟) c hcW
            have : Sum.inl c ∈ (Qon W).sup id := by
              rw [(hT W hWI).on_sup]
              exact mem_union_left _ (mem_map_of_mem _ hcW)
            obtain ⟨K0, hK0, hcK0⟩ := mem_sup.1 this
            refine ⟨K0.image (liftLab W), mem_biUnion.2 ⟨W, hWI, mem_image.2 ⟨K0, ?_, rfl⟩⟩,
              mem_image.2 ⟨Sum.inl c, hcK0, rfl⟩⟩
            simpa [pick, hW𝒟] using hK0
          rcases mem_union.1 hx with hxL | hxA
          · rw [hLL0] at hxL
            obtain ⟨c, hc, rfl⟩ := mem_image.1 hxL
            exact hcopy c (mem_union_left _ hc)
          · rcases mem_union.1 hxA with hxR | hxG
            · obtain ⟨c, hc, rfl⟩ := mem_image.1 hxR
              exact hcopy c (mem_union_right _ hc)
            · obtain ⟨W, hW, hxW⟩ := mem_biUnion.1 hxG
              obtain ⟨t, ht, rfl⟩ := mem_image.1 hxW
              have : Sum.inr t ∈ (pick W).sup id := by
                simp only [pick]
                split_ifs
                · rw [(hT W hW).on_sup]; exact mem_union_right _ (mem_map_of_mem _ ht)
                · rw [(hT W hW).off_sup]; exact mem_map_of_mem _ ht
              obtain ⟨K0, hK0, htK0⟩ := mem_sup.1 this
              exact ⟨K0.image (liftLab W), mem_biUnion.2 ⟨W, hW, mem_image_of_mem _ hK0⟩,
                mem_image.2 ⟨Sum.inr t, htK0, rfl⟩⟩
  · -- `C`-refined
    intro x hx
    rcases x with c | ⟨W, t⟩
    · -- a copy of `X ∪ R` lies in at most `C'` cliques
      have hcXR : c ∈ Xg ∪ R := by
        rcases mem_union.1 hx with h' | h'
        · rw [hXg''] at h'
          obtain ⟨c', hc', hcc⟩ := mem_image.1 h'
          rw [Sum.inl.injEq] at hcc
          exact mem_union_left _ (hcc ▸ hc')
        · rcases mem_union.1 h' with h'' | h''
          · obtain ⟨c', hc', hcc⟩ := mem_image.1 h''
            rw [Sum.inl.injEq] at hcc
            exact mem_union_right _ (hcc ▸ hc')
          · obtain ⟨W, -, hW⟩ := mem_biUnion.1 h''
            obtain ⟨t, -, ht⟩ := mem_image.1 hW
            exact absurd ht Sum.inr_ne_inl
      have hsub : 𝒬.filter (fun K => Sum.inl c ∈ K) ⊆
          (I.filter fun W => c ∈ W).biUnion fun W =>
            ((Qon W).filter fun K0 => Sum.inl c ∈ K0).image (image (liftLab W)) := by
        intro K hK
        obtain ⟨hK𝒬, hcK⟩ := mem_filter.1 hK
        obtain ⟨W, hW, hKW⟩ := mem_biUnion.1 hK𝒬
        obtain ⟨K0, hK0, rfl⟩ := mem_image.1 hKW
        obtain ⟨k, hk, hkc⟩ := mem_image.1 hcK
        rcases k with c' | t
        · have hcc : c' = c := Sum.inl_injective hkc
          subst hcc
          have hK0on : K0 ∈ Qon W := by
            rcases mem_union.1 hK0 with h' | h'
            · exact h'
            · obtain ⟨t, -, ht⟩ := mem_map.1 (hoffsub W hW K0 h' hk)
              exact absurd ht Sum.inr_ne_inl
          have hcW : c' ∈ W := by
            rcases mem_union.1 (honsub W hW K0 hK0on hk) with h' | h'
            · obtain ⟨c'', hc'', hcc⟩ := mem_map.1 h'
              rw [Function.Embedding.inl_apply, Sum.inl.injEq] at hcc
              exact hcc ▸ hc''
            · obtain ⟨t, -, ht⟩ := mem_map.1 h'
              exact absurd ht Sum.inr_ne_inl
          exact mem_biUnion.2 ⟨W, mem_filter.2 ⟨hW, hcW⟩,
            mem_image_of_mem _ (mem_filter.2 ⟨hK0on, hk⟩)⟩
        · exact absurd hkc Sum.inr_ne_inl
      refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
      have hone : ∀ W ∈ I.filter (fun W => c ∈ W),
          (((Qon W).filter fun K0 => Sum.inl c ∈ K0).image (image (liftLab W))).card ≤ 1 := by
        intro W hW
        refine card_image_le.trans (card_le_one.2 fun K0 hK0 K0' hK0' => ?_)
        obtain ⟨hK0, hc0⟩ := mem_filter.1 hK0
        obtain ⟨hK0', hc0'⟩ := mem_filter.1 hK0'
        by_contra hne
        exact disjoint_left.1 ((hT W (mem_filter.1 hW).1).on_disj hK0 hK0' hne) hc0 hc0'
      calc _ ≤ ∑ _W ∈ I.filter (fun W => c ∈ W), 1 := sum_le_sum hone
        _ = (I.filter fun W => c ∈ W).card := by rw [card_eq_sum_ones]
        _ ≤ (𝒲.filter fun W => c ∈ W).card :=
            card_le_card (fun W hW => mem_filter.2 ⟨(mem_filter.1 (mem_filter.1 hW).1).1,
              (mem_filter.1 hW).2⟩)
        _ ≤ C' := hFam.mult_le c (by
            rcases mem_union.1 hcXR with h' | h'
            · exact mem_union_left _ h'
            · exact mem_union_right _ h')
        _ ≤ _ := by omega
    · -- a gadget copy lies in at most two cliques
      have hsub : 𝒬.filter (fun K => Sum.inr (W, t) ∈ K) ⊆
          (((Qon W).filter fun K0 => Sum.inr t ∈ K0) ∪
            ((Qoff W).filter fun K0 => Sum.inr t ∈ K0)).image (image (liftLab W)) := by
        intro K hK
        obtain ⟨hK𝒬, htK⟩ := mem_filter.1 hK
        obtain ⟨W', hW', hKW⟩ := mem_biUnion.1 hK𝒬
        obtain ⟨K0, hK0, rfl⟩ := mem_image.1 hKW
        obtain ⟨k, hk, hkt⟩ := mem_image.1 htK
        rcases k with c | t'
        · exact absurd hkt Sum.inl_ne_inr
        · simp only [liftLab, Sum.elim_inr, Sum.inr.injEq, Prod.mk.injEq] at hkt
          obtain ⟨rfl, rfl⟩ := hkt
          refine mem_image_of_mem _ ?_
          rcases mem_union.1 hK0 with h' | h'
          · exact mem_union_left _ (mem_filter.2 ⟨h', hk⟩)
          · exact mem_union_right _ (mem_filter.2 ⟨h', hk⟩)
      refine (card_le_card hsub).trans (card_image_le.trans ((card_union_le _ _).trans ?_))
      have hle : ∀ 𝒦 : Finset (Finset (E' ⊕ Finset (Fin n ⊕ Fin hg))),
          (𝒦 : Set (Finset (E' ⊕ Finset (Fin n ⊕ Fin hg)))).PairwiseDisjoint id →
          (𝒦.filter fun K0 => Sum.inr t ∈ K0).card ≤ 1 := by
        intro 𝒦 h𝒦
        refine card_le_one.2 fun K0 hK0 K0' hK0' => ?_
        obtain ⟨hK0, hc0⟩ := mem_filter.1 hK0
        obtain ⟨hK0', hc0'⟩ := mem_filter.1 hK0'
        by_contra hne
        exact disjoint_left.1 (h𝒦 hK0 hK0' hne) hc0 hc0'
      by_cases hW : W ∈ I
      · have := hle _ (hT W hW).on_disj
        have := hle _ (hT W hW).off_disj
        omega
      · -- not a copy of `A`
        exfalso
        rcases mem_union.1 hx with h' | h'
        · rw [hXg''] at h'
          obtain ⟨c, -, hc⟩ := mem_image.1 h'
          exact Sum.inl_ne_inr hc
        · rcases mem_union.1 h' with h'' | h''
          · obtain ⟨c, -, hc⟩ := mem_image.1 h''
            exact Sum.inl_ne_inr hc
          · obtain ⟨W', hW', hxW⟩ := mem_biUnion.1 h''
            obtain ⟨t', -, ht'⟩ := mem_image.1 hxW
            rw [Sum.inr.injEq, Prod.mk.injEq] at ht'
            exact hW (ht'.1 ▸ hW')
  · -- the degree bound
    have hnat : ∀ S : Finset (Fin n), S.card + 1 = r →
        mdeg ends'' A S ≤ (C' + Ce * 3 ^ r) * D0 := by
      intro S hS
      have hS' : S.card = r - 1 := by omega
      have h1 : mdeg ends'' A S ≤ mdeg ends'' (R.image Sum.inl) S + mdeg ends'' Gad S := by
        unfold mdeg
        rw [hA, filter_union]
        exact card_union_le _ _
      have h2 : mdeg ends'' (R.image Sum.inl) S ≤ C' * D0 := by
        have : mdeg ends'' (R.image Sum.inl) S = mdeg ends' R S := by
          rw [mdeg, filter_image, card_image_of_injective _ Sum.inl_injective]; rfl
        rw [this]
        have hsub : R.filter (fun c => S ⊆ ends' c) ⊆
            (𝒲.filter fun W => S ⊆ W.biUnion ends').biUnion id := by
          intro c hc
          obtain ⟨hcR, hSc⟩ := mem_filter.1 hc
          obtain ⟨W, hW, hcW⟩ := hRsub c hcR
          exact mem_biUnion.2 ⟨W, mem_filter.2 ⟨hW, hSc.trans (subset_biUnion_of_mem ends' hcW)⟩,
            hcW⟩
        calc mdeg ends' R S ≤ ∑ W ∈ 𝒲.filter (fun W => S ⊆ W.biUnion ends'), (id W).card :=
              (card_le_card hsub).trans card_biUnion_le
          _ ≤ ∑ _W ∈ 𝒲.filter (fun W => S ⊆ W.biUnion ends'), C' :=
              sum_le_sum fun W hW => hFam.card_le W (mem_filter.1 hW).1
          _ = (𝒲.filter fun W => S ⊆ W.biUnion ends').card * C' := by rw [sum_const, smul_eq_mul]
          _ ≤ D0 * C' := Nat.mul_le_mul_right _ (hD0S S hS')
          _ = C' * D0 := mul_comm _ _
      have h3 : mdeg ends'' Gad S ≤ Ce * (3 ^ r * D0) := by
        refine le_trans ?_ (hsum S hS')
        unfold mdeg
        rw [hGad, filter_biUnion]
        refine card_biUnion_le.trans (sum_le_sum fun W hW => ?_)
        rw [filter_image, card_image_of_injective _ (fun t t' h => by
          simpa using h), newEdges, filter_image]
        refine le_of_eq (card_image_of_injOn ?_).symm
        intro t ht t' ht' htt
        exact image_inj_of_injOn (injOn_emb (hvalid W hW))
          (hTG W hW t (mem_filter.1 ht).1) (hTG W hW t' (mem_filter.1 ht').1) htt
      calc mdeg ends'' A S ≤ C' * D0 + Ce * (3 ^ r * D0) := h1.trans (Nat.add_le_add h2 h3)
        _ = (C' + Ce * 3 ^ r) * D0 := by ring
    have hmax : mmaxDeg r ends'' A ≤ (C' + Ce * 3 ^ r) * D0 :=
      Finset.sup_le fun S hS => hnat S (mem_filter.1 hS).2
    have hBD : (0 : ℝ) ≤ bigDelta r ends X :=
      le_trans (Nat.cast_nonneg _) (le_max_left _ _)
    calc (mmaxDeg r ends'' A : ℝ) ≤ ((C' + Ce * 3 ^ r) * D0 : ℕ) := by exact_mod_cast hmax
      _ = (C' + Ce * 3 ^ r : ℝ) * D0 := by push_cast; ring
      _ ≤ (C' + Ce * 3 ^ r : ℝ) * (C' * bigDelta r ends X) := by gcongr
      _ = (((C' + Ce * 3 ^ r) * C' : ℕ) : ℝ) * bigDelta r ends X := by push_cast; ring
      _ ≤ (((C' + Ce * 3 ^ r) * C' + 3 * Ce + C' + 2 : ℕ) : ℝ) * bigDelta r ends X := by
          gcongr; omega
  · -- flatness
    intro c hc
    rcases mem_union.1 hc with h' | h'
    · obtain ⟨c', hc', rfl⟩ := mem_image.1 h'
      exact hflat c' hc'
    · obtain ⟨W, hW, hcW⟩ := mem_biUnion.1 h'
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hcW
      obtain ⟨p, hp⟩ := (hT W hW).wf.edge_aux t ht
      show (placeEdge (Φ W) t \ Y).card ≤ r - 1
      have hmem : Φ W p ∈ placeEdge (Φ W) t := mem_image_of_mem (emb (Φ W)) hp
      have hlt : (placeEdge (Φ W) t \ Y).card < (placeEdge (Φ W) t).card :=
        card_lt_card ⟨sdiff_subset, fun h'' => (mem_sdiff.1 (h'' hmem)).2 (hrange W hW p)⟩
      rw [hplace_card W hW t ht] at hlt
      omega

/-- **Theorem 3.7 of arXiv:2402.17855v1**, for all `q > r ≥ 1`. -/
theorem theorem_3_7 : Theorem_3_7 := fun _ _ hr hrq => theorem_3_7_for_all hr hrq

/-- The inductive form of **Theorem 3.8** (`Theorem_3_8_for`: Theorem 3.7 in the lower
uniformities implies the conclusion of Theorem 3.8) has its hypothesis discharged by
`theorem_3_7`; this recovers `theorem_3_8_conclusion` through the article's induction. -/
theorem theorem_3_8_conclusion_via_3_7 (q r : ℕ) (hr : 1 ≤ r) (hrq : r < q) :
    Theorem_3_8_conclusion q r :=
  theorem_3_8 q r hr hrq fun _ _ hr' _ hrq' => theorem_3_7_for_all hr' hrq'

end RefinedAbsorption.Faithful2024
