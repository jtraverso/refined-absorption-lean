module
public import RequestProject.Sharp.SparsCount
public import RequestProject.FlatDown.MultDegree

/-!
# The refiner of the Edge Sparsification Lemma

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Lemma 3.12.

Given a partition `φ : V → Fin k` and special sets `Sp I` (of size `q - r`, avoiding the parts
of `I`), every copy `x` receives its private cliques on `sClique x = ends x ∪ Sp(type of x)`
(`R₁`, the clique refiner), and the Multiplicity Reduction Lemma is applied to `R₁`.
**`sparsify_build`** records the resulting residual multi-refiner and bounds its degrees by the
two counting quantities of `Sharp/SparsCount.lean`: the number of cliques containing an
`(r-1)`-set `S`, and the link of `S` in the cliques.
-/

@[expose] public section

namespace RefinedAbsorption.Sharp

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Dense
  RefinedAbsorption.RefineDown

/-- An `r`-multigraph of multiplicity `≤ M` inside `Z` has `mdeg Y S ≤ M · |link of S|`. -/
theorem mdeg_le_mult_link {V E : Type*} [DecidableEq V] {r M : ℕ} {ends : E → Finset V}
    {Y : Finset E} {Z : Finset V} (hYr : MIsRGraph r ends Y) (hYZ : ∀ c ∈ Y, ends c ⊆ Z)
    (hmult : ∀ e, mult ends Y e ≤ M) (S : Finset V) (hS : S.card + 1 = r) :
    mdeg ends Y S ≤ M * (Z.filter fun v => v ∉ S ∧ ∃ c ∈ Y, ends c = insert v S).card := by
  classical
  set Lk := Z.filter fun v => v ∉ S ∧ ∃ c ∈ Y, ends c = insert v S
  have hsub : Y.filter (fun c => S ⊆ ends c) ⊆
      Lk.biUnion fun v => Y.filter (fun c => ends c = insert v S) := by
    intro c hc
    obtain ⟨hcY, hSc⟩ := mem_filter.1 hc
    have hcard : (ends c \ S).card = 1 := by
      rw [card_sdiff_of_subset hSc, hYr c hcY]; omega
    obtain ⟨v, hv⟩ := card_eq_one.1 hcard
    have hvc : v ∈ ends c \ S := by rw [hv]; exact mem_singleton_self v
    have hce : ends c = insert v S := by
      ext w
      constructor
      · intro hw
        by_cases hwS : w ∈ S
        · exact mem_insert_of_mem hwS
        · have : w ∈ ends c \ S := mem_sdiff.2 ⟨hw, hwS⟩
          rw [hv, mem_singleton] at this
          rw [this]; exact mem_insert_self _ _
      · intro hw
        rcases mem_insert.1 hw with rfl | hw
        · exact (mem_sdiff.1 hvc).1
        · exact hSc hw
    refine mem_biUnion.2 ⟨v, mem_filter.2 ⟨hYZ c hcY (mem_sdiff.1 hvc).1, (mem_sdiff.1 hvc).2,
      c, hcY, hce⟩, mem_filter.2 ⟨hcY, hce⟩⟩
  calc mdeg ends Y S ≤ _ := card_le_card hsub
    _ ≤ ∑ v ∈ Lk, (Y.filter (fun c => ends c = insert v S)).card := card_biUnion_le
    _ ≤ ∑ _v ∈ Lk, M := sum_le_sum fun v _ => hmult _
    _ = M * Lk.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- The cliques lie in `U`. -/
theorem sClique_subset {V E : Type} [DecidableEq V] {k : ℕ} {ends : E → Finset V}
    {φ : V → Fin k} {Sp : Multiset (Fin k) → Finset V} {U : Finset V} {x : E}
    (hx : ends x ⊆ U) (hSp : Sp (ptype φ (ends x)) ⊆ U.filter fun v => φ v ∉ ptype φ (ends x)) :
    sClique ends φ Sp x ⊆ U :=
  union_subset hx (hSp.trans (filter_subset _ _))

theorem card_sClique {V E : Type} [DecidableEq V] {k s r : ℕ} {ends : E → Finset V}
    {φ : V → Fin k} {Sp : Multiset (Fin k) → Finset V} {U : Finset V} {x : E}
    (hxr : (ends x).card = r) (hSpc : (Sp (ptype φ (ends x))).card = s)
    (hSp : Sp (ptype φ (ends x)) ⊆ U.filter fun v => φ v ∉ ptype φ (ends x)) :
    (sClique ends φ Sp x).card = r + s := by
  unfold sClique
  rw [card_union_of_disjoint, hxr, hSpc]
  rw [disjoint_left]
  intro v hv hv'
  exact (mem_filter.1 (hSp hv')).2 (mem_ptype φ hv)

/-- **The refiner of the Edge Sparsification Lemma**; see the module docstring. -/
theorem sparsify_build (q r : ℕ) (hr : 2 ≤ r) (hrq : r < q) :
    ∃ M' Cm : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (U : Finset (Fin n)) (X : Finset E) {k : ℕ} (φ : Fin n → Fin k)
      (Sp : Multiset (Fin k) → Finset (Fin n)),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) →
      (∀ x ∈ X, (Sp (ptype φ (ends x))).card = q - r ∧
        Sp (ptype φ (ends x)) ⊆ U.filter fun v => φ v ∉ ptype φ (ends x)) →
      ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
        (R Y : Finset E') (𝒲 : Finset (Finset E')),
        Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
        IsResidualMultiRefiner q r (q.choose r + Cm) ends' (X.image g) R Y 𝒲 ∧ Y ⊆ R ∧
        (∀ c ∈ R, ends' c ⊆ U) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' Y S ≤ M' *
          (U.filter fun v => v ∉ S ∧ ∃ x ∈ X, insert v S ⊆ sClique ends φ Sp x ∧
            insert v S ≠ ends x).card) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ (1 + (M' + 2) ^ 2) *
          (fakeModulus q r * (q.choose r * (X.filter fun x => S ⊆ sClique ends φ Sp x).card))) ∧
        (∀ W ∈ 𝒲, (W.filter (· ∈ X.image g)).card ≤ 1) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤
          (X.filter fun x => S ⊆ sClique ends φ Sp x).card + Cm * ((1 + (M' + 2) ^ 2) *
          (fakeModulus q r * (q.choose r * (X.filter fun x => S ⊆ sClique ends φ Sp x).card)))) := by
  obtain ⟨M', Cm, -, hmr⟩ := multiplicityReduction_quant q r hrq.le
  refine ⟨M', Cm, ?_⟩
  intro n E _ ends U X k φ Sp hXr hXU hSp
  set Vx := sClique ends φ Sp with hVx
  set Mf := fakeModulus q r with hMf
  have hsub : ∀ x ∈ X, ends x ⊆ Vx x := fun x _ => subset_union_left
  have hq : ∀ x ∈ X, (Vx x).card = q := by
    intro x hx
    rw [hVx, card_sClique (hXr x hx) (hSp x hx).1 (hSp x hx).2]; omega
  have hVU : ∀ x ∈ X, Vx x ⊆ U := fun x hx => sClique_subset (hXU x hx) (hSp x hx).2
  have h₁ := cliqueRefiner_residual hrq.le hXr hsub hq
  set R₁ := cliqueR ends r Mf Vx X with hR₁
  have hR₁r : MIsRGraph r (cEnds ends) R₁ := fun c hc => h₁.rgraph c (mem_union_right _ hc)
  obtain ⟨N, _, endsN, Rm, Ym, 𝒲m, hRm, hYmR, hm, hmult, hdegm, hparm⟩ :=
    hmr (cEnds ends) R₁ hR₁r
  have hinrfresh : ∀ c ∈ Rm.image (Sum.inr : N → CLab (Fin n) E ⊕ N), ∀ x : CLab (Fin n) E,
      Sum.inl x ≠ c := by
    intro c hc x hx
    obtain ⟨y, -, rfl⟩ := mem_image.1 hc
    exact Sum.inl_ne_inr hx
  have h12 := IsResidualMultiRefiner.compose (Sum.inl : CLab (Fin n) E → CLab (Fin n) E ⊕ N)
    Sum.inl_injective (fun c => rfl) h₁ subset_union_right hm hinrfresh
  have hone := oneX_compose (Sum.inl : CLab (Fin n) E → CLab (Fin n) E ⊕ N) Sum.inl_injective
    h₁.disjoint subset_rfl (cliqueRefiner_oneX (ends := ends) (r := r) (Vx := Vx) (X := X)) hm
    hinrfresh
  rw [image_image] at h12 hone
  set ends' : CLab (Fin n) E ⊕ N → Finset (Fin n) := Sum.elim (cEnds ends) endsN with hends'
  have hmdR₁ : ∀ S, mdeg (cEnds ends) R₁ S ≤
      Mf * (q.choose r * (X.filter fun x => S ⊆ Vx x).card) := fun S => mdeg_cliqueR_le hq S
  have hmdR : ∀ S, mdeg ends' (R₁.image Sum.inl ∪ Rm.image Sum.inr) S ≤ (1 + (M' + 2) ^ 2) *
      (Mf * (q.choose r * (X.filter fun x => S ⊆ Vx x).card)) := by
    intro S
    refine (mdeg_union_le _ _ _ S).trans ?_
    have e1 : mdeg ends' (R₁.image Sum.inl) S = mdeg (cEnds ends) R₁ S :=
      mdeg_image_eq (A := R₁) (fun c _ => rfl) Sum.inl_injective.injOn subset_rfl S
    have e2 : mdeg ends' (Rm.image Sum.inr) S ≤ (M' + 2) ^ 2 * mdeg (cEnds ends) R₁ S :=
      hdegm S
    rw [e1]
    have := hmdR₁ S
    calc mdeg (cEnds ends) R₁ S + mdeg ends' (Rm.image Sum.inr) S
        ≤ mdeg (cEnds ends) R₁ S + (M' + 2) ^ 2 * mdeg (cEnds ends) R₁ S := by omega
      _ = (1 + (M' + 2) ^ 2) * mdeg (cEnds ends) R₁ S := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ this
  refine ⟨CLab (Fin n) E ⊕ N, inferInstance, fun x => Sum.inl (Sum.inl x), ends',
    R₁.image Sum.inl ∪ Rm.image Sum.inr, Ym, _,
    fun x y h => Sum.inl_injective (Sum.inl_injective h), fun c => rfl, ?_, h12,
    hYmR.trans subset_union_right, ?_, ?_, fun S _ => hmdR S, ?_, ?_⟩
  · intro c hc x hx
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      obtain ⟨_, _, _, _, _, _, _, _, hc₁'⟩ := mem_cliqueR.1 hc₁
      rw [hc₁'] at hx
      exact Sum.inl_ne_inr (Sum.inl_injective hx)
    · obtain ⟨y, -, rfl⟩ := mem_image.1 h
      exact Sum.inl_ne_inr hx
  · intro c hc
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      obtain ⟨x, hx, h1, -, -⟩ := cliqueRefiner_ends hc₁
      exact h1.trans (hVU x hx)
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 h
      obtain ⟨c₁, hc₁, he⟩ := mem_image.1 (hRm y hy)
      show endsN y ⊆ U
      rw [← he]
      obtain ⟨x, hx, h1, -, -⟩ := cliqueRefiner_ends hc₁
      exact h1.trans (hVU x hx)
  · intro S hS
    have hYr : MIsRGraph r ends' Ym := fun c hc => hm.rgraph c (mem_union_right _ (hYmR hc))
    have hYU : ∀ c ∈ Ym, ends' c ⊆ U := by
      intro c hc
      obtain ⟨y, hy, rfl⟩ := mem_image.1 (hYmR hc)
      obtain ⟨c₁, hc₁, he⟩ := mem_image.1 (hRm y hy)
      show endsN y ⊆ U
      rw [← he]
      obtain ⟨x, hx, h1, -, -⟩ := cliqueRefiner_ends hc₁
      exact h1.trans (hVU x hx)
    refine (mdeg_le_mult_link hYr hYU hmult S (by omega)).trans (Nat.mul_le_mul_left _ ?_)
    refine card_le_card (monotone_filter_right _ fun v _ hv => ⟨hv.1, ?_⟩)
    obtain ⟨c, hc, hce⟩ := hv.2
    obtain ⟨y, hy, rfl⟩ := mem_image.1 (hYmR hc)
    obtain ⟨c₁, hc₁, he⟩ := mem_image.1 (hRm y hy)
    obtain ⟨x, hx, h1, -, h3⟩ := cliqueRefiner_ends hc₁
    have : cEnds ends c₁ = insert v S := he.trans hce
    exact ⟨x, hx, this ▸ h1, this ▸ h3⟩
  · exact hone
  · intro S hS
    have hSne : S.Nonempty := by rw [← card_pos, hS]; omega
    have hm1 : pdeg ends' 𝒲m S ≤ Cm * mdeg ends' (R₁.image Sum.inl ∪ Rm.image Sum.inr) S :=
      pdeg_le_of_parallel hm hparm hSne
    refine (pdeg_union_le _ _ _ S).trans (Nat.add_le_add ?_ (hm1.trans
      (Nat.mul_le_mul_left _ (hmdR S))))
    exact (pdeg_image_le Sum.inl (fun c => rfl) _ S).trans (pdeg_cliqueW_le hsub S)

end RefinedAbsorption.Sharp
