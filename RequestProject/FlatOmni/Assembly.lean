module
public import RequestProject.FlatOmni.Attach
public import RequestProject.FlatOmni.SharpBounds
public import RequestProject.Local.CliqueOmni

/-!
# Theorem 3.7 for graphs with flatness and clique pieces (sparse form)

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Theorem 3.7 (Refined Multi-Omni-Absorber
Theorem, with the flatness conclusion (2)) for graphs, with the hypothesis `Δ(L) ≤ n / C` of the
paper, and Remark 3.9 (the pieces of an omni-absorber are cliques `K_q`).
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

`FlatCliqueOmniAbsorbersS q a` is `FlatCliqueOmniAbsorbers q a` (see `Local/CliqueOmni.lean`) with
the extra hypothesis `Ch · d ≤ |P|`: the degree `d` of `L` is at most a small fraction of the
reserve `P`, as in the hypothesis `Δ_{r-1}(X) ≤ n / C` of Theorem 3.7.

**`flatCliqueOmniAbsorbersS_two`**: `FlatCliqueOmniAbsorbersS q (sharpCost 2)` for every `q > 2`.
The construction:

1. a local refiner inside `Y ∪ P` with degrees `≤ C (d + sharpPot 2 |P|)` (`localRefiner`);
2. every new copy is replaced by fake edges placed in `P`, giving a simple graph `F` of new edges,
   each meeting `P` (`fakeStage`);
3. every piece receives a bounded absorber placed in `P` (`absStage`);
4. the pieces are the cliques of the on/off decompositions of the absorbers
   (`cliquePieces_refiner`).

Finally `sharpPot 2 m ≤ 6 · sharpCost 2 m` (`sharpPot_two_le`).
-/

@[expose] public section

namespace RefinedAbsorption.FlatOmni

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.FlatDown
  RefinedAbsorption.Sharp RefinedAbsorption.RefineDown

/-- **Flat clique omni-absorbers for graphs, sparse form** (Theorem 3.7 for `r = 2` with the
hypothesis `Δ(L) ≤ |P| / Ch`; see the module docstring). -/
def FlatCliqueOmniAbsorbersS (q : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ K : ℕ, ∃ C Ch : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
    (Y P : Finset (Fin n)) (L : Finset E) (d : ℕ),
    Disjoint Y P → Y.card ≤ K * P.card → Ch ≤ P.card → Ch * d ≤ P.card →
    MIsRGraph 2 ends L → (∀ x ∈ L, ends x ⊆ Y) → (∀ v, mdeg ends L {v} ≤ d) →
    (∀ e, mult ends L e ≤ K) →
    ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
      (R : Finset E') (𝒲 : Finset (Finset E')),
      Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
      IsMultiRefiner q 2 C ends' (L.image g) R 𝒲 ∧
      (∀ c ∈ R, ends' c ⊆ Y ∪ P ∧ (ends' c ∩ P).Nonempty) ∧
      (∀ v, mdeg ends' R {v} ≤ C * (d + a P.card)) ∧
      (∀ e, mult ends' R e ≤ C) ∧
      (∀ W ∈ 𝒲, ∀ x ∈ W.biUnion ends', ∀ y ∈ W.biUnion ends', x ≠ y →
        ∃ c ∈ W, ends' c = {x, y})

/-- Without the smallness hypothesis the statement is stronger. -/
theorem FlatCliqueOmniAbsorbers.toS {q : ℕ} {a : ℕ → ℕ}
    (h : RefinedAbsorption.Local.FlatCliqueOmniAbsorbers q a) : FlatCliqueOmniAbsorbersS q a := by
  intro K
  obtain ⟨C, Ch, hC⟩ := h K
  exact ⟨C, Ch, fun n E _ ends Y P L d hYP hYK hCh _ hLr hLY hdeg hmult =>
    hC n ends Y P L d hYP hYK hCh hLr hLY hdeg hmult⟩

section Inr

variable {n : ℕ} {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))

theorem injOn_image_inr (G : Finset (Finset (Fin n))) :
    Set.InjOn (Sum.elim ends id) ↑(G.image (Sum.inr : Finset (Fin n) → E ⊕ Finset (Fin n))) := by
  intro a ha b hb hab
  obtain ⟨f, -, rfl⟩ := mem_image.1 (mem_coe.1 ha)
  obtain ⟨f', -, rfl⟩ := mem_image.1 (mem_coe.1 hb)
  change f = f' at hab
  rw [hab]

theorem mdeg_image_inr (G : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    mdeg (Sum.elim ends id) (G.image (Sum.inr : Finset (Fin n) → E ⊕ Finset (Fin n))) S =
      deg G S := by
  rw [mdeg_eq_deg_image (injOn_image_inr ends G), image_image, Sum.elim_comp_inr, image_id]

theorem mult_image_inr_le (G : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    mult (Sum.elim ends id) (G.image (Sum.inr : Finset (Fin n) → E ⊕ Finset (Fin n))) e ≤ 1 := by
  refine card_le_one.2 fun a ha b hb => ?_
  obtain ⟨ha, hae⟩ := mem_filter.1 ha
  obtain ⟨hb, hbe⟩ := mem_filter.1 hb
  exact injOn_image_inr ends G (mem_coe.2 ha) (mem_coe.2 hb) (hae.trans hbe.symm)

end Inr

/-- **Theorem 3.7 for graphs, with flatness and clique pieces** (sparse form, additive term
`sharpCost 2 m = ⌈m^{1/2}⌉ (⌊log₂ m⌋ + 1)`). -/
theorem flatCliqueOmniAbsorbersS_two {q : ℕ} (hq : 2 < q) :
    FlatCliqueOmniAbsorbersS q (sharpCost 2) := by
  classical
  intro K
  obtain ⟨C₁, Ch₁, hloc⟩ := localRefiner hq K
  obtain ⟨Cf, C₂, hfake⟩ := fakeStage hq C₁ K
  obtain ⟨Ca, habs⟩ := absStage hq C₂ K
  set M := Cf * C₁ + Ca + Ca * C₂ * C₁ with hM
  obtain ⟨m₀, hm₀⟩ := exists_mul_sharpPot_le (r := 2) le_rfl (3 * M)
  set C₃ := 2 * (C₂ + 1) + q.choose 2 with hC₃
  set Cd := C₂ * C₁ + Ca + Ca * C₂ * C₁ with hCd
  refine ⟨C₃ + 7 * Cd + 1, 3 * M + Ch₁ + m₀ + 1, ?_⟩
  intro n E _ ends Y P L d hYP hYK hCh hChd hLr hLY hdeg hmult
  set s := sharpPot 2 P.card with hs
  have hP0 : 0 < P.card := by omega
  have hdeg1 : ∀ v, mdeg ends L {v} ≤ d + 1 := fun v => (hdeg v).trans (Nat.le_succ d)
  obtain ⟨E', _, g, ends', R, 𝒲, hg, hge, hgR, href, hRYP, hone, hdegR, hpdR⟩ :=
    hloc n ends Y P L (d + 1) hYK (by omega) hLr hLY (by omega) hdeg1
  set X := d + 1 + s with hX
  set B := C₁ * X with hB
  -- smallness
  have hs3 : 3 * (M * s) ≤ P.card := by
    have := hm₀ P.card (by omega); rw [mul_assoc] at this; exact this
  have hd3 : 3 * (M * d) ≤ P.card := by
    rw [← mul_assoc]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hChd
  have h13 : 3 * M ≤ P.card := by omega
  have hsmall : M * X ≤ P.card := by
    rw [hX, mul_add, mul_add, mul_one]; omega
  -- 2. fake edges
  have hXY : ∀ c ∈ L.image g, ends' c ⊆ Y := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
    rw [hge]; exact hLY x hx
  have hBf : Cf * B ≤ P.card := by
    calc Cf * B = (Cf * C₁) * X := by rw [hB]; ring
      _ ≤ M * X := Nat.mul_le_mul_right _ (by omega)
      _ ≤ P.card := hsmall
  obtain ⟨F, 𝒱, h𝒱, hF, hdegF, hpd𝒱, hinj𝒱⟩ := hfake n ends' (L.image g) R 𝒲 Y P B href hXY
    hRYP hYP hone hdegR hpdR hYK hBf hP0
  -- 3. absorbers
  set B' := d + C₂ * B with hB'
  have hhost : ∀ v, deg ((L.image g).image ends' ∪ F) {v} ≤ B' := by
    intro v
    have h1 : deg ((L.image g).image ends') {v} ≤ d := by
      rw [image_image]
      have : ends' ∘ g = ends := funext hge
      rw [this]
      unfold deg
      rw [filter_image]
      exact card_image_le.trans (hdeg v)
    unfold deg at h1 ⊢
    rw [filter_union]
    exact (card_union_le _ _).trans (Nat.add_le_add h1 (hdegF v))
  have hspan : ∀ W ∈ 𝒱, W.biUnion (Sum.elim ends' id) ⊆ Y ∪ P := by
    intro W hW x hx
    obtain ⟨y, hy, hxy⟩ := mem_biUnion.1 hx
    rcases mem_union.1 (h𝒱.subset W hW hy) with h1 | h1
    · obtain ⟨c, hc, rfl⟩ := mem_image.1 h1
      exact mem_union_left _ (hXY c hc hxy)
    · obtain ⟨f, hf, rfl⟩ := mem_image.1 h1
      exact (hF f hf).1 hxy
  have hU : (Y ∪ P).card ≤ (K + 1) * P.card :=
    (card_union_le Y P).trans (by rw [add_mul, one_mul]; omega)
  have hCaB : Ca * B' ≤ P.card := by
    calc Ca * B' = Ca * d + (Ca * C₂ * C₁) * X := by rw [hB', hB]; ring
      _ ≤ Ca * X + (Ca * C₂ * C₁) * X :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
      _ ≤ M * X := by rw [← add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      _ ≤ P.card := hsmall
  obtain ⟨AW, Qon, Qoff, hA, hAedge, hdegA⟩ := habs n ends' (L.image g) F 𝒱 (Y ∪ P) P B' h𝒱
    hinj𝒱 hspan hU hhost (fun v => (hpd𝒱 v).trans (Nat.le_add_left _ _)) hCaB hP0
  -- 4. clique pieces
  obtain ⟨hcl, hclique⟩ := cliquePieces_refiner h𝒱 hA
  refine ⟨E' ⊕ Finset (Fin n), inferInstance, Sum.inl ∘ g, Sum.elim ends' id,
    (F ∪ 𝒱.biUnion AW).image Sum.inr, cliqueFam ends' 𝒱 AW Qon Qoff,
    Sum.inl_injective.comp hg, fun c => by simp [hge], fun c hc x => ?_, ?_, ?_, fun v => ?_,
    fun e => ?_, hclique⟩
  · obtain ⟨f, -, rfl⟩ := mem_image.1 hc
    exact Sum.inl_ne_inr
  · rw [← image_image]
    exact hcl.mono (by omega)
  · intro c hc
    obtain ⟨f, hf, rfl⟩ := mem_image.1 hc
    change f ⊆ Y ∪ P ∧ (f ∩ P).Nonempty
    rcases mem_union.1 hf with hf | hf
    · exact hF f hf
    · obtain ⟨W, hW, hfW⟩ := mem_biUnion.1 hf
      obtain ⟨h1, h2⟩ := hAedge W hW f hfW
      refine ⟨?_, h2⟩
      rw [union_assoc, union_self] at h1
      exact h1
  · rw [mdeg_image_inr]
    have hsc1 : 1 ≤ sharpCost 2 P.card := one_le_sharpCost 2 (by omega)
    have hs6 : s ≤ 6 * sharpCost 2 P.card := sharpPot_two_le _
    have hX7 : X ≤ 7 * (d + sharpCost 2 P.card) := by omega
    have hdu : deg (F ∪ 𝒱.biUnion AW) {v} ≤ C₂ * B + Ca * B' := by
      unfold deg
      rw [filter_union]
      exact (card_union_le _ _).trans (Nat.add_le_add (hdegF v) (hdegA v))
    refine hdu.trans ?_
    have hdX : Ca * d ≤ Ca * X := Nat.mul_le_mul_left _ (by omega)
    calc C₂ * B + Ca * B' = C₂ * C₁ * X + Ca * d + Ca * C₂ * C₁ * X := by rw [hB', hB]; ring
      _ ≤ C₂ * C₁ * X + Ca * X + Ca * C₂ * C₁ * X := by omega
      _ = Cd * X := by rw [hCd]; ring
      _ ≤ Cd * (7 * (d + sharpCost 2 P.card)) := Nat.mul_le_mul_left _ hX7
      _ = (7 * Cd) * (d + sharpCost 2 P.card) := by ring
      _ ≤ (C₃ + 7 * Cd + 1) * (d + sharpCost 2 P.card) :=
          Nat.mul_le_mul_right _ (by omega)
  · exact (mult_image_inr_le ends' _ e).trans (by omega)

end RefinedAbsorption.FlatOmni
