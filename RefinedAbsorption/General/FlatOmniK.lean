module
public import RefinedAbsorption.General.LocalK
public import RefinedAbsorption.General.FakeStageK
public import RefinedAbsorption.General.AttachK
public import RefinedAbsorption.FlatOmni.Assembly

/-!
# Theorem 3.7 in every uniformity (flatness, clique pieces, small trace), sparse form

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Theorem 3.7 and Remark 3.9.
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

**`flatOmniK_of_levels`**: `FlatOmniK q k (sharpCost k)` from the sparse link levels of
uniformity `k`.  The construction: a local refiner inside `Y ∪ P` (`localRefinerK`), fake edges
for its new copies placed in `P` (`fakeStageK`), bounded absorbers for its pieces placed in `P`
(`absStageK`), and the cliques of the on/off decompositions as pieces (`cliquePieces_refinerK`).
Every clique piece contains at most one old copy, so its span meets `Y` in at most `k` vertices.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.FlatDown
  RefinedAbsorption.Sharp RefinedAbsorption.RefineDown RefinedAbsorption.FlatOmni

theorem sharpCost_le_sharpPot (r : ℕ) {m : ℕ} (hm : 1 ≤ m) : sharpCost r m ≤ sharpPot r m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [sharpPot_succ]; exact Nat.le_add_right _ _

/-- For every `c`, eventually `c · sharpCost r m ≤ m`. -/
theorem exists_mul_sharpCost_le {r : ℕ} (hr : 2 ≤ r) (c : ℕ) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → c * sharpCost r m ≤ m := by
  obtain ⟨m₀, hm₀⟩ := exists_mul_sharpPot_le hr c
  exact ⟨m₀ + 1, fun m hm => (Nat.mul_le_mul_left _ (sharpCost_le_sharpPot r (by omega))).trans
    (hm₀ m (by omega))⟩

/-- Every clique piece contains at most one old copy. -/
theorem cliqueFam_old_le_one {n : ℕ} {E : Type} [DecidableEq E] {ends : E → Finset (Fin n)}
    {𝒱 : Finset (Finset (E ⊕ Finset (Fin n)))}
    {AW Qon Qoff : Finset (E ⊕ Finset (Fin n)) → Finset (Finset (Fin n))} {X : Finset E}
    (hone : ∀ W ∈ 𝒱, (W.filter fun y => y ∈ X.image Sum.inl).card ≤ 1) :
    ∀ P ∈ cliqueFam ends 𝒱 AW Qon Qoff, (P.filter fun y => y ∈ X.image Sum.inl).card ≤ 1 := by
  intro P hP
  rcases mem_union.1 hP with hP | hP
  · obtain ⟨⟨W, Q⟩, hWQ, rfl⟩ := mem_image.1 hP
    refine le_trans (card_le_card fun y hy => ?_) (hone W (mem_sigma.1 hWQ).1)
    obtain ⟨hyP, hyX⟩ := mem_filter.1 hy
    obtain ⟨hyW, -⟩ := mem_pOn.1 hyP
    rcases mem_union.1 hyW with h1 | h1
    · exact mem_filter.2 ⟨h1, hyX⟩
    · exfalso
      obtain ⟨f, -, rfl⟩ := mem_image.1 h1
      obtain ⟨x, -, hx⟩ := mem_image.1 hyX
      exact Sum.inl_ne_inr hx
  · obtain ⟨⟨W, Q⟩, -, rfl⟩ := mem_image.1 hP
    refine le_of_eq_of_le (card_eq_zero.2 (filter_eq_empty_iff.2 fun y hy hyX => ?_)) zero_le_one
    obtain ⟨hyA, -⟩ := mem_pOff.1 hy
    obtain ⟨f, -, rfl⟩ := mem_image.1 hyA
    obtain ⟨x, -, hx⟩ := mem_image.1 hyX
    exact Sum.inl_ne_inr hx

/-- **Small trace.**  If every `k`-subset of the span of a piece carries a copy of the piece,
every new copy meets `P`, and a piece contains at most one old copy, then the span of the piece
meets `Y` (disjoint from `P`) in at most `k` vertices. -/
theorem trace_le_of_clique {n k : ℕ} {E' : Type} [DecidableEq E'] {ends : E' → Finset (Fin n)}
    {Old New W : Finset E'} {Y P : Finset (Fin n)} (hk : 1 ≤ k) (hYP : Disjoint Y P)
    (hsub : W ⊆ Old ∪ New) (hnew : ∀ c ∈ New, (ends c ∩ P).Nonempty)
    (hone : (W.filter (· ∈ Old)).card ≤ 1)
    (hcl : ∀ S ⊆ W.biUnion ends, S.card = k → ∃ c ∈ W, ends c = S) :
    (W.biUnion ends ∩ Y).card ≤ k := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq (s := W.biUnion ends ∩ Y) (n := k + 1) hcon
  obtain ⟨v₁, hv₁⟩ : T.Nonempty := card_pos.1 (by omega)
  obtain ⟨v₂, hv₂, hne⟩ : ∃ v₂ ∈ T, v₂ ≠ v₁ := by
    by_contra h
    push_neg at h
    have : T ⊆ {v₁} := fun x hx => mem_singleton.2 (h x hx)
    have := card_le_card this
    rw [card_singleton] at this
    omega
  have hold : ∀ v ∈ T, ∃ c ∈ W, c ∈ Old ∧ ends c = T.erase v := by
    intro v hv
    have hsubT : T.erase v ⊆ W.biUnion ends := fun x hx =>
      (mem_inter.1 (hT (mem_of_mem_erase hx))).1
    obtain ⟨c, hcW, hc⟩ := hcl _ hsubT (by rw [card_erase_of_mem hv, hTc]; omega)
    refine ⟨c, hcW, ?_, hc⟩
    rcases mem_union.1 (hsub hcW) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨z, hz⟩ := hnew c h1
      rw [hc] at hz
      obtain ⟨hz1, hz2⟩ := mem_inter.1 hz
      exact disjoint_left.1 hYP (mem_inter.1 (hT (mem_of_mem_erase hz1))).2 hz2
  obtain ⟨c₁, hc₁W, hc₁O, hc₁⟩ := hold v₁ hv₁
  obtain ⟨c₂, hc₂W, hc₂O, hc₂⟩ := hold v₂ hv₂
  have h12 : c₁ = c₂ := card_le_one.1 hone c₁ (mem_filter.2 ⟨hc₁W, hc₁O⟩) c₂
    (mem_filter.2 ⟨hc₂W, hc₂O⟩)
  have : T.erase v₁ = T.erase v₂ := by rw [← hc₁, ← hc₂, h12]
  have hv : v₂ ∈ T.erase v₁ := mem_erase.2 ⟨hne, hv₂⟩
  rw [this] at hv
  exact (notMem_erase v₂ T) hv

/-- **Theorem 3.7 in uniformity `k`** (flat, clique pieces, small trace), from the sparse link
levels of uniformity `k`. -/
theorem flatOmniK_of_levels {q k : ℕ} (hk : 2 ≤ k) (hkq : k < q)
    (hL : ∀ j, 1 ≤ j → j < k - 1 → PlacedLinkLevelS q k j (sharpCost k)) :
    FlatOmniK q k (sharpCost k) := by
  classical
  intro K
  obtain ⟨C₁, Ch₁, hloc⟩ := localRefinerK hk hkq hL K
  obtain ⟨Cf, C₂, hfake⟩ := fakeStageK hk hkq C₁ K
  obtain ⟨Ca, habs⟩ := absStageK hk hkq C₂ K
  set M := Ch₁ + Cf * C₁ + Ca + Ca * C₂ * C₁ with hM
  obtain ⟨m₀, hm₀⟩ := exists_mul_sharpCost_le hk (2 * M)
  set C₃ := 2 * (C₂ + 1) + q.choose k with hC₃
  set Cd := C₂ * C₁ + Ca + Ca * C₂ * C₁ with hCd
  refine ⟨C₃ + Cd + 1, 2 * M + m₀ + 1, ?_⟩
  intro n E _ ends Y P L d hYP hYK hCh hChd hLr hLY hdeg hmult
  set s := sharpCost k P.card with hs
  have hP0 : 0 < P.card := by omega
  have hs1 : 1 ≤ s := one_le_sharpCost k (by omega)
  set D := d + s with hD
  have hs2 : 2 * (M * s) ≤ P.card := by
    have := hm₀ P.card (by omega); rw [← mul_assoc]; exact this
  have hd2 : 2 * (M * d) ≤ P.card := by
    rw [← mul_assoc]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hChd
  have hsmall : M * D ≤ P.card := by rw [hD, mul_add]; omega
  -- 1. the local refiner
  have hdegD : ∀ S : Finset (Fin n), S.card = k - 1 → mdeg ends L S ≤ D :=
    fun S hS => (hdeg S hS).trans (Nat.le_add_right _ _)
  obtain ⟨E₁, _, g, ends₁, R, 𝒲, hg, hge, hgR, href, hRYP, hone, hdegR, hpdR⟩ :=
    hloc n ends Y P L D hYK (le_trans (Nat.mul_le_mul_right _ (by omega)) hsmall) (by omega)
      hLr hLY (by omega) hdegD
  set B := C₁ * D with hB
  -- 2. fake edges
  have hXY : ∀ c ∈ L.image g, ends₁ c ⊆ Y := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
    rw [hge]; exact hLY x hx
  have hBf : Cf * B ≤ P.card := by
    calc Cf * B = (Cf * C₁) * D := by rw [hB]; ring
      _ ≤ M * D := Nat.mul_le_mul_right _ (by omega)
      _ ≤ P.card := hsmall
  obtain ⟨F, 𝒱, h𝒱, hF, hdegF, hpd𝒱, hinj𝒱, hone𝒱⟩ := hfake n ends₁ (L.image g) R 𝒲 Y P B href
    hXY hRYP hYP hone hdegR hpdR hYK hBf hP0
  -- 3. absorbers
  set B' := d + C₂ * B with hB'
  have hhost : ∀ S : Finset (Fin n), S.card = k - 1 →
      deg ((L.image g).image ends₁ ∪ F) S ≤ B' := by
    intro S hS
    have h1 : deg ((L.image g).image ends₁) S ≤ d := by
      rw [image_image]
      have : ends₁ ∘ g = ends := funext hge
      rw [this]
      unfold deg
      rw [filter_image]
      exact card_image_le.trans (hdeg S hS)
    unfold deg at h1 ⊢
    rw [filter_union]
    exact (card_union_le _ _).trans (Nat.add_le_add h1 (hdegF S hS))
  have hspan : ∀ W ∈ 𝒱, W.biUnion (Sum.elim ends₁ id) ⊆ Y ∪ P := by
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
    calc Ca * B' = Ca * d + (Ca * C₂ * C₁) * D := by rw [hB', hB]; ring
      _ ≤ Ca * D + (Ca * C₂ * C₁) * D :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
      _ ≤ M * D := by rw [← add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      _ ≤ P.card := hsmall
  obtain ⟨AW, Qon, Qoff, hA, hAedge, hdegA⟩ := habs n ends₁ (L.image g) F 𝒱 (Y ∪ P) P B' h𝒱
    hinj𝒱 hspan hU hhost (fun S hS => (hpd𝒱 S hS).trans (Nat.le_add_left _ _)) hCaB hP0
  -- 4. clique pieces
  obtain ⟨hcl, hclique⟩ := cliquePieces_refinerK h𝒱 hA
  have hnewflat : ∀ c ∈ (F ∪ 𝒱.biUnion AW).image (Sum.inr : Finset (Fin n) → E₁ ⊕ Finset (Fin n)),
      Sum.elim ends₁ id c ⊆ Y ∪ P ∧ (Sum.elim ends₁ id c ∩ P).Nonempty := by
    intro c hc
    obtain ⟨f, hf, rfl⟩ := mem_image.1 hc
    change f ⊆ Y ∪ P ∧ (f ∩ P).Nonempty
    rcases mem_union.1 hf with hf | hf
    · exact hF f hf
    · obtain ⟨W, hW, hfW⟩ := mem_biUnion.1 hf
      obtain ⟨h1, h2⟩ := hAedge W hW f hfW
      refine ⟨?_, h2⟩
      rw [union_assoc, union_self] at h1
      exact h1
  have hold1 := cliqueFam_old_le_one (ends := ends₁) (AW := AW) (Qon := Qon) (Qoff := Qoff) hone𝒱
  refine ⟨E₁ ⊕ Finset (Fin n), inferInstance, Sum.inl ∘ g, Sum.elim ends₁ id,
    (F ∪ 𝒱.biUnion AW).image Sum.inr, cliqueFam ends₁ 𝒱 AW Qon Qoff,
    Sum.inl_injective.comp hg, fun c => by simp [hge], fun c hc x => ?_, ?_, hnewflat,
    fun S hS => ?_, fun e => ?_, hclique, fun W hW => ?_⟩
  · obtain ⟨f, -, rfl⟩ := mem_image.1 hc
    exact Sum.inl_ne_inr
  · rw [← image_image]
    exact hcl.mono (by omega)
  · rw [mdeg_image_inr]
    have hdu : deg (F ∪ 𝒱.biUnion AW) S ≤ C₂ * B + Ca * B' := by
      unfold deg
      rw [filter_union]
      exact (card_union_le _ _).trans (Nat.add_le_add (hdegF S hS) (hdegA S hS))
    refine hdu.trans ?_
    have hdX : Ca * d ≤ Ca * D := Nat.mul_le_mul_left _ (by omega)
    calc C₂ * B + Ca * B' = C₂ * C₁ * D + Ca * d + Ca * C₂ * C₁ * D := by rw [hB', hB]; ring
      _ ≤ C₂ * C₁ * D + Ca * D + Ca * C₂ * C₁ * D := by omega
      _ = Cd * D := by rw [hCd]; ring
      _ ≤ (C₃ + Cd + 1) * (d + s) := Nat.mul_le_mul_right _ (by omega)
  · exact (mult_image_inr_le ends₁ _ e).trans (by omega)
  · exact trace_le_of_clique (by omega) hYP (hcl.subset W hW) (fun c hc => (hnewflat c hc).2)
      (hold1 W hW) (hclique W hW)

end RefinedAbsorption.General
