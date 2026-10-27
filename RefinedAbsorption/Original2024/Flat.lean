module
public import RefinedAbsorption.Original2024.FlatChain
public import RefinedAbsorption.Original2024.Final

/-!
# Theorem 3.8 with the flatness output

M. Delcourt and L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture*,
arXiv:2402.17855v1, Theorem 3.8.

The article's Theorem 3.8 also asserts that the multi-refiner `R` is `(r-1)`-flat to a set `Y`
of at least `n/3` vertices.  Here `R` is *`i`-flat to `Y`* (`IsFlatTo i Y ends R`) if every copy
of `R` has at most `i` vertices outside `Y`; for `r`-sets, `(r-1)`-flat to `Y` means that every
new copy meets `Y`.  The statement below is the strong form: the set `Y` is **arbitrary**
(chosen by the user, not by the construction), subject only to `|Y| ≥ n/3`.  The corollary
`MultiRefinerFlatConclusion.exists_inside` gives the other reading as well (a set `Y'` with
`|Y'| ≥ n/3` such that every new copy has at most `r - 1` vertices *inside* `Y'`).

## Construction (`r ≥ 2`)

Split `Y` into halves `Z` and `P = Y \ Z`.

1. The refine-down stage `multiStageS_M` with reserve `Z`: every new copy meets `Z`, and the
   residue lies inside `Z`, has bounded multiplicity and `(r-1)`-degrees `O(D + sharpCost r |Z|)`.
2. Theorem 3.7 in uniformity `r` (`General.flatOmniK_of_levels`) applied to the residue inside `Z`
   with new vertices in `P`: a complete multi-refiner whose new copies lie in `Z ∪ P = Y` and meet
   `P`; its pieces are cliques, so their degrees are controlled by the copy degrees
   (`pdeg_le_of_clique`).
3. The two stages are composed (`IsResidualMultiRefiner.compose`).

## Main results

* `IsFlatTo`, `MultiRefinerFlatConclusion`, `Theorem_3_8_flat_for`.
* `multiRefinerFlat_two_le`, **`theorem_3_8_flat_two_le`**: Theorem 3.8 with flatness, `q > r ≥ 2`.
-/

@[expose] public section

namespace RefinedAbsorption.Original2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement RefinedAbsorption.Dense RefinedAbsorption.Sharp
  RefinedAbsorption.General

/-- `R` is **`i`-flat to `Y`**: every copy of `R` has at most `i` vertices outside `Y`. -/
def IsFlatTo {α E : Type*} [DecidableEq α] (i : ℕ) (Y : Finset α) (ends : E → Finset α)
    (R : Finset E) : Prop :=
  ∀ c ∈ R, (ends c \ Y).card ≤ i

/-- **The conclusion of Theorem 3.8 with the flatness output** for fixed `q, r`: as
`MultiRefinerConclusion`, and moreover, for **every** set `Y` of at least `n/3` vertices, the
multi-refiner can be chosen `(r-1)`-flat to `Y`. -/
def MultiRefinerFlatConclusion (q r : ℕ) : Prop :=
  ∃ C : ℕ, 1 ≤ C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Finset (Fin n)), ∀ D : ℝ,
    IsRGraph r X → MaxDegLE r X D → D ≤ n / C → ∀ Y : Finset (Fin n), n ≤ 3 * Y.card →
    ∃ (E : Type) (_ : DecidableEq E) (ends : E → Finset (Fin n)) (K Xl R : Finset E)
      (𝒲 : Finset (Finset E)) (B : ℕ),
      Xl.image ends = X ∧ (B : ℝ) ≤ C * max D (budget n r) ∧
      IsMultiRefinerOn q r C (univ : Finset (Fin n)) ends Xl R 𝒲 ∧
      Placement.IsStrongMultiRefiner q r C ends K Xl R 𝒲 B ∧
      IsFlatTo (r - 1) Y ends R

/-- **Theorem 3.8 (multi-refiner theorem) with the flatness output**, in the inductive form of the
article. -/
def Theorem_3_8_flat_for (q r : ℕ) : Prop :=
  (∀ q' r' : ℕ, 1 ≤ r' → r' < r → r' < q' → Theorem_1_11_for q' r') →
    MultiRefinerFlatConclusion q r

/-- The flat conclusion contains the conclusion without flatness (take `Y = univ`). -/
theorem MultiRefinerFlatConclusion.toConclusion {q r : ℕ} (h : MultiRefinerFlatConclusion q r) :
    MultiRefinerConclusion q r := by
  obtain ⟨C, hC, n₀, h⟩ := h
  refine ⟨C, hC, n₀, fun n hn X D hX hXD hDn => ?_⟩
  obtain ⟨E, hE, ends, K, Xl, R, 𝒲, B, h1, h2, h3, h4, -⟩ :=
    h n hn X D hX hXD hDn univ (by rw [card_univ, Fintype.card_fin]; omega)
  exact ⟨E, hE, ends, K, Xl, R, 𝒲, B, h1, h2, h3, h4⟩

/-- An `r`-set meeting `Y` has at most `r - 1` vertices outside `Y`. -/
theorem card_sdiff_le_of_meets {α : Type*} [DecidableEq α] {s Y : Finset α} {r : ℕ}
    (hs : s.card = r) (h : (s ∩ Y).Nonempty) : (s \ Y).card ≤ r - 1 := by
  have h1 := card_sdiff_add_card_inter s Y
  have h2 := h.card_pos
  omega

/-- **Degrees of clique pieces.**  If every piece is a clique (every `r`-subset of its span
carries one of its copies), the number of pieces whose span contains a nonempty `(r-1)`-set `S` is
at most `C` times the number of copies containing `S`. -/
theorem pdeg_le_of_clique {V E : Type*} [DecidableEq V] [DecidableEq E] {q r C : ℕ}
    {ends : E → Finset V} {X R Y : Finset E} {𝒲 : Finset (Finset E)}
    (h : IsResidualMultiRefiner q r C ends X R Y 𝒲)
    (hcl : ∀ W ∈ 𝒲, ∀ T ⊆ W.biUnion ends, T.card = r → ∃ c ∈ W, ends c = T)
    {S : Finset V} (hS : S.card + 1 = r) (hS0 : S.Nonempty) :
    pdeg ends 𝒲 S ≤ C * mdeg ends (X ∪ R) S := by
  unfold pdeg mdeg
  refine (card_le_card (t := ((X ∪ R).filter fun c => S ⊆ ends c).biUnion
    (fun c => 𝒲.filter fun W => c ∈ W)) ?_).trans ?_
  · intro W hW
    obtain ⟨hW𝒲, hSW⟩ := mem_filter.1 hW
    obtain ⟨x, hx⟩ := hS0
    obtain ⟨c₀, hc₀W, -⟩ := mem_biUnion.1 (hSW hx)
    have hc₀r : (ends c₀).card = r := h.rgraph c₀ (h.subset W hW𝒲 hc₀W)
    have hlt : S.card < (W.biUnion ends).card := by
      have := card_le_card (subset_biUnion_of_mem ends hc₀W)
      omega
    obtain ⟨v, hv, hvS⟩ := exists_mem_notMem_of_card_lt_card hlt
    obtain ⟨c, hcW, hc⟩ := hcl W hW𝒲 (insert v S) (insert_subset hv hSW)
      (by rw [card_insert_of_notMem hvS]; omega)
    exact mem_biUnion.2 ⟨c, mem_filter.2 ⟨h.subset W hW𝒲 hcW, hc ▸ subset_insert v S⟩,
      mem_filter.2 ⟨hW𝒲, hcW⟩⟩
  · refine card_biUnion_le.trans ?_
    calc ∑ c ∈ (X ∪ R).filter (fun c => S ⊆ ends c), (𝒲.filter fun W => c ∈ W).card
        ≤ ∑ c ∈ (X ∪ R).filter (fun c => S ⊆ ends c), C :=
          sum_le_sum fun c hc => h.mult_le c (mem_filter.1 hc).1
      _ = C * ((X ∪ R).filter fun c => S ⊆ ends c).card := by
          rw [sum_const, smul_eq_mul, mul_comm]

set_option maxHeartbeats 4000000 in
/-- **The flat multi-refiner conclusion for `q > r ≥ 2`.** -/
theorem multiRefinerFlat_two_le {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    MultiRefinerFlatConclusion q r := by
  have hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelS q r i (sharpCost r) := fun i hi hir => by
    rcases Nat.lt_or_ge i (r - 1) with h | h
    · exact placedLinkLevelS_all r q i hr hrq hi h
    · obtain rfl : i = r - 1 := by omega
      exact (placedLinkLevel_last q r hr hrq).toS _
  obtain ⟨Cs, C₁, M, -, -, hstage⟩ := multiStageS_M hr hrq hL
  have hF : FlatOmniK q r (sharpCost r) :=
    flatOmniK_of_levels hr hrq fun j hj hjr => placedLinkLevelS_all r q j hr hrq hj hjr
  obtain ⟨C₂, Ch, homni⟩ := hF (M + 1)
  set A := Cs + Ch * C₁ + Ch with hA
  obtain ⟨m₀, hm₀⟩ := FlatOmni.exists_mul_sharpPot_le hr (2 * A)
  set Cb := C₁ + C₂ * (C₁ + 1) + C₂ * (C₁ + C₂ * (C₁ + 1)) with hCb
  set Cf := 24 * A + 32 * (Cb + C₁ + C₂ + 1) with hCf
  refine ⟨Cf, by omega, 24 * A + 6 * m₀ + 12, ?_⟩
  intro n hn X D hX hXD hDn Y hY
  have hCf0 : (0 : ℝ) < Cf := by positivity
  -- the integer degree bound
  set Df := ⌊D⌋₊ with hDf
  have hCD : Cf * Df ≤ n := by
    rcases lt_or_ge D 0 with hD0 | hD0
    · rw [hDf, Nat.floor_of_nonpos hD0.le, mul_zero]; exact Nat.zero_le _
    · have h1 : (Df : ℝ) ≤ D := Nat.floor_le hD0
      have h2 : (Cf : ℝ) * Df ≤ n := by
        calc (Cf : ℝ) * Df ≤ Cf * D := mul_le_mul_of_nonneg_left h1 hCf0.le
          _ ≤ Cf * (n / Cf) := mul_le_mul_of_nonneg_left hDn hCf0.le
          _ = n := by field_simp
      exact_mod_cast h2
  set Dn := Df + 1 with hDn'
  have hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → deg X S ≤ Dn := by
    intro S hS
    have h1 := hXD S (by omega)
    have : deg X S ≤ Df := Nat.le_floor h1
    omega
  -- the two halves of `Y`
  obtain ⟨Z, hZY, hZc⟩ := exists_subset_card_eq (s := Y) (Nat.div_le_self Y.card 2)
  set P := Y \ Z with hP
  have hPc : P.card = Y.card - Z.card := card_sdiff_of_subset hZY
  have hZ6 : n ≤ 6 * Z.card + 3 := by omega
  have hU8 : n ≤ 8 * Z.card := by omega
  have hZP : Z.card ≤ P.card := by omega
  have hZm : m₀ ≤ Z.card := by omega
  have hZ1 : 1 ≤ Z.card := by omega
  have hZn : Z.card ≤ n := (card_le_card (subset_univ Z)).trans (by simp)
  have hPn : P.card ≤ n := (card_le_card (subset_univ P)).trans (by simp)
  set sZ := sharpCost r Z.card with hsZ
  have hsZA : 2 * A * sZ ≤ Z.card := by
    have h1 := hm₀ Z.card hZm
    have h2 : sZ ≤ sharpPot r Z.card := sharpCost_le_sharpPot r hZ1
    have h3 : 2 * A * sZ ≤ 2 * A * sharpPot r Z.card := Nat.mul_le_mul_left _ h2
    omega
  set D' := Dn + sZ with hD'
  have hAD : A * D' ≤ Z.card := by
    have h1 : 24 * (A * Df) ≤ n := by
      rw [← mul_assoc]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hCD
    have h2 : A * Dn = A * Df + A := by rw [hDn']; ring
    have : A * D' = A * Dn + A * sZ := by rw [hD']; ring
    have h4 : 2 * (A * sZ) ≤ Z.card := by rw [← mul_assoc]; exact hsZA
    omega
  have hD'1 : 1 ≤ D' := by omega
  have hCsD : Cs * D' ≤ Z.card :=
    le_trans (Nat.mul_le_mul_right _ (by omega)) hAD
  have hChD : Ch * (C₁ * D') ≤ P.card := by
    have : Ch * (C₁ * D') ≤ A * D' := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by rw [hA, mul_comm Ch C₁]; omega)
    omega
  have hCh : Ch ≤ P.card := by
    have : Ch ≤ A * D' := le_trans (by omega) (Nat.mul_le_mul_left A hD'1)
    omega
  -- stage 1: refine down into `Z`
  have hXr : MIsRGraph r (id : Finset (Fin n) → Finset (Fin n)) X := hX
  obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hY₁Z, hY₁m, -, hdeg₁,
    hone₁, hpd₁, hmeet₁⟩ := hstage n id Z univ X D' hXr (fun _ _ => subset_univ _)
      (by rw [card_univ, Fintype.card_fin]; exact hU8) hCsD hD'1 (by omega)
      (fun S hS => le_trans (hdeg S hS) (by omega))
  have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
  have hdegY₁ : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ C₁ * D' :=
    fun S hS => (mdeg_mono _ hY₁R S).trans (hdeg₁ S hS)
  -- stage 2: Theorem 3.7 inside `Z ∪ P`
  obtain ⟨E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, hends₂, hR₂f, h₂, hR₂loc, hdeg₂, -, hcl₂, -⟩ :=
    homni n ends₁ Z P Y₁ (C₁ * D') disjoint_sdiff
      (le_trans hZP (Nat.le_mul_of_pos_left _ (by omega))) hCh hChD hY₁r hY₁Z hdegY₁
      (fun e => (hY₁m e).trans (Nat.le_succ M))
  have hcomp := IsResidualMultiRefiner.compose g₂ hg₂ hends₂ h₁
    (hY₁R.trans subset_union_right) h₂ hR₂f
  have hone := oneX_compose g₂ hg₂ h₁.disjoint hY₁R hone₁ h₂ hR₂f
  rw [image_image] at hcomp hone
  -- the budget
  set Bd := Dn + sharpCost r n with hBd
  have hsZn : sZ ≤ sharpCost r n := sharpCost_mono (by omega) hZn
  have hsPn : sharpCost r P.card ≤ sharpCost r n := sharpCost_mono (by omega) hPn
  have hD'B : D' ≤ Bd := by omega
  have hendsX : ∀ e, ends₂ ((g₂ ∘ g₁) e) = e := fun e => by simp [hends₂, hends₁]
  have hdegR : ∀ S : Finset (Fin n), S.card = r - 1 →
      mdeg ends₂ (R₁.image g₂ ∪ R₂) S ≤ (C₁ + C₂ * (C₁ + 1)) * Bd := by
    intro S hS
    refine (Dense.mdeg_union_le _ _ _ S).trans ?_
    rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
    have h1 := hdeg₁ S hS
    have h2 := hdeg₂ S hS
    have e1 : C₁ * D' ≤ C₁ * Bd := Nat.mul_le_mul_left _ hD'B
    have e2 : C₂ * (C₁ * D' + sharpCost r P.card) ≤ C₂ * (C₁ * Bd + Bd) :=
      Nat.mul_le_mul_left _ (by omega)
    have e3 : (C₁ + C₂ * (C₁ + 1)) * Bd = C₁ * Bd + C₂ * (C₁ * Bd + Bd) := by ring
    omega
  have hCbB : (C₁ + C₂ * (C₁ + 1)) * Bd ≤ Cf * Bd := Nat.mul_le_mul_right _ (by omega)
  refine ⟨E₂, inferInstance, ends₂, X.image (g₂ ∘ g₁), X.image (g₂ ∘ g₁), R₁.image g₂ ∪ R₂,
    𝒲₁.image (image g₂) ∪ 𝒲₂, Bd, ?_, ?_, ⟨fun _ _ => subset_univ _, hcomp.mono (by omega)⟩,
    ?_, ?_⟩
  · rw [image_image]
    have : ends₂ ∘ (g₂ ∘ g₁) = id := funext hendsX
    rw [this, image_id]
  · set Lg := budget n r with hLg
    have hn3 : 3 ≤ n := by omega
    have hL1 : 1 ≤ Lg := HyperPlan.one_le_rpow_log (by omega) hn3
    set Mx := max D Lg with hMx
    have hM1 : 1 ≤ Mx := hL1.trans (le_max_right _ _)
    have hDnM : (Dn : ℝ) ≤ 2 * Mx := by
      have hfl : (Df : ℝ) ≤ Mx := by
        rcases le_or_gt 0 D with hD0 | hD0
        · exact (Nat.floor_le hD0).trans (le_max_left _ _)
        · rw [hDf, Nat.floor_of_nonpos hD0.le]; simp only [Nat.cast_zero]; linarith
      rw [hDn']; push_cast; linarith
    have hsP : (sharpCost r n : ℝ) ≤ 30 * Mx := by
      have h1 : (sharpCost r n : ℝ) ≤ sharpPot r n := by
        exact_mod_cast sharpCost_le_sharpPot r (by omega)
      have h2 := sharpPot_le hr hn3
      have h3 : (n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n = Lg := rfl
      rw [h3] at h2
      linarith [le_max_right D Lg]
    have hC32 : (32 : ℝ) ≤ Cf := by
      have : 32 ≤ Cf := by omega
      exact_mod_cast this
    calc (Bd : ℝ) = Dn + sharpCost r n := by rw [hBd]; push_cast; ring
      _ ≤ 2 * Mx + 30 * Mx := add_le_add hDnM hsP
      _ = 32 * Mx := by ring
      _ ≤ Cf * Mx := mul_le_mul_of_nonneg_right hC32 (by linarith)
  · exact
    { refiner := hcomp.mono (by omega)
      keep := subset_rfl
      inj := by
        intro x hx y hy hxy
        obtain ⟨u, -, rfl⟩ := mem_image.1 (mem_coe.1 hx)
        obtain ⟨v, -, rfl⟩ := mem_image.1 (mem_coe.1 hy)
        rw [hendsX, hendsX] at hxy
        rw [hxy]
      oneX := hone
      degX := fun S hS => by
        rw [mdeg_image_eq (A := X) (fun c _ => hendsX c) (hg₂.comp hg₁).injOn subset_rfl]
        exact (hdeg S hS).trans (by omega)
      degR := fun S hS => (hdegR S hS).trans hCbB
      pieceDeg := fun S hS => by
        have hS0 : S.Nonempty := by rw [← card_pos, hS]; omega
        show pdeg ends₂ _ S ≤ _
        refine (pdeg_union_le _ _ _ S).trans ?_
        have h1 := (pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)
        have h2 := pdeg_le_of_clique h₂ hcl₂ (by omega) hS0
        have h3 : mdeg ends₂ (Y₁.image g₂ ∪ R₂) S ≤ C₁ * Bd + C₂ * (C₁ * Bd + Bd) := by
          refine (Dense.mdeg_union_le _ _ _ S).trans ?_
          rw [mdeg_image_eq (A := Y₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
          have := hdegY₁ S hS
          have := hdeg₂ S hS
          have e1 : C₁ * D' ≤ C₁ * Bd := Nat.mul_le_mul_left _ hD'B
          have e2 : C₂ * (C₁ * D' + sharpCost r P.card) ≤ C₂ * (C₁ * Bd + Bd) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        have h4 : C₂ * mdeg ends₂ (Y₁.image g₂ ∪ R₂) S ≤
            C₂ * (C₁ * Bd + C₂ * (C₁ * Bd + Bd)) := Nat.mul_le_mul_left _ h3
        have e1 : C₁ * D' ≤ C₁ * Bd := Nat.mul_le_mul_left _ hD'B
        have e3 : Cb * Bd = C₁ * Bd + C₂ * (C₁ + 1) * Bd +
            C₂ * (C₁ * Bd + C₂ * (C₁ * Bd + Bd)) := by rw [hCb]; ring
        have e4 : Cb * Bd ≤ Cf * Bd := Nat.mul_le_mul_right _ (by omega)
        omega }
  · intro c hc
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      rw [hends₂]
      refine card_sdiff_le_of_meets (h₁.rgraph c₁ (mem_union_right _ hc₁)) ?_
      obtain ⟨v, hv⟩ := hmeet₁ c₁ hc₁
      exact ⟨v, mem_inter.2 ⟨(mem_inter.1 hv).1, hZY (mem_inter.1 hv).2⟩⟩
    · refine card_sdiff_le_of_meets (h₂.rgraph c (mem_union_right _ h)) ?_
      obtain ⟨v, hv⟩ := (hR₂loc c h).2
      exact ⟨v, mem_inter.2 ⟨(mem_inter.1 hv).1, sdiff_subset (mem_inter.1 hv).2⟩⟩

/-- **Theorem 3.8 with the flatness output**, `q > r ≥ 2`. -/
theorem theorem_3_8_flat_two_le {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    Theorem_3_8_flat_for q r :=
  fun _ => multiRefinerFlat_two_le hr hrq

end RefinedAbsorption.Original2024
