module
public import RequestProject.Faithful2024.FlatSparsify
public import RequestProject.Faithful2024.FlatLabelled
public import RequestProject.HyperPlan.Native
public import RequestProject.Faithful2024.Defs

/-!
# Theorem 3.8 of arXiv:2402.17855v1, faithful form, `q > r ≥ 2`

**`theorem_3_8_conclusion_two_le`**: `Theorem_3_8_conclusion q r` for `q > r ≥ 2`: the input is an
arbitrary `r`-uniform multi-hypergraph `X` (labelled copies) of multiplicity at most `M(q,r)` on
`v(X) = n ≥ C` vertices, with **no** bound `Δ(X) ≤ n/C`, and `Y` is prescribed with
`|Y| ≥ n/3`.

Construction (following the article: Edge Sparsification, then refine down):
1. Edge Sparsification with flatness (`edgeSparsificationFlat_holds`) on the whole vertex set with
   the special sets inside `Y`: every new copy meets `Y`; the residue has
   `Δ ≤ Cst ⌈n^{1-1/r}⌉ ≪ n`.
2. The flat multi-refiner for the (sparse) residue (`flatLabelled_two_le`): every new copy meets
   `Y`.
3. Composition (`IsResidualMultiRefiner.compose`), and the conversion to the faithful contract
   (`isMultiRefinerF_of_residual`, `isCRefinedMultiFamily_of_residual`).
-/

@[expose] public section

namespace RefinedAbsorption.Faithful2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Window RefinedAbsorption.Sharp
  RefinedAbsorption.FlatDown RefinedAbsorption.Dense RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement RefinedAbsorption.General

section Convert

variable {α E : Type*} [DecidableEq α] [DecidableEq E]

/-- A multi-refiner in the sense of the project (`IsMultiRefiner`, i.e. a residual multi-refiner
with empty residue) whose pieces contain at most one copy of `X` and whose copies lie in `U` is a
multi-refiner in the sense of Definitions 1.8 and 3.2. -/
theorem isMultiRefinerF_of_residual {q r C : ℕ} {U : Finset α} {ends : E → Finset α}
    {X R : Finset E} {𝒲 : Finset (Finset E)} (h : IsMultiRefiner q r C ends X R 𝒲)
    (hU : ∀ c ∈ X ∪ R, ends c ⊆ U) (hone : ∀ W ∈ 𝒲, (W.filter (· ∈ X)).card ≤ 1) :
    IsMultiRefinerF q r U ends X R 𝒲 := by
  refine ⟨hU, h.rgraph, h.disjoint, h.subset, h.divisible, fun W hW => ?_, fun L hL hdiv => ?_⟩
  · rw [← filter_mem_eq_inter]; exact hone W hW
  · obtain ⟨𝒰, h𝒰, Res, hRes, -, hpw, -, hcov⟩ := h.decomp L hL hdiv
    have hRes0 : Res = ∅ := subset_empty.1 hRes
    subst hRes0
    refine ⟨𝒰, h𝒰, hpw, ?_⟩
    rw [union_empty] at hcov
    rw [hcov, union_comm]

/-- The refinement family of an `IsMultiRefiner` with constant `C` is `(r+1) C`-refined in the
sense of Definition 1.9 (`v(H) ≤ r · e(H)`). -/
theorem isCRefinedMultiFamily_of_residual {q r C : ℕ} {ends : E → Finset α}
    {X R Y : Finset E} {𝒲 : Finset (Finset E)} (h : IsResidualMultiRefiner q r C ends X R Y 𝒲) :
    IsCRefinedMultiFamily ((r + 1) * C) ends (X ∪ R) 𝒲 := by
  refine ⟨fun c hc => (h.mult_le c hc).trans ?_, fun W hW => ?_, fun W hW => (h.card_le W hW).trans ?_⟩
  · exact Nat.le_mul_of_pos_left _ (by omega)
  · refine card_biUnion_le.trans ?_
    calc ∑ c ∈ W, (ends c).card = ∑ _c ∈ W, r :=
          sum_congr rfl fun c hc => h.rgraph c (h.subset W hW hc)
      _ = r * W.card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ r * C := Nat.mul_le_mul_left _ (h.card_le W hW)
      _ ≤ (r + 1) * C := Nat.mul_le_mul_right _ (by omega)
  · exact Nat.le_mul_of_pos_left _ (by omega)

theorem IsCRefinedMultiFamily.mono {C C' : ℕ} {ends : E → Finset α} {G : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsCRefinedMultiFamily C ends G 𝒲) (hC : C ≤ C') :
    IsCRefinedMultiFamily C' ends G 𝒲 :=
  ⟨fun c hc => (h.mult_le c hc).trans hC, fun W hW => (h.verts_le W hW).trans hC,
    fun W hW => (h.card_le W hW).trans hC⟩

theorem mrefDeg_le_of [Fintype α] {r B : ℕ} {ends : E → Finset α} {𝒲 : Finset (Finset E)}
    (h : ∀ S : Finset α, S.card = r - 1 → pdeg ends 𝒲 S ≤ B) (hr : 1 ≤ r) :
    mrefDeg r ends 𝒲 ≤ B :=
  Finset.sup_le fun S hS => h S (by have := (mem_filter.1 hS).2; omega)

theorem mdeg_le_mmaxDeg [Fintype α] {r : ℕ} (hr : 1 ≤ r) (ends : E → Finset α) (X : Finset E)
    (S : Finset α) (hS : S.card = r - 1) : mdeg ends X S ≤ mmaxDeg r ends X :=
  le_sup (f := mdeg ends X) (mem_filter.2 ⟨mem_univ _, by omega⟩)

end Convert

theorem exists_mul_winCost_le {r : ℕ} (hr : 2 ≤ r) (c : ℕ) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → c * winCost r m ≤ m := by
  obtain ⟨m₀, h⟩ := exists_mul_sharpCost_le hr c
  exact ⟨m₀, fun m hm => (Nat.mul_le_mul_left _ (winCost_le_sharpCost r m)).trans (h m hm)⟩

/-- `sharpCost r n ≤ 30 · n^{1-1/r} log n` for `n ≥ 3`. -/
theorem sharpCost_le_budget {r n : ℕ} (hr : 2 ≤ r) (hn : 3 ≤ n) :
    (sharpCost r n : ℝ) ≤ 30 * budget n r := by
  have h1 : (sharpCost r n : ℝ) ≤ sharpPot r n := by
    exact_mod_cast sharpCost_le_sharpPot r (by omega)
  exact h1.trans (sharpPot_le hr hn)

set_option maxHeartbeats 1000000 in
/-- **Theorem 3.8 of arXiv:2402.17855v1 (Multi-Refiner Theorem), faithful conclusion,
`q > r ≥ 2`.** -/
theorem theorem_3_8_conclusion_two_le {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    Theorem_3_8_conclusion q r := by
  obtain ⟨Cst, m₀, hS⟩ := edgeSparsificationFlat_holds hr hrq (multBound q r)
  obtain ⟨Cf, m₁, hCf, hF⟩ := flatLabelled_two_le hr hrq
  obtain ⟨n₂, hn₂⟩ := exists_mul_winCost_le hr (Cf * Cst)
  set K := Cst + Cf * Cst + Cf with hK
  set C := (r + 1) * (Cst + Cf) + Cst + 30 * K + Cf + m₀ + m₁ + n₂ + 3 with hC
  refine ⟨C, by omega, ?_⟩
  intro n E _ ends X hXr hmult hCn Y hY
  have hY3 : n ≤ 3 * Y.card := by
    have : (n : ℝ) ≤ 3 * Y.card := by linarith
    exact_mod_cast this
  have hn3 : 3 ≤ n := by omega
  set D₀ := mmaxDeg r ends X with hD₀
  have hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D₀ :=
    fun S hS => mdeg_le_mmaxDeg (by omega) ends X S hS
  have hcardU : (univ : Finset (Fin n)).card = n := by rw [card_univ, Fintype.card_fin]
  -- 1. edge sparsification with flatness
  obtain ⟨E₁, _, g₁, ends₁, R₁, Res₁, 𝒲₁, hg₁, hends₁, hR₁f, h₁, hResR, -, hdegRes, -, hone₁,
    hpd₁, hmeet₁⟩ := hS n ends univ Y X D₀ hXr (fun _ _ => subset_univ _)
      (by rw [hcardU]; omega) (subset_univ _) (by rw [hcardU]; exact hY3) hmult hdeg
  rw [hcardU] at hdegRes hpd₁
  have hResr : MIsRGraph r ends₁ Res₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hResR hc))
  -- 2. the flat refiner of the residue
  obtain ⟨E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, hends₂, hR₂f, h₂, hone₂, -, hpd₂, hmeet₂⟩ :=
    hF n ends₁ Res₁ (Cst * winCost r n) (by omega) hResr hdegRes
      (by rw [← mul_assoc]; exact hn₂ n (by omega)) Y hY3
  -- 3. composition
  have hcomp := IsResidualMultiRefiner.compose g₂ hg₂ hends₂ h₁
    (hResR.trans subset_union_right) h₂ hR₂f
  have hone := oneX_compose g₂ hg₂ h₁.disjoint hResR hone₁ h₂ hR₂f
  rw [image_image] at hcomp hone
  have hendsX : ∀ c, ends₂ ((g₂ ∘ g₁) c) = ends c := fun c => by simp [hends₂, hends₁]
  set R := R₁.image g₂ ∪ R₂ with hRdef
  set 𝒲 := 𝒲₁.image (image g₂) ∪ 𝒲₂ with h𝒲def
  have hpdeg : ∀ S : Finset (Fin n), S.card = r - 1 →
      pdeg ends₂ 𝒲 S ≤ Cst * (D₀ + sharpCost r n) +
        Cf * (Cst * winCost r n + 1 + sharpCost r n) := by
    intro S hS
    refine (pdeg_union_le _ _ _ S).trans (Nat.add_le_add ?_ (hpd₂ S hS))
    exact (pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)
  refine ⟨E₂, inferInstance, g₂ ∘ g₁, ends₂, R, 𝒲, hg₂.comp hg₁, hendsX,
    isMultiRefinerF_of_residual hcomp (fun _ _ => subset_univ _) hone,
    (isCRefinedMultiFamily_of_residual hcomp).mono (by omega), ?_, ?_⟩
  · -- the refinement degree
    have hmr := mrefDeg_le_of (r := r) hpdeg (by omega)
    have hw : winCost r n ≤ sharpCost r n := winCost_le_sharpCost r n
    have hbound : Cst * (D₀ + sharpCost r n) + Cf * (Cst * winCost r n + 1 + sharpCost r n) ≤
        Cst * D₀ + K * sharpCost r n + Cf := by
      have : Cf * (Cst * winCost r n) ≤ Cf * (Cst * sharpCost r n) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hw)
      have e : Cst * D₀ + K * sharpCost r n + Cf = Cst * D₀ + Cst * sharpCost r n +
          Cf * (Cst * sharpCost r n) + Cf * sharpCost r n + Cf := by rw [hK]; ring
      nlinarith
    have hmr' : (mrefDeg r ends₂ 𝒲 : ℝ) ≤ Cst * D₀ + K * sharpCost r n + Cf := by
      exact_mod_cast hmr.trans hbound
    have hL1 : (1 : ℝ) ≤ budget n r := HyperPlan.one_le_rpow_log (by omega) hn3
    have hsc := sharpCost_le_budget hr hn3
    have hΔD : (D₀ : ℝ) ≤ bigDelta r ends X := le_max_left _ _
    have hΔL : budget n r ≤ bigDelta r ends X := le_max_right _ _
    have hCreal : ((Cst + 30 * K + Cf : ℕ) : ℝ) ≤ C := by exact_mod_cast (by omega)
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hCst0 : (0 : ℝ) ≤ Cst := Nat.cast_nonneg _
    have hCf0 : (0 : ℝ) ≤ Cf := Nat.cast_nonneg _
    have hΔ0 : (0 : ℝ) ≤ bigDelta r ends X := le_trans (by norm_num) (hL1.trans hΔL)
    push_cast at hCreal
    calc (mrefDeg r ends₂ 𝒲 : ℝ) ≤ Cst * D₀ + K * sharpCost r n + Cf := hmr'
      _ ≤ Cst * bigDelta r ends X + K * (30 * bigDelta r ends X) + Cf * bigDelta r ends X := by
          gcongr
          · linarith
          · nlinarith
      _ = (Cst + 30 * K + Cf) * bigDelta r ends X := by ring
      _ ≤ C * bigDelta r ends X := mul_le_mul_of_nonneg_right hCreal hΔ0
  · -- flatness
    intro c hc
    have hcr : (ends₂ c).card = r := hcomp.rgraph c (mem_union_right _ hc)
    refine Original2024.card_sdiff_le_of_meets hcr ?_
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      rw [hends₂]
      exact hmeet₁ c₁ hc₁
    · exact hmeet₂ c h

end RefinedAbsorption.Faithful2024
