module
public import RequestProject.Original2024.Host
public import RequestProject.RefinerOne.Instance

/-!
# Theorems 1.11 and 1.7 of the original article for `r = 1`

For `r = 1` the chain refiner of `RefinerOne/` is placed on vertices of the host `G`: the new
vertices are chosen among the vertices `v` with `{v} ∈ G` that are not vertices of `X`.  Every
piece is empty or a single copy of `K_q^1`, so no absorbers are needed.
-/

@[expose] public section

namespace RefinedAbsorption.Original2024

open Finset RefinedAbsorption.ChainRefiner

/-- An injective labelling of the chain labels which maps the input labels onto a given set. -/
lemma exists_chain_labelling_in {n q m : ℕ} (Pool Xv : Finset (Fin n)) (hXP : Xv ⊆ Pool)
    (hXv : Xv.card = m) (hfresh : (m + 2) * (q - 1) ≤ Pool.card - m) (v0 : Fin n) :
    ∃ g : Lab → Fin n, Set.InjOn g (Ulab q m) ∧ (Xlab m).image g = Xv ∧
      ∀ a ∈ Ulab q m, g a ∈ Pool := by
  classical
  set Z : Finset Lab := (range (m + 2) ×ˢ range (q - 1)).image (fun p => zl p.1 p.2) with hZdef
  have hZ : Z.card = (m + 2) * (q - 1) := by
    rw [hZdef, card_image_of_injective _ ?_]
    · simp
    · intro p p' h
      obtain ⟨h1, h2⟩ := zl_inj.1 h
      exact Prod.ext h1 h2
  have hXl : (Xlab m).card = m := by
    rw [Xlab, card_image_of_injective _ (fun _ _ h => xl_inj.1 h)]; simp
  obtain ⟨F, hF, hFc⟩ := exists_subset_card_eq (s := Pool \ Xv) (n := (m + 2) * (q - 1))
    (by rw [card_sdiff_of_subset hXP, hXv]; exact hfresh)
  let e1 := equivOfCardEq (s := Xlab m) (t := Xv) (by rw [hXl, hXv])
  let e2 := equivOfCardEq (s := Z) (t := F) (by rw [hZ, hFc])
  let g : Lab → Fin n := fun a =>
    if h : a ∈ Xlab m then (e1 ⟨a, h⟩ : Fin n) else if h' : a ∈ Z then (e2 ⟨a, h'⟩ : Fin n)
      else v0
  have hXZ : Disjoint (Xlab m) Z := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨k, -, rfl⟩ := mem_image.1 ha
    obtain ⟨p, -, hp⟩ := mem_image.1 hb
    exact xl_ne_zl _ _ _ hp.symm
  have gX : ∀ a (h : a ∈ Xlab m), g a = e1 ⟨a, h⟩ := fun a h => by simp [g, h]
  have gZ : ∀ a (h : a ∈ Z), g a = e2 ⟨a, h⟩ := fun a h => by
    simp [g, h, Finset.disjoint_right.1 hXZ h]
  have hFX : ∀ v ∈ F, v ∉ Xv := fun v hv => (mem_sdiff.1 (hF hv)).2
  refine ⟨g, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have hU : ∀ c, c ∈ (Ulab q m : Set Lab) → c ∈ Xlab m ∨ c ∈ Z := fun c hc => by
      have h : c ∈ Xlab m ∪ Z := hc
      exact mem_union.1 h
    rcases hU a ha with ha' | ha' <;> rcases hU b hb with hb' | hb'
    · rw [gX a ha', gX b hb'] at hab
      exact congrArg Subtype.val (e1.injective (Subtype.ext hab))
    · rw [gX a ha', gZ b hb'] at hab
      exact absurd ((e1 ⟨a, ha'⟩).2) (hab ▸ hFX _ (e2 ⟨b, hb'⟩).2)
    · rw [gZ a ha', gX b hb'] at hab
      exact absurd ((e1 ⟨b, hb'⟩).2) (hab ▸ hFX _ (e2 ⟨a, ha'⟩).2)
    · rw [gZ a ha', gZ b hb'] at hab
      exact congrArg Subtype.val (e2.injective (Subtype.ext hab))
  · ext v
    constructor
    · intro hv
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
      rw [gX a ha]
      exact (e1 ⟨a, ha⟩).2
    · intro hv
      refine mem_image.2 ⟨(e1.symm ⟨v, hv⟩ : Lab), (e1.symm ⟨v, hv⟩).2, ?_⟩
      rw [gX _ (e1.symm ⟨v, hv⟩).2]
      simp
  · intro a ha
    have h : a ∈ Xlab m ∪ Z := ha
    rcases mem_union.1 h with ha' | ha'
    · rw [gX a ha']; exact hXP (e1 ⟨a, ha'⟩).2
    · rw [gZ a ha']; exact (mem_sdiff.1 (hF (e2 ⟨a, ha'⟩).2)).1


lemma xl_mem_piece {q i t k : ℕ} {e : Bool} (h : xl k ∈ piece q i t e) : k = i := by
  simp only [piece, mem_union, mem_image, xl, zl] at h
  rcases h with ⟨j, -, hj⟩ | h | ⟨j, -, hj⟩
  · exact absurd hj (by simp)
  · split_ifs at h with he
    · simpa using h
    · simp at h
  · exact absurd hj (by simp)

/-- Every piece of the chain refiner contains at most one edge of `X`. -/
lemma chain_oneX {V : Type*} [DecidableEq V] {q m : ℕ} {g : Lab → V} (hq : 1 ≤ q)
    (hg : Set.InjOn g (Ulab q m)) {W : Finset (Finset V)} (hW : W ∈ 𝒲g q m g) :
    (W.filter (· ∈ Xg m g)).card ≤ 1 := by
  obtain ⟨P, rfl, hP⟩ := mem_𝒲g hW
  have hPU : P ⊆ Ulab q m := by
    rcases hP with rfl | ⟨x, hx, rfl⟩
    · exact finPiece_subset_U hq
    · exact piece_subset_U hq hx
  have hsub : (sing (P.image g)).filter (· ∈ Xg m g) ⊆
      sing ((P.filter (· ∈ Xlab m)).image g) := by
    intro f hf
    rw [mem_filter] at hf
    obtain ⟨v, hv, rfl⟩ := mem_sing.1 hf.1
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
    have h2 : g a ∈ (Xlab m).image g := singleton_mem_sing.1 hf.2
    have haX : a ∈ Xlab m := (mem_image_iff_of_injOn hg Xlab_subset_Ulab (hPU ha)).1 h2
    exact singleton_mem_sing.2 (mem_image_of_mem g (mem_filter.2 ⟨ha, haX⟩))
  refine (card_le_card hsub).trans ?_
  rw [card_sing]
  refine card_image_le.trans ?_
  rcases hP with rfl | ⟨x, hx, rfl⟩
  · rw [card_le_one]
    intro a ha
    obtain ⟨-, haX⟩ := mem_filter.1 ha
    obtain ⟨k, -, rfl⟩ := mem_image.1 haX
    exact absurd (mem_filter.1 ha).1 not_mem_finPiece_xl
  · rw [card_le_one]
    intro a ha b hb
    obtain ⟨ha1, haX⟩ := mem_filter.1 ha
    obtain ⟨hb1, hbX⟩ := mem_filter.1 hb
    obtain ⟨k, -, rfl⟩ := mem_image.1 haX
    obtain ⟨k', -, rfl⟩ := mem_image.1 hbX
    rw [xl_mem_piece ha1, xl_mem_piece hb1]

lemma card_𝒲g_le {V : Type*} [DecidableEq V] (q m : ℕ) (g : Lab → V) :
    (𝒲g q m g).card ≤ m * q * 2 + 1 := by
  refine (card_union_le _ _).trans ?_
  rw [card_singleton]
  refine Nat.add_le_add_right (card_image_le.trans (le_of_eq ?_)) 1
  simp [Idx, card_product]; ring

/-- **The chain refiner inside a host `1`-graph.** -/
theorem hostChain {q : ℕ} (hq : 2 ≤ q) (n : ℕ) (G X : Finset (Finset (Fin n))) (D : ℝ)
    (hG : IsRGraph 1 G) (hδ : MinDegGE 1 G ((1 - 1 / 2) * n)) (hXG : X ⊆ G)
    (hXD : MaxDegLE 1 X D) (hDn : D ≤ n / (8 * q : ℕ)) :
    ∃ (R : Finset (Finset (Fin n))) (𝒲 : Finset (Finset (Finset (Fin n)))),
      IsRefinedRefiner q 1 (8 * q) X R 𝒲 ∧ R ⊆ G ∧ (∀ W ∈ 𝒲, HasDecomposition q 1 W) ∧
      (R.card : ℝ) ≤ 3 * q * D ∧ (∀ W ∈ 𝒲, (W.filter (· ∈ X)).card ≤ 1) ∧
      R.card ≤ 3 * q * X.card ∧ 𝒲.card ≤ 3 * q * X.card := by
  classical
  have hX : IsRGraph 1 X := fun e he => hG e (hXG he)
  have hD0 : (0 : ℝ) ≤ D := by
    have h := hXD ∅ (by simp)
    exact le_trans (Nat.cast_nonneg _) h
  by_cases hX0 : X = ∅
  · subst hX0
    refine ⟨∅, ∅, (refinerAbsorbers_empty q 1 (8 * q) n D).1, empty_subset _,
      fun W hW => absurd hW (Finset.notMem_empty W), ?_, fun W hW => absurd hW (Finset.notMem_empty W),
      by simp, by simp⟩
    simp only [card_empty, Nat.cast_zero]; positivity
  set Xv := X.biUnion id with hXvdef
  have hXeq : X = sing Xv := eq_sing_biUnion hX
  set Pool := G.biUnion id with hPooldef
  have hGeq : G = sing Pool := eq_sing_biUnion hG
  have hXP : Xv ⊆ Pool := biUnion_subset_biUnion_of_subset_left _ hXG
  set m := Xv.card with hmdef
  have hm : 1 ≤ m := by
    rw [Nat.one_le_iff_ne_zero, hmdef, Ne, ← card_sing, ← hXeq, card_eq_zero]
    exact hX0
  have hmD : (m : ℝ) ≤ D := by
    have h := hXD ∅ (by simp)
    rwa [deg_empty, hXeq, card_sing] at h
  have hPool : (n : ℝ) / 2 ≤ Pool.card := by
    have h := hδ ∅ (by simp)
    rw [deg_empty, hGeq, card_sing] at h
    linarith
  have hq0 : (0 : ℝ) < (8 * q : ℕ) := by positivity
  have hnm : ((8 * q * m : ℕ) : ℝ) ≤ n := by
    rw [le_div_iff₀ hq0] at hDn
    push_cast at hDn ⊢
    nlinarith
  have hfresh : (m + 2) * (q - 1) ≤ Pool.card - m := by
    have h4 : 4 * q * m ≤ Pool.card := by
      have : ((4 * q * m : ℕ) : ℝ) ≤ Pool.card := by push_cast at hnm ⊢; linarith
      exact_mod_cast this
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (m + 2) * p + m ≤ 4 * (p + 1) * m := by nlinarith
    omega
  have hn : 0 < n := by
    have h8 : 0 < 8 * q * m := Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
    have h8' : (0 : ℝ) < ((8 * q * m : ℕ) : ℝ) := by exact_mod_cast h8
    have : (0 : ℝ) < n := lt_of_lt_of_le h8' hnm
    exact_mod_cast this
  obtain ⟨g, hg, hgX, hgP⟩ := exists_chain_labelling_in (q := q) Pool Xv hXP rfl hfresh ⟨0, hn⟩
  have hXg : X = Xg m g := by rw [Xg, hgX, hXeq]
  have hXc : X.card = m := by rw [hXeq, card_sing]
  have hRm : (Rg q m g).card ≤ 3 * q * m := (card_Rg_le (g := g) (m := m) (q := q) (by omega)).trans
    (by
      obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith)
  refine ⟨Rg q m g, 𝒲g q m g, ?_, ?_, fun W hW => chain_hasDecomposition (by omega) hg hW, ?_,
    fun W hW => hXg ▸ chain_oneX (by omega) hg hW, hXc ▸ hRm,
    hXc ▸ (card_𝒲g_le q m g).trans (show m * q * 2 + 1 ≤ 3 * q * m by nlinarith)⟩
  · rw [hXg]; exact chain_isRefinedRefiner (by omega) hg (by omega)
  · rw [hGeq, Rg]
    refine sing_mono ?_
    intro v hv
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
    exact hgP a (Rlab_union_Xlab_subset (by omega) (mem_union_left _ ha))
  · have hR := card_Rg_le (g := g) (m := m) (q := q) (by omega)
    have : (Rg q m g).card ≤ 3 * q * m := hR.trans (by
      obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith)
    have h' : ((Rg q m g).card : ℝ) ≤ 3 * q * m := by exact_mod_cast this
    have hq1 : (0 : ℝ) ≤ q := by positivity
    nlinarith

theorem deg_eq_card_of_one {n : ℕ} (R : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S.card + 1 = 1) : deg R S = R.card := by
  have : S = ∅ := by rw [← card_eq_zero]; omega
  subst this; exact deg_empty R

/-- **Theorem 1.11 (strong form), `r = 1`.** -/
theorem theorem_1_11_strong_one {q : ℕ} (hq : 2 ≤ q) : Theorem_1_11_strong_for q 1 := by
  refine ⟨8 * q, by omega, 1 / 2, by norm_num, ?_⟩
  intro n G X D hG hδ hXG hXD hDn
  have hX : IsRGraph 1 X := fun e he => hG e (hXG he)
  have hD0 : (0 : ℝ) ≤ D := le_trans (Nat.cast_nonneg _) (hXD ∅ (by simp))
  have hXD' : (X.card : ℝ) ≤ D := by
    have h := hXD ∅ (by simp)
    rwa [deg_empty] at h
  obtain ⟨R, 𝒲, hR, hRG, -, hRc, honeX, -, h𝒲c⟩ := hostChain hq n G X D hG hδ hXG hXD hDn
  have hRr : ∀ e ∈ R, e.card = 1 := fun e he => hR.rgraph e (mem_union_right _ he)
  have hM : D ≤ max D (budget n 1) := le_max_left _ _
  have hq1 : (0 : ℝ) ≤ q := by positivity
  refine ⟨R, 𝒲, chosenQR hR, ⟨fun e he => ⟨hX e he, subset_univ _⟩,
    fun e he => ⟨hRr e he, subset_univ _⟩, hR.disjoint,
    fun H hH => ⟨hR.subset H hH, hR.divisible H hH⟩,
    fun L hL hd => (chosenQR_spec hR hL hd).1, fun L hL hd => (chosenQR_spec hR hL hd).2.1,
    fun L hL hd => (chosenQR_spec hR hL hd).2.2⟩, hRG, ⟨hR.mult_le, hR.card_le, fun H hH => ?_⟩,
    fun S hS => ?_, honeX, fun S hS => ?_⟩
  · refine (Absorber17.card_vertexSet_le (fun e he => hR.rgraph e (hR.subset H hH he))
      (hR.card_le H hH)).trans ?_
    omega
  · rw [deg_eq_card_of_one R hS]
    push_cast
    nlinarith
  · have h1 : ((𝒲.filter fun H => S ⊆ vertexSet H).card : ℝ) ≤ 3 * q * X.card := by
      exact_mod_cast (card_filter_le _ _).trans h𝒲c
    push_cast
    nlinarith

/-- **Theorem 1.11, `r = 1`.** -/
theorem theorem_1_11_one {q : ℕ} (hq : 2 ≤ q) : Theorem_1_11_for q 1 := by
  obtain ⟨C, hC, ε, hε, h⟩ := theorem_1_11_strong_one hq
  refine ⟨C, hC, ε, hε, fun n G X D hG hδ hXG hXD hDn => ?_⟩
  obtain ⟨R, F, QR, h1, h2, h3, h4, -⟩ := h n G X D hG hδ hXG hXD hDn
  exact ⟨R, F, QR, h1, h2, h3, h4⟩

/-- **Theorem 1.7 (strong form), `r = 1`.** -/
theorem theorem_1_7_strong_one {q : ℕ} (hq : 2 ≤ q) : Theorem_1_7_strong_for q 1 := by
  refine ⟨16 * q, by omega, 1 / 2, by norm_num, ?_⟩
  intro n G X D hG hδ hXG hXD hDn
  have hX : IsRGraph 1 X := fun e he => hG e (hXG he)
  have hD0 : (0 : ℝ) ≤ D := le_trans (Nat.cast_nonneg _) (hXD ∅ (by simp))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hDn' : D ≤ n / (8 * q : ℕ) :=
    hDn.trans (div_le_div_of_nonneg_left hn0 (by positivity) (by push_cast; linarith))
  obtain ⟨R, 𝒲, hR, hRG, hdec, hRc, honeX, -⟩ := hostChain hq n G X D hG hδ hXG hXD hDn'
  obtain ⟨Qon, hA⟩ := isAttachedAbsorbers_empty (q := q) (r := 1) (X := X) (R := R) (𝒲 := 𝒲)
    hdec
  obtain ⟨QA, hQA, href⟩ := omniAbsorber_of_refiner_absorbers (by omega) (by omega) hR hA
  have hsup : 𝒲.sup (fun _ => (∅ : Finset (Finset (Fin n)))) = ∅ :=
    (Finset.sup_eq_bot_iff _ _).2 (fun _ _ => rfl)
  rw [hsup, union_empty] at hQA href
  have hRr : ∀ e ∈ R, e.card = 1 := fun e he => hR.rgraph e (mem_union_right _ he)
  have hon : ∀ W ∈ 𝒲, IsDecomposition q 1 W (Qon W) := by
    intro W hW
    have h := hA.on W hW
    rwa [empty_union] at h
  refine ⟨R, _, QA, ⟨fun e he => ⟨hX e he, subset_univ _⟩, fun e he => ⟨hRr e he, subset_univ _⟩,
    hQA.disjoint, fun Q hQ => ?_, hQA.subset_family, hQA.decomp⟩, hRG,
    fun e he => (href e he).trans (by omega), fun S hS => ?_, fun Q hQ => ?_⟩
  · obtain ⟨W, hW', hQW⟩ := mem_sup.1 hQ
    have hQ' : Q ∈ Qon W := by simpa using hQW
    refine ⟨(hon W hW').card_eq Q hQ', ((hon W hW').cliqueEdges_subset hQ').trans ?_⟩
    intro e he
    exact hR.subset W hW' he
  · rw [deg_eq_card_of_one R hS]
    have hM : D ≤ max D (budget n 1) := le_max_left _ _
    push_cast
    have hq1 : (0 : ℝ) ≤ q := by positivity
    nlinarith
  · obtain ⟨W, hW', hQW⟩ := mem_sup.1 hQ
    have hQ' : Q ∈ Qon W := by simpa using hQW
    refine le_trans (card_le_card ?_) (honeX W hW')
    intro e he
    rw [mem_filter] at he ⊢
    exact ⟨(hon W hW').cliqueEdges_subset hQ' he.1, he.2⟩

/-- **Theorem 1.7, `r = 1`.** -/
theorem theorem_1_7_one {q : ℕ} (hq : 2 ≤ q) : Theorem_1_7_for q 1 := by
  obtain ⟨C, hC, ε, hε, h⟩ := theorem_1_7_strong_one hq
  refine ⟨C, hC, ε, hε, fun n G X D hG hδ hXG hXD hDn => ?_⟩
  obtain ⟨A, F, QA, h1, h2, h3, h4, -⟩ := h n G X D hG hδ hXG hXD hDn
  exact ⟨A, F, QA, h1, h2, h3, h4⟩

end RefinedAbsorption.Original2024
