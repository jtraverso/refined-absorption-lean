module
public import RequestProject.Original2024.Flat

/-!
# Theorem 3.8 with the flatness output, `r = 1`

For `r = 1` the chain refiner (`RefinerOne/`) is placed with its new vertices inside the given
set `Y`: the pool of vertices is `Y ∪ V(X)`, and the new vertices avoid `V(X)`, so they lie in
`Y`.  Hence every new copy is `0`-flat to `Y`.

* `hostChainPool`: the chain refiner inside a host `1`-graph `G` with `4 q |X| ≤ |G|`.
* `multiRefinerFlat_one`, `theorem_3_8_flat_one`, and **`theorem_3_8_flat`** (all `q > r ≥ 1`).
-/

@[expose] public section

namespace RefinedAbsorption.Original2024

open Finset RefinedAbsorption.ChainRefiner

/-- **The chain refiner inside a host `1`-graph with a large pool.** -/
theorem hostChainPool {q : ℕ} (hq : 2 ≤ q) (n : ℕ) (G X : Finset (Finset (Fin n)))
    (hG : IsRGraph 1 G) (hXG : X ⊆ G) (hpool : 4 * q * X.card ≤ G.card) :
    ∃ (R : Finset (Finset (Fin n))) (𝒲 : Finset (Finset (Finset (Fin n)))),
      IsRefinedRefiner q 1 (8 * q) X R 𝒲 ∧ R ⊆ G ∧
      (∀ W ∈ 𝒲, (W.filter (· ∈ X)).card ≤ 1) ∧
      R.card ≤ 3 * q * X.card ∧ 𝒲.card ≤ 3 * q * X.card := by
  classical
  have hX : IsRGraph 1 X := fun e he => hG e (hXG he)
  by_cases hX0 : X = ∅
  · subst hX0
    exact ⟨∅, ∅, (refinerAbsorbers_empty q 1 (8 * q) n 0).1, empty_subset _,
      fun W hW => absurd hW (Finset.notMem_empty W), by simp, by simp⟩
  set Xv := X.biUnion id with hXvdef
  have hXeq : X = sing Xv := eq_sing_biUnion hX
  set Pool := G.biUnion id with hPooldef
  have hGeq : G = sing Pool := eq_sing_biUnion hG
  have hXP : Xv ⊆ Pool := biUnion_subset_biUnion_of_subset_left _ hXG
  set m := Xv.card with hmdef
  have hm : 1 ≤ m := by
    rw [Nat.one_le_iff_ne_zero, hmdef, Ne, ← card_sing, ← hXeq, card_eq_zero]
    exact hX0
  have hXc : X.card = m := by rw [hXeq, card_sing]
  have hGc : G.card = Pool.card := by rw [hGeq, card_sing]
  have hfresh : (m + 2) * (q - 1) ≤ Pool.card - m := by
    have h4 : 4 * q * m ≤ Pool.card := by rw [← hXc, ← hGc]; exact hpool
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (m + 2) * p + m ≤ 4 * (p + 1) * m := by nlinarith
    omega
  have hn : 0 < n := by
    obtain ⟨v, hv⟩ : Xv.Nonempty := by rw [← card_pos]; omega
    exact Fin.pos v
  obtain ⟨g, hg, hgX, hgP⟩ := exists_chain_labelling_in (q := q) Pool Xv hXP rfl hfresh ⟨0, hn⟩
  have hXg : X = Xg m g := by rw [Xg, hgX, hXeq]
  have hRm : (Rg q m g).card ≤ 3 * q * m := (card_Rg_le (g := g) (m := m) (q := q) (by omega)).trans
    (by
      obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith)
  refine ⟨Rg q m g, 𝒲g q m g, ?_, ?_, fun W hW => hXg ▸ chain_oneX (by omega) hg hW, hXc ▸ hRm,
    hXc ▸ (card_𝒲g_le q m g).trans (show m * q * 2 + 1 ≤ 3 * q * m by nlinarith)⟩
  · rw [hXg]; exact chain_isRefinedRefiner (by omega) hg (by omega)
  · rw [hGeq, Rg]
    refine sing_mono ?_
    intro v hv
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
    exact hgP a (Rlab_union_Xlab_subset (by omega) (mem_union_left _ ha))

/-- **The flat multi-refiner conclusion for `r = 1`**: the new vertices lie in `Y`. -/
theorem multiRefinerFlat_one {q : ℕ} (hq : 2 ≤ q) : MultiRefinerFlatConclusion q 1 := by
  refine ⟨12 * q, by omega, 0, fun n _ X D hX hXD hDn Y hY => ?_⟩
  have hXD' : (X.card : ℝ) ≤ D := by
    have h := hXD ∅ (by simp)
    rwa [RefinedAbsorption.ChainRefiner.deg_empty] at h
  have hq0 : (0 : ℝ) < ((12 * q : ℕ) : ℝ) := by positivity
  have hXn : 12 * q * X.card ≤ n := by
    have h1 : (X.card : ℝ) ≤ n / ((12 * q : ℕ) : ℝ) := hXD'.trans hDn
    rw [le_div_iff₀ hq0] at h1
    have : (((12 * q * X.card : ℕ)) : ℝ) ≤ n := by push_cast at h1 ⊢; linarith
    exact_mod_cast this
  set G := sing Y ∪ X with hGdef
  have hG : IsRGraph 1 G := by
    intro e he
    rcases mem_union.1 he with h | h
    · obtain ⟨a, -, rfl⟩ := mem_sing.1 h; simp
    · exact hX e h
  have hpool : 4 * q * X.card ≤ G.card := by
    have h1 : Y.card ≤ G.card := by
      rw [← card_sing Y]; exact card_le_card subset_union_left
    have e1 : 12 * q * X.card = 3 * (4 * q * X.card) := by ring
    omega
  obtain ⟨R, 𝒲, hR, hRG, honeX, hRc, h𝒲c⟩ := hostChainPool hq n G X hG subset_union_right hpool
  have hRY : ∀ e ∈ R, ∃ a ∈ Y, {a} = e := by
    intro e he
    rcases mem_union.1 (hRG he) with h | h
    · exact mem_sing.1 h
    · exact absurd h (disjoint_right.1 hR.disjoint he)
  have hS0 : ∀ S : Finset (Fin n), S.card = 1 - 1 → S = ∅ := fun S hS => by
    rw [← card_eq_zero]; omega
  have hmulti := (IsRefinedRefiner.toMulti hR).mono (show 8 * q ≤ 12 * q by omega)
  refine ⟨Finset (Fin n), inferInstance, id, X, X, R, 𝒲, X.card, image_id, ?_,
    ⟨fun _ _ => subset_univ _, hmulti⟩,
    ⟨hmulti, subset_rfl, Set.injOn_id _, honeX, fun S hS => ?_, fun S hS => ?_,
      fun S hS => ?_⟩, ?_⟩
  · have hM : D ≤ max D (budget n 1) := le_max_left _ _
    have hq1 : (1 : ℝ) ≤ 12 * q := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    have h0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
    push_cast
    nlinarith
  · rw [hS0 S hS]
    exact le_of_eq (RefinedAbsorption.ChainRefiner.deg_empty X)
  · rw [hS0 S hS]
    show deg R ∅ ≤ _
    rw [RefinedAbsorption.ChainRefiner.deg_empty]
    exact hRc.trans (Nat.mul_le_mul_right _ (by omega))
  · exact (card_filter_le _ _).trans (h𝒲c.trans (Nat.mul_le_mul_right _ (by omega)))
  · intro e he
    obtain ⟨a, ha, rfl⟩ := hRY e he
    simp [ha]

/-- **Theorem 3.8 with the flatness output**, `r = 1`. -/
theorem theorem_3_8_flat_one {q : ℕ} (hq : 2 ≤ q) : Theorem_3_8_flat_for q 1 :=
  fun _ => multiRefinerFlat_one hq

/-- **Theorem 3.8 (multi-refiner theorem) with the flatness output**, for all `q > r ≥ 1`: the
multi-refiner of `X` can be chosen `(r-1)`-flat to any prescribed set `Y` with `|Y| ≥ n/3`. -/
theorem theorem_3_8_flat : ∀ q r : ℕ, 1 ≤ r → r < q → Theorem_3_8_flat_for q r := by
  intro q r hr hrq
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    exact theorem_3_8_flat_one (by omega)
  · exact theorem_3_8_flat_two_le h hrq

/-- The flat multi-refiner conclusion holds for all `q > r ≥ 1` (unconditionally). -/
theorem multiRefinerFlat : ∀ q r : ℕ, 1 ≤ r → r < q → MultiRefinerFlatConclusion q r :=
  fun q r hr hrq => theorem_3_8_flat q r hr hrq fun q' r' _ _ hr'q' =>
    theorem_1_11 q' r' (by omega) hr'q'

/-- **The other reading of the flatness output.**  From the flat conclusion one also gets a set
`Y` with `|Y| ≥ n/3` such that every new copy has at most `r - 1` vertices **inside** `Y` (no new
copy lies inside `Y`): apply the flat conclusion to a set `Z` of `⌈n/3⌉` vertices and take
`Y = V \ Z`. -/
theorem MultiRefinerFlatConclusion.exists_inside {q r : ℕ} (h : MultiRefinerFlatConclusion q r) :
    ∃ C : ℕ, 1 ≤ C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Finset (Fin n)), ∀ D : ℝ,
      IsRGraph r X → MaxDegLE r X D → D ≤ n / C →
      ∃ (Y : Finset (Fin n)) (E : Type) (_ : DecidableEq E) (ends : E → Finset (Fin n))
        (K Xl R : Finset E) (𝒲 : Finset (Finset E)) (B : ℕ),
        n ≤ 3 * Y.card ∧ Xl.image ends = X ∧ (B : ℝ) ≤ C * max D (budget n r) ∧
        IsMultiRefinerOn q r C (univ : Finset (Fin n)) ends Xl R 𝒲 ∧
        Placement.IsStrongMultiRefiner q r C ends K Xl R 𝒲 B ∧
        ∀ c ∈ R, (ends c ∩ Y).card ≤ r - 1 := by
  obtain ⟨C, hC, n₀, h⟩ := h
  refine ⟨C, hC, max n₀ 2, fun n hn X D hX hXD hDn => ?_⟩
  have hn2 : 2 ≤ n := le_of_max_le_right hn
  obtain ⟨Z, -, hZc⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n)))
    (n := (n + 2) / 3) (by rw [card_univ, Fintype.card_fin]; omega)
  obtain ⟨E, hE, ends, K, Xl, R, 𝒲, B, h1, h2, h3, h4, h5⟩ :=
    h n (le_of_max_le_left hn) X D hX hXD hDn Z (by omega)
  have hYc : (univ \ Z).card = n - (n + 2) / 3 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, hZc]
  refine ⟨univ \ Z, E, hE, ends, K, Xl, R, 𝒲, B, by omega, h1, h2, h3, h4, fun c hc => ?_⟩
  have hflat := h5 c hc
  have : ends c ∩ (univ \ Z) = ends c \ Z := by
    ext v; simp [mem_sdiff]
  rw [this]
  exact hflat

end RefinedAbsorption.Original2024
