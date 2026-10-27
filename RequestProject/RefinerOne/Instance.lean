module
public import RequestProject.RefinerOne.Transfer

/-!
# `RefinerWithAbsorbers` for `r = 1`

The instance `RefinerAbsorbersFor q 1` (every `q ≥ 2`) of the refined-refiner-with-absorbers
statement, proved by the chain construction: the refiner of a `1`-graph `X` with `m` vertices
uses at most `(m + 2)(q - 1)` new vertices, every piece is a single copy of `K_q^1` (or empty),
so empty absorbers can be attached.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset ChainRefiner

/-- An injective labelling of the chain labels which maps the input labels onto a given set. -/
lemma exists_chain_labelling {n q m : ℕ} (Xv : Finset (Fin n)) (hXv : Xv.card = m)
    (hfresh : (m + 2) * (q - 1) ≤ n - m) (v0 : Fin n) :
    ∃ g : Lab → Fin n, Set.InjOn g (Ulab q m) ∧ (Xlab m).image g = Xv := by
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
  obtain ⟨F, hF, hFc⟩ := exists_subset_card_eq (s := univ \ Xv) (n := (m + 2) * (q - 1))
    (by rw [card_univ_diff, Fintype.card_fin, hXv]; exact hfresh)
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
  refine ⟨g, ?_, ?_⟩
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

/-- A `1`-graph is the set of singletons of its vertices. -/
lemma eq_sing_biUnion {V : Type*} [DecidableEq V] {X : Finset (Finset V)} (hX : IsRGraph 1 X) :
    X = sing (X.biUnion id) := by
  ext e
  constructor
  · intro he
    obtain ⟨a, rfl⟩ := card_eq_one.1 (hX e he)
    rw [singleton_mem_sing]
    exact mem_biUnion.2 ⟨{a}, he, mem_singleton_self a⟩
  · intro he
    obtain ⟨a, ha, rfl⟩ := mem_sing.1 he
    obtain ⟨f, hf, haf⟩ := mem_biUnion.1 ha
    obtain ⟨c, rfl⟩ := card_eq_one.1 (hX f hf)
    rw [id, mem_singleton] at haf
    rwa [haf]

/-- **`RefinerWithAbsorbers` holds for `r = 1`.** -/
theorem refinerAbsorbersFor_one {q : ℕ} (hq : 2 ≤ q) : RefinerAbsorbersFor q 1 := by
  refine ⟨8 * q, by omega, fun n X D hX hXD hDn => ?_⟩
  classical
  by_cases hX0 : X = ∅
  · subst hX0
    exact ⟨∅, ∅, _, _, _, refinerAbsorbers_empty q 1 (8 * q) n D⟩
  set Xv := X.biUnion id with hXvdef
  have hXeq : X = sing Xv := eq_sing_biUnion hX
  set m := Xv.card with hmdef
  have hm : 1 ≤ m := by
    rw [Nat.one_le_iff_ne_zero, hmdef, Ne, ← card_sing, ← hXeq, card_eq_zero]
    exact hX0
  have hmD : (m : ℝ) ≤ D := by
    have h := hXD ∅ (by simp)
    rwa [deg_empty, hXeq, card_sing] at h
  have hq0 : (0 : ℝ) < 8 * q := by positivity
  have hnm : 8 * q * m ≤ n := by
    have h1 : (8 * q : ℝ) * D ≤ n := by
      rw [show ((8 * q : ℕ) : ℝ) = 8 * q by push_cast; ring] at hDn
      rw [le_div_iff₀ hq0] at hDn
      linarith
    have h2 : ((8 * q * m : ℕ) : ℝ) ≤ n := by
      push_cast
      nlinarith
    exact_mod_cast h2
  have hfresh : (m + 2) * (q - 1) ≤ n - m := by
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (m + 2) * p + m ≤ 8 * (p + 1) * m := by nlinarith
    omega
  have hn : 0 < n := by nlinarith
  obtain ⟨g, hg, hgX⟩ := exists_chain_labelling (q := q) Xv rfl hfresh ⟨0, hn⟩
  have hXg : X = Xg m g := by rw [Xg, hgX, hXeq]
  obtain ⟨Qon, hQon⟩ := isAttachedAbsorbers_empty (q := q) (r := 1) (X := X)
    (R := Rg q m g) (𝒲 := 𝒲g q m g)
    (fun W hW => chain_hasDecomposition (by omega) hg hW)
  refine ⟨Rg q m g, 𝒲g q m g, fun _ => ∅, Qon, fun _ => ∅, ?_, hQon, ?_⟩
  · rw [hXg]
    exact chain_isRefinedRefiner (by omega) hg (by omega)
  · intro S hS
    have hS0 : S = ∅ := by rw [← card_eq_zero]; omega
    subst hS0
    have hsup : (𝒲g q m g).sup (fun _ => (∅ : Finset (Finset (Fin n)))) = ∅ :=
      (Finset.sup_eq_bot_iff _ _).2 (fun _ _ => rfl)
    rw [hsup, union_empty, deg_empty]
    have hR := card_Rg_le (g := g) (m := m) (q := q) (by omega)
    have hR' : ((Rg q m g).card : ℝ) ≤ 3 * q * m := by
      have : (Rg q m g).card ≤ 3 * q * m := hR.trans (by
        obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        nlinarith)
      exact_mod_cast this
    have hM : D ≤ max D ((n : ℝ) ^ (1 - 1 / ((1 : ℕ) : ℝ)) * Real.log n) := le_max_left _ _
    push_cast
    have hq1 : (0 : ℝ) ≤ q := by positivity
    nlinarith

end RefinedAbsorption
