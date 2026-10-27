module
public import RequestProject.OddGrid.Assemble

/-!
# The grid on `Fin n`

With `s = ⌊√n⌋` and `R = ⌊n / s⌋`, the vertex `i < s R` sits on the cell `(i / s, i % s)` of the
`R × s` board (`baseG`), and the remaining `n - s R < s` vertices sit in an extra column `s`
(`baseGb`).  `base_plan`: every graph on `Fin n` (`n ≥ 25`) with maximum degree `≤ D` has a valid
plan with at most `256` final pairs and load `≤ 5 D + 400 s ⌈log₂ n⌉` at every vertex.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset Classical

variable {n : ℕ}

/-- Coordinates of the vertices of `Fin n`. -/
def bco (n : ℕ) (i : Fin n) : ℕ × ℕ :=
  if i.val < Nat.sqrt n * (n / Nat.sqrt n) then (i.val / Nat.sqrt n, i.val % Nat.sqrt n)
  else (i.val - Nat.sqrt n * (n / Nat.sqrt n), Nat.sqrt n)

lemma sqrt_le_div (n : ℕ) : Nat.sqrt n ≤ n / Nat.sqrt n := by
  rcases Nat.eq_zero_or_pos (Nat.sqrt n) with h | h
  · rw [h]; exact Nat.zero_le _
  · exact (Nat.le_div_iff_mul_le h).2 (Nat.sqrt_le n)

lemma lt_mul_add (n : ℕ) : n < Nat.sqrt n * (n / Nat.sqrt n) + Nat.sqrt n ∨ Nat.sqrt n = 0 := by
  rcases Nat.eq_zero_or_pos (Nat.sqrt n) with h | h
  · exact Or.inr h
  · left
    have h1 := Nat.div_add_mod n (Nat.sqrt n)
    have h2 := Nat.mod_lt n h
    omega

/-- The full grid of the first `s R` vertices. -/
def baseG (n : ℕ) (hn : 1 ≤ n) : Grid n where
  act i := i.val < Nat.sqrt n * (n / Nat.sqrt n)
  co := bco n
  R := n / Nat.sqrt n
  C := Nat.sqrt n
  inj v w hv hw h := by
    simp only [bco, if_pos hv, if_pos hw, Prod.mk.injEq] at h
    apply Fin.ext
    rw [← Nat.div_add_mod v.val (Nat.sqrt n), ← Nat.div_add_mod w.val (Nat.sqrt n), h.1, h.2]
  bdd v hv := by
    have hs : 0 < Nat.sqrt n := Nat.sqrt_pos.2 hn
    simp only [bco, if_pos hv]
    exact ⟨(Nat.div_lt_iff_lt_mul hs).2 (by rw [mul_comm]; exact hv), Nat.mod_lt _ hs⟩

/-- All vertices, with the extra column `s`. -/
def baseGb (n : ℕ) (hn : 1 ≤ n) : Grid n where
  act _ := True
  co := bco n
  R := n / Nat.sqrt n
  C := Nat.sqrt n + 1
  inj v w _ _ h := by
    have hs : 0 < Nat.sqrt n := Nat.sqrt_pos.2 hn
    unfold bco at h
    split_ifs at h with hv hw hw
    · simp only [Prod.mk.injEq] at h
      apply Fin.ext
      rw [← Nat.div_add_mod v.val (Nat.sqrt n), ← Nat.div_add_mod w.val (Nat.sqrt n), h.1, h.2]
    · simp only [Prod.mk.injEq] at h
      have := Nat.mod_lt v.val hs; omega
    · simp only [Prod.mk.injEq] at h
      have := Nat.mod_lt w.val hs; omega
    · simp only [Prod.mk.injEq] at h
      apply Fin.ext; omega
  bdd v _ := by
    have hs : 0 < Nat.sqrt n := Nat.sqrt_pos.2 hn
    have h1 := sqrt_le_div n
    have h2 := lt_mul_add n
    have hvn := v.isLt
    unfold bco
    split_ifs with hv
    · exact ⟨(Nat.div_lt_iff_lt_mul hs).2 (by rw [mul_comm]; exact hv),
        by have := Nat.mod_lt v.val hs; omega⟩
    · constructor <;> omega

lemma baseG_full (hn : 1 ≤ n) : (baseG n hn).Full := by
  intro a ha b hb
  have hs : 0 < Nat.sqrt n := Nat.sqrt_pos.2 hn
  simp only [baseG] at ha hb
  have hlt : a * Nat.sqrt n + b < Nat.sqrt n * (n / Nat.sqrt n) := by
    have : (a + 1) * Nat.sqrt n ≤ (n / Nat.sqrt n) * Nat.sqrt n := Nat.mul_le_mul_right _ ha
    nlinarith
  have hn' : a * Nat.sqrt n + b < n :=
    lt_of_lt_of_le hlt (by rw [mul_comm]; exact Nat.div_mul_le_self n _)
  refine ⟨⟨a * Nat.sqrt n + b, hn'⟩, hlt, ?_⟩
  simp only [baseG, bco, if_pos hlt]
  ext
  · simp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt hb, zero_add]
  · simp only
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

lemma base_extraOK (hn : 1 ≤ n) : Grid.ExtraOK (baseG n hn) (baseGb n hn) where
  co _ := rfl
  sub _ _ := trivial
  col v _ hv := by
    have h1 := sqrt_le_div n
    have h2 := lt_mul_add n
    have hs : 0 < Nat.sqrt n := Nat.sqrt_pos.2 hn
    have hvn := v.isLt
    simp only [baseG] at hv ⊢
    simp only [bco, if_neg hv]
    generalize n / Nat.sqrt n = R at *
    generalize Nat.sqrt n = s at *
    refine ⟨trivial, ?_⟩
    omega

lemma div_sqrt_le (n : ℕ) : n / Nat.sqrt n ≤ Nat.sqrt n + 2 := by
  rcases Nat.eq_zero_or_pos (Nat.sqrt n) with h | h
  · rw [h]; simp
  · apply Nat.div_le_of_le_mul
    have := Nat.lt_succ_sqrt' n
    nlinarith

lemma base_budget (hn : 25 ≤ n) (D : ℕ) :
    gridBudget D (n / Nat.sqrt n) (Nat.sqrt n) (n / Nat.sqrt n) (Nat.sqrt n + 1) ≤
      5 * D + 400 * Nat.sqrt n * Nat.clog 2 n := by
  have hs : 5 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
  have hR := div_sqrt_le n
  have hR' := sqrt_le_div n
  have hc1 : 1 ≤ Nat.clog 2 n := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) (by omega))
  have hcs : Nat.clog 2 (Nat.sqrt n) ≤ Nat.clog 2 n := Nat.clog_mono_right _ (Nat.sqrt_le_self n)
  have hcR : Nat.clog 2 (n / Nat.sqrt n) ≤ Nat.clog 2 n := Nat.clog_mono_right _ (Nat.div_le_self _ _)
  set s := Nat.sqrt n
  set R := n / s
  set c := Nat.clog 2 n
  unfold gridBudget
  have e1 : 2 * Nat.clog 2 s * (25 * (R + s) + 1) ≤ 2 * c * (25 * (2 * s + 2) + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hcs) (by omega)
  have e2 : 2 * Nat.clog 2 R * (25 * (4 + R) + 1) ≤ 2 * c * (25 * (s + 6) + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hcR) (by omega)
  have e3 : 80 + 50 * s ≤ 130 * c * s := by nlinarith
  nlinarith

/-- **The plan on `Fin n`.** -/
theorem base_plan (hn : 25 ≤ n) {X : Finset (Finset (Fin n))} (hX2 : ∀ e ∈ X, e.card = 2) {D : ℕ}
    (hD : ∀ v, (X.filter (v ∈ ·)).card ≤ D) :
    ∃ sp : List (Spec n), PlanOK sp X ∧ 1 ≤ sp.length ∧ (prun sp X sp.length).card ≤ 256 ∧
      ∀ v, ∑ t ∈ range sp.length, pass sp X t v ≤ 5 * D + 400 * Nat.sqrt n * Nat.clog 2 n := by
  have hn1 : 1 ≤ n := by omega
  have hs : 5 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
  obtain ⟨sp, h1, h2, h3, h4⟩ := Grid.grid_plan (baseG_full hn1)
    (show 2 ≤ (baseG n hn1).R from le_trans (by omega) (sqrt_le_div n)) hs
    (base_extraOK hn1) (fun _ => trivial) le_rfl hX2 hD
  exact ⟨sp, h1, h2, h3, fun v => (h4 v).trans (base_budget hn D)⟩

end RefinedAbsorption.OddGrid
