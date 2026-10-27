module
public import RequestProject.Extensions.Packing

/-!
# Asymptotically resolvable Steiner systems (from the Pippenger–Spencer theorem)

A Steiner system is *resolvable* if its blocks split into parallel classes (perfect matchings);
then exactly `R = binom(n-1, r-1) / binom(q-1, r-1)` classes are needed, the number of blocks
through a point.  We prove, taking the **Pippenger–Spencer theorem** (1989) as an external
classical input (`PippengerSpencer`, stated as a hypothesis, not proved here):

* `steiner_almost_resolvable`: for `q > r ≥ 2` and `ε > 0`, for all large `n`, the blocks of
  **every** `(n, q, r)`-Steiner system split into at most `(1 + ε) R` matchings (partial
  parallel classes);
* `exists_almost_resolvable_steiner`: together with the Existence Conjecture (proved in this
  project), for every large admissible `n` there is an `(n, q, r)`-Steiner system with this
  property;
* `resolution_classes_lower`: at least `R` matchings are always needed, so `(1 + ε) R` is
  asymptotically optimal.

The Steiner system is used as a `q`-uniform hypergraph on the `n` points: it is `R`-regular and
its codegrees equal `R (q-1)/(n-1) = o(R)` (`steiner_codeg_mul`).
-/

@[expose] public section

namespace RefinedAbsorption.Extensions

open Finset RefinedAbsorption.Original2024

/-- **The Pippenger–Spencer theorem** (external classical input, not proved here).  For every
`k ≥ 2` and `ε > 0` there are `δ > 0` and `D₀` such that every `k`-uniform hypergraph `H` whose
vertex degrees all lie in `[(1-δ)D, D]`, with `D ≥ D₀`, and whose codegrees are at most `δ D`,
has chromatic index at most `(1 + ε) D`: its edges can be coloured with `m ≤ (1 + ε) D` colours so
that edges of the same colour are disjoint. -/
def PippengerSpencer : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ D₀ : ℝ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (D : ℝ), D₀ ≤ D →
      (∀ e ∈ H, e.card = k) →
      (∀ v : V, (1 - δ) * D ≤ (deg H {v} : ℝ) ∧ (deg H {v} : ℝ) ≤ D) →
      (∀ u v : V, u ≠ v → (deg H {u, v} : ℝ) ≤ δ * D) →
      ∃ (m : ℕ) (c : Finset V → Fin m), (m : ℝ) ≤ (1 + ε) * D ∧
        ∀ e ∈ H, ∀ e' ∈ H, e ≠ e' → c e = c e' → Disjoint e e'

variable {q r n : ℕ}

/-- Every point of a Steiner system lies in `binom(n-1, r-1) / binom(q-1, r-1)` blocks. -/
theorem steiner_deg_point_mul {𝒮 : Finset (Finset (Fin n))}
    (h𝒮 : IsSteinerSystem q r 𝒮) (hr : 1 ≤ r) (v : Fin n) :
    (q - 1).choose (r - 1) * deg 𝒮 {v} = (n - 1).choose (r - 1) := by
  have := (isSteinerSystem_iff_isDecomposition.1 h𝒮).deg_eq {v} (by simpa using hr)
  rw [deg_completeRGraph (by simpa using hr), card_singleton] at this
  rw [this]; rfl

/-- Every pair of points of a Steiner system lies in `binom(n-2, r-2) / binom(q-2, r-2)` blocks. -/
theorem steiner_deg_pair_mul {𝒮 : Finset (Finset (Fin n))}
    (h𝒮 : IsSteinerSystem q r 𝒮) (hr : 2 ≤ r) {u v : Fin n} (huv : u ≠ v) :
    (q - 2).choose (r - 2) * deg 𝒮 {u, v} = (n - 2).choose (r - 2) := by
  have hc : ({u, v} : Finset (Fin n)).card = 2 := card_pair huv
  have := (isSteinerSystem_iff_isDecomposition.1 h𝒮).deg_eq {u, v} (by omega)
  rw [deg_completeRGraph (by omega), hc] at this
  rw [this]; rfl

/-- **Codegree identity:** `codeg · (n - 1) = deg · (q - 1)` in a Steiner system (`r ≥ 2`). -/
theorem steiner_codeg_mul {𝒮 : Finset (Finset (Fin n))}
    (h𝒮 : IsSteinerSystem q r 𝒮) (hr : 2 ≤ r) (hrq : r ≤ q) {u v : Fin n} (huv : u ≠ v) :
    deg 𝒮 {u, v} * (n - 1) = deg 𝒮 {v} * (q - 1) := by
  have hn : 2 ≤ n := by
    have := card_le_univ ({u, v} : Finset (Fin n))
    rw [card_pair huv, Fintype.card_fin] at this; exact this
  have ha := steiner_deg_point_mul h𝒮 (by omega) v
  have hb := steiner_deg_pair_mul h𝒮 hr huv
  obtain ⟨s, hs⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  obtain ⟨q', hq'⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  subst hs hn' hq'
  simp only [Nat.add_sub_cancel, show s + 2 - 1 = s + 1 by omega,
    show n' + 2 - 1 = n' + 1 by omega, show q' + 2 - 1 = q' + 1 by omega] at ha hb ⊢
  have e1 := Nat.add_one_mul_choose_eq n' s
  have e2 := Nat.add_one_mul_choose_eq q' s
  have hpos : 0 < q'.choose s * (s + 1) := Nat.mul_pos (Nat.choose_pos (by omega)) (by omega)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc deg 𝒮 {u, v} * (n' + 1) * (q'.choose s * (s + 1))
      = (q'.choose s * deg 𝒮 {u, v}) * ((n' + 1) * (s + 1)) := by ring
    _ = ((n' + 1) * n'.choose s) * (s + 1) := by rw [hb]; ring
    _ = (n' + 1).choose (s + 1) * (s + 1) * (s + 1) := by rw [e1]
    _ = ((q' + 1).choose (s + 1) * deg 𝒮 {v}) * (s + 1) * (s + 1) := by rw [ha]
    _ = deg 𝒮 {v} * ((q' + 1).choose (s + 1) * (s + 1)) * (s + 1) := by ring
    _ = deg 𝒮 {v} * ((q' + 1) * q'.choose s) * (s + 1) := by rw [e2]
    _ = deg 𝒮 {v} * (q' + 1) * (q'.choose s * (s + 1)) := by ring

/-- **Almost resolvability of every large Steiner system** (from Pippenger–Spencer). -/
theorem steiner_almost_resolvable (hPS : PippengerSpencer) (hr : 2 ≤ r) (hrq : r < q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮 →
      ∃ (m : ℕ) (c : Finset (Fin n) → Fin m),
        (m : ℝ) ≤ (1 + ε) * (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ∧
        ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B' := by
  obtain ⟨δ, hδ, D₀, hP⟩ := hPS q (by omega) ε hε
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (((q : ℝ) - 1) / δ + |D₀| * ((q : ℝ) - 1) + q + 2)
  refine ⟨N₁, fun n hn 𝒮 h𝒮 => ?_⟩
  have hnR : (N₁ : ℝ) ≤ n := by exact_mod_cast hn
  have hq1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    linarith
  have hqd : 0 ≤ ((q : ℝ) - 1) / δ := div_nonneg (by linarith) hδ.le
  have hD0 : 0 ≤ |D₀| * ((q : ℝ) - 1) := mul_nonneg (abs_nonneg _) (by linarith)
  have hnq : (q : ℝ) + 2 < n := by linarith
  have hnq' : q + 2 < n := by exact_mod_cast hnq
  -- two distinct points
  let v₀ : Fin n := ⟨0, by omega⟩
  let v₁ : Fin n := ⟨1, by omega⟩
  have h01 : v₁ ≠ v₀ := by simp [v₀, v₁, Fin.ext_iff]
  set a := deg 𝒮 {v₀} with ha_def
  have hqpos : 0 < (q - 1).choose (r - 1) := Nat.choose_pos (by omega)
  -- all points have degree `a`
  have hdeg : ∀ v : Fin n, deg 𝒮 {v} = a := by
    intro v
    have h1 := steiner_deg_point_mul h𝒮 (by omega) v
    have h2 := steiner_deg_point_mul h𝒮 (by omega) v₀
    exact Nat.eq_of_mul_eq_mul_left hqpos (h1.trans h2.symm)
  -- codegrees
  have hcod : ∀ u v : Fin n, u ≠ v → deg 𝒮 {u, v} * (n - 1) = a * (q - 1) := by
    intro u v huv
    rw [steiner_codeg_mul h𝒮 hr hrq.le huv, hdeg v]
  have hb1 : 1 ≤ deg 𝒮 {v₁, v₀} := by
    have := steiner_deg_pair_mul h𝒮 hr h01
    have hpos : 0 < (n - 2).choose (r - 2) := Nat.choose_pos (by omega)
    rcases Nat.eq_zero_or_pos (deg 𝒮 {v₁, v₀}) with h0 | h0
    · rw [h0, mul_zero] at this; omega
    · exact h0
  have hn1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n - 1 by omega)
  have hnc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hqc : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  -- `a (q - 1) ≥ n - 1`
  have haq : (n : ℝ) - 1 ≤ (a : ℝ) * ((q : ℝ) - 1) := by
    have := hcod v₁ v₀ h01
    have h' : ((deg 𝒮 {v₁, v₀} : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) = (a : ℝ) * ((q - 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [hnc, hqc] at h'
    have hb1' : (1 : ℝ) ≤ (deg 𝒮 {v₁, v₀} : ℝ) := by exact_mod_cast hb1
    nlinarith
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  obtain ⟨m, c, hm, hc⟩ := hP (Fin n) 𝒮 (a : ℝ) (by
      -- `D₀ ≤ a`
      by_contra hlt
      push_neg at hlt
      have h1 : (a : ℝ) * ((q : ℝ) - 1) < |D₀| * ((q : ℝ) - 1) :=
        mul_lt_mul_of_pos_right (lt_of_lt_of_le hlt (le_abs_self _)) (by linarith)
      linarith)
    h𝒮.card_eq
    (fun v => by rw [hdeg v]; constructor <;> nlinarith)
    (fun u v huv => by
      have := hcod u v huv
      have h' : ((deg 𝒮 {u, v} : ℕ) : ℝ) * ((n : ℝ) - 1) = (a : ℝ) * ((q : ℝ) - 1) := by
        rw [← hnc, ← hqc]; exact_mod_cast this
      have hqδ : (q : ℝ) - 1 ≤ δ * ((n : ℝ) - 1) := by
        have : ((q : ℝ) - 1) / δ ≤ (n : ℝ) - 1 := by linarith
        rwa [div_le_iff₀ hδ, mul_comm] at this
      have hn1' : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      have : ((deg 𝒮 {u, v} : ℕ) : ℝ) * ((n : ℝ) - 1) ≤ (δ * a) * ((n : ℝ) - 1) := by
        rw [h']; nlinarith
      exact le_of_mul_le_mul_right this hn1')
  refine ⟨m, c, ?_, hc⟩
  have hcast : (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) = a := by
    rw [div_eq_iff (by exact_mod_cast hqpos.ne'), ← steiner_deg_point_mul h𝒮 (by omega) v₀]
    push_cast; ring
  rw [hcast]; exact hm

/-- **At least `R` classes are needed**: blocks through a common point get distinct colours. -/
theorem resolution_classes_lower (hr : 1 ≤ r) (hrq : r ≤ q) {𝒮 : Finset (Finset (Fin n))}
    (h𝒮 : IsSteinerSystem q r 𝒮) (hn : 1 ≤ n) {m : ℕ} {c : Finset (Fin n) → Fin m}
    (hc : ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B') :
    (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ≤ m := by
  classical
  set v : Fin n := ⟨0, hn⟩
  have hR := steiner_deg_point_mul h𝒮 hr v
  have hqpos : 0 < (q - 1).choose (r - 1) := Nat.choose_pos (by omega)
  have hcast : (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ)
      = deg 𝒮 {v} := by
    rw [div_eq_iff (by exact_mod_cast hqpos.ne'), ← hR]; push_cast; ring
  rw [hcast]
  have hle : deg 𝒮 {v} ≤ m := by
    have := card_le_card_of_injOn (s := 𝒮.filter (fun B => {v} ⊆ B))
      (t := (univ : Finset (Fin m))) c (fun _ _ => mem_coe.2 (mem_univ _)) (by
        intro B hB B' hB' hcc
        by_contra hne
        rw [mem_coe, mem_filter] at hB hB'
        exact disjoint_left.1 (hc B hB.1 B' hB'.1 hne hcc) (singleton_subset_iff.1 hB.2)
          (singleton_subset_iff.1 hB'.2))
    simpa [deg] using this
  exact_mod_cast hle

/-- **Existence of asymptotically resolvable Steiner systems**: for `q > r ≥ 2`, `ε > 0` and
every large admissible `n` there is an `(n, q, r)`-Steiner system whose blocks split into at most
`(1 + ε)·binom(n-1, r-1)/binom(q-1, r-1)` partial parallel classes (assuming Pippenger–Spencer). -/
theorem exists_almost_resolvable_steiner (hPS : PippengerSpencer) (hr : 2 ≤ r) (hrq : r < q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, DesignDivisibility n q r 1 →
      ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem q r 𝒮 ∧
      ∃ (m : ℕ) (c : Finset (Fin n) → Fin m),
        (m : ℝ) ≤ (1 + ε) * (((n - 1).choose (r - 1) : ℕ) / ((q - 1).choose (r - 1) : ℕ) : ℝ) ∧
        ∀ B ∈ 𝒮, ∀ B' ∈ 𝒮, B ≠ B' → c B = c B' → Disjoint B B' := by
  obtain ⟨n₁, h1⟩ := steiner_almost_resolvable hPS hr hrq hε
  obtain ⟨n₂, h2⟩ := steiner_exists (by omega) hrq
  refine ⟨max n₁ n₂, fun n hn hdiv => ?_⟩
  obtain ⟨𝒮, h𝒮⟩ := h2 n (le_of_max_le_right hn) hdiv
  exact ⟨𝒮, h𝒮, h1 n (le_of_max_le_left hn) 𝒮 h𝒮⟩

end RefinedAbsorption.Extensions
