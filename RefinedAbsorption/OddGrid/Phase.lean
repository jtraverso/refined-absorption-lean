module
public import RefinedAbsorption.OddGrid.Halve

/-!
# Repeated halving

`phase G` halves the columns of `G` until fewer than `5` remain.  `phase_spec`: the resulting plan
segment is valid on rook pairs of `G`, lands in rook pairs of the final grid, has at most
`2 ⌈log₂ C⌉` stages, and its load at every vertex is at most `(#stages) (25 (R + C) + 1)`.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset Classical

variable {n : ℕ}

namespace Grid

/-- Halve the columns until fewer than `5` remain. -/
noncomputable def phase (G : Grid n) : List (Spec n) × Grid n :=
  if 5 ≤ G.C then
    (G.hSeg ++ (phase G.colHalve).1, (phase G.colHalve).2)
  else ([], G)
termination_by G.C
decreasing_by simp only [colHalve]; omega

lemma hSeg_length (G : Grid n) : G.hSeg.length = 2 := rfl

theorem phase_spec : ∀ (G : Grid n), G.Full → 2 ≤ G.R →
    (phase G).2.Full ∧ (phase G).2.R = G.R ∧ (phase G).2.C < 5 ∧ (phase G).2.C ≤ G.C ∧
    min G.C 3 ≤ (phase G).2.C ∧ (phase G).1.length ≤ 2 * Nat.clog 2 G.C ∧
    ∀ P : Finset (Finset (Fin n)), (∀ e ∈ P, G.Rook e) →
      SegOK (phase G).1 P ∧ (∀ e ∈ prun (phase G).1 P (phase G).1.length, (phase G).2.Rook e) ∧
      ∀ v, passSum (phase G).1 P v ≤ (phase G).1.length * (25 * (G.R + G.C) + 1) := by
  intro G
  induction hc : G.C using Nat.strong_induction_on generalizing G with
  | _ c ih =>
  subst hc
  intro hF hR
  by_cases hC : 5 ≤ G.C
  · have hlt : G.colHalve.C < G.C := by simp only [colHalve]; omega
    obtain ⟨iF, iR, iC, iC', imin, ilen, iP⟩ :=
      ih _ hlt G.colHalve rfl (full_colHalve hF) (by simpa [colHalve] using hR)
    have hRe : G.colHalve.R = G.R := rfl
    have hCe : G.colHalve.C = (G.C + 1) / 2 := rfl
    rw [phase, if_pos hC]
    simp only
    refine ⟨iF, iR, iC, by omega, by omega, ?_, fun P hP => ?_⟩
    · rw [List.length_append, hSeg_length]
      have h2 := Nat.clog_of_two_le (b := 2) (n := G.C) (by norm_num) (by omega)
      rw [hCe] at ilen
      have : (G.C + 2 - 1) / 2 = (G.C + 1) / 2 := by omega
      rw [this] at h2
      omega
    · obtain ⟨hs, hout, hload⟩ := halve_seg hF hR hC hP
      obtain ⟨is, iout, iload⟩ := iP _ hout
      refine ⟨hs.append is, ?_, fun v => ?_⟩
      · intro e he
        rw [prun_append_length] at he
        exact iout e he
      · rw [passSum_append]
        have h1 := hload v
        have h2 := iload v
        rw [hRe, hCe] at h2
        have h3 : (phase G.colHalve).1.length * (25 * (G.R + (G.C + 1) / 2) + 1) ≤
            (phase G.colHalve).1.length * (25 * (G.R + G.C) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        rw [List.length_append, hSeg_length, Nat.add_mul]
        have h4 := h2.trans h3
        have h5 : 25 * (G.R + G.C) + 1 ≤ 2 * (25 * (G.R + G.C) + 1) := by omega
        exact add_le_add (h1.trans h5) h4
  · rw [phase, if_neg hC]
    dsimp only
    refine ⟨hF, rfl, by omega, le_rfl, min_le_left _ _, by simp, fun P hP => ?_⟩
    refine ⟨SegOK.nil P, fun e he => hP e (by simpa [prun] using he), fun v => ?_⟩
    simp [passSum]

end Grid

end RefinedAbsorption.OddGrid
