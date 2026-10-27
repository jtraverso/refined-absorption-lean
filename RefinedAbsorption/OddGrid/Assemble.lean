module
public import RefinedAbsorption.OddGrid.XStage

/-!
# The complete plan on a grid

`grid_plan`: for a full grid `G` with `R ≥ 2` rows and `C ≥ 5` columns, extended by one column to a
grid `Gb` containing every vertex, every graph `X` with maximum degree `≤ D` has a valid plan whose
final pair set has at most `256` pairs and whose total load at every vertex is at most
`gridBudget D G.R G.C Gb.R Gb.C = O(D + (R + C) log (R + C))`.

The plan: the first stage (`xstage`) routes `X` into rook pairs of `Gb`; `extra_seg` empties the
extra column; `phase` halves the columns until fewer than `5` remain; `phase` on the swapped grid
halves the rows.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset Classical

variable {n : ℕ}

/-- The load bound of the grid plan. -/
def gridBudget (D R C Rb Cb : ℕ) : ℕ :=
  D + (4 * D + 4) + (25 * (Rb + Cb) + 1) + 2 * Nat.clog 2 C * (25 * (R + C) + 1) +
    2 * Nat.clog 2 R * (25 * (4 + R) + 1)

namespace Grid

variable {G Gb : Grid n}

lemma exists_kappa (hx : ExtraOK G Gb) (hall : ∀ v, Gb.act v) {X : Finset (Finset (Fin n))}
    (hX2 : ∀ e ∈ X, e.card = 2) {D : ℕ} (hD : ∀ v, (X.filter (v ∈ ·)).card ≤ D)
    (hC : 5 ≤ G.C) (hbC : Gb.C ≤ G.C + 1) :
    ∃ κ : Finset (Fin n) → ℕ, (∀ e ∈ X, κ e < G.C ∧ κ e ∉ G.colsOf e) ∧
      ∀ ρ x, (X.filter (fun e => ρ ∈ G.rowsOf e ∧ κ e = x)).card ≤ 4 * D + 4 := by
  have hrow : ∀ ρ, (X.filter (fun e => ρ ∈ G.rowsOf e)).card ≤ Gb.C * D := by
    intro ρ
    set W := univ.filter (fun v => (G.co v).1 = ρ)
    have hW : W.card ≤ Gb.C := by
      calc _ ≤ (range Gb.C).card := by
            apply card_le_card_of_injOn (fun w => (G.co w).2)
            · intro w _
              have := (Gb.bdd w (hall w)).2
              rw [hx.co] at this
              simpa using this
            · intro w hw w' hw' h
              simp only [W, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw hw'
              exact gb_inj hx (hall w) (hall w') (Prod.ext (hw.trans hw'.symm) h)
        _ = Gb.C := card_range _
    calc _ ≤ (X.filter (fun e => ∃ x ∈ W, x ∈ e)).card := by
          apply card_le_card
          intro e he
          obtain ⟨heX, hρ⟩ := mem_filter.1 he
          obtain ⟨v, hv, hvρ⟩ := mem_image.1 hρ
          exact mem_filter.2 ⟨heX, v, by simp [W, hvρ], hv⟩
      _ ≤ W.card * D := card_filter_meet_le X W hD
      _ ≤ Gb.C * D := Nat.mul_le_mul_right _ hW
  have hm : Gb.C * D / (4 * D + 4) * 4 ≤ Gb.C := by
    have h1 := Nat.div_mul_le_self (Gb.C * D) (4 * D + 4)
    set m := Gb.C * D / (4 * D + 4)
    by_contra hcon
    push_neg at hcon
    nlinarith
  obtain ⟨κ, h1, h2⟩ := greedy_color G.rowsOf G.colsOf (C := G.C) (L := 4 * D + 4)
    (Δ := Gb.C * D) (by omega) (by omega) X
    (fun e he => by rw [← hX2 e he]; exact card_image_le)
    (fun e he => by rw [← hX2 e he]; exact card_image_le) hrow
  exact ⟨κ, h1, h2⟩

/-- The complete plan. -/
noncomputable def gplan (κ : Finset (Fin n) → ℕ) (G Gb : Grid n) : List (Spec n) :=
  [G.xSpec0 κ] ++ (G.xSeg Gb ++ (G.phase.1 ++ G.phase.2.swap.phase.1))

/-- **The plan on a grid.** -/
theorem grid_plan (hF : G.Full) (hR : 2 ≤ G.R) (hC : 5 ≤ G.C) (hx : ExtraOK G Gb)
    (hall : ∀ v, Gb.act v) (hbC : Gb.C ≤ G.C + 1) {X : Finset (Finset (Fin n))}
    (hX2 : ∀ e ∈ X, e.card = 2) {D : ℕ} (hD : ∀ v, (X.filter (v ∈ ·)).card ≤ D) :
    ∃ sp : List (Spec n), PlanOK sp X ∧ 1 ≤ sp.length ∧ (prun sp X sp.length).card ≤ 256 ∧
      ∀ v, ∑ t ∈ range sp.length, pass sp X t v ≤ gridBudget D G.R G.C Gb.R Gb.C := by
  obtain ⟨κ, hκ, hL⟩ := exists_kappa hx hall hX2 hD hC hbC
  obtain ⟨xs, xout, xmv, xload⟩ := xstage hF hx hall hX2 hD hκ hL
  obtain ⟨es, eout, eload⟩ := extra_seg hF hR (by omega) hx xout
  obtain ⟨F1, R1, C1, -, min1, len1, P1⟩ := phase_spec G hF hR
  obtain ⟨s1, out1, load1⟩ := P1 _ eout
  set G1 := G.phase.2
  have hF1s : G1.swap.Full := G1.full_swap F1
  have hR1s : 2 ≤ G1.swap.R := by
    show 2 ≤ G1.C
    have : min G.C 3 = 3 := by omega
    omega
  obtain ⟨F2, R2, C2, -, -, len2, P2⟩ := phase_spec G1.swap hF1s hR1s
  have out1' : ∀ e ∈ prun G.phase.1 _ G.phase.1.length, G1.swap.Rook e :=
    fun e he => (G1.rook_swap).2 (out1 e he)
  obtain ⟨s2, out2, load2⟩ := P2 _ out1'
  refine ⟨gplan κ G Gb, ?_, ?_, ?_, ?_⟩
  · apply planOK_of_segOK hX2 (xs.append (es.append (s1.append s2)))
    intro e he
    rw [rt_append_lt _ _ _ (by simp)]
    exact xmv e he
  · simp [gplan]
  · unfold gplan
    rw [prun_append_length, prun_append_length, prun_append_length]
    set G2 := G1.swap.phase.2
    have hcard := G2.card_le (P := prun _ _ _) out2
    have hR2 : G2.R < 5 := by rw [R2]; exact C1
    have h16 : G2.R * G2.C ≤ 16 := by
      have := Nat.mul_le_mul (show G2.R ≤ 4 by omega) (show G2.C ≤ 4 by omega)
      omega
    calc _ ≤ (G2.R * G2.C) ^ 2 := hcard
      _ ≤ 16 ^ 2 := Nat.pow_le_pow_left h16 2
      _ = 256 := by norm_num
  · intro v
    change passSum (gplan κ G Gb) X v ≤ _
    unfold gplan
    rw [passSum_append, passSum_append, passSum_append]
    have a1 := xload v
    have a2 := eload v
    have a3 := load1 v
    have a4 := load2 v
    have hRs : G1.swap.R = G1.C := rfl
    have hCs : G1.swap.C = G.R := by show G1.R = G.R; exact R1
    rw [hRs, hCs] at a4
    rw [hCs] at len2
    have b3 : G.phase.1.length * (25 * (G.R + G.C) + 1) ≤
        2 * Nat.clog 2 G.C * (25 * (G.R + G.C) + 1) := Nat.mul_le_mul_right _ len1
    have b4 : G1.swap.phase.1.length * (25 * (G1.C + G.R) + 1) ≤
        2 * Nat.clog 2 G.R * (25 * (4 + G.R) + 1) :=
      Nat.mul_le_mul len2 (by omega)
    unfold gridBudget
    linarith

end Grid

end RefinedAbsorption.OddGrid
