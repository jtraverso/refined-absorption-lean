module
public import RequestProject.RefineDown.Round

/-!
# Chaining placed rounds

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855.  Lean formalization: Juan Pablo
Traverso Gianini, Apache-2.0.

`IterSpec` is the invariant of a chain of placed rounds started at the copies `X` (tags `≤ k`):
a residual multi-refiner of `X` (the original copies are kept untouched) with residue in a simple
set `Y ⊆ R`, all new copies tagged in `(k, k + m]`, at most one copy of `X` per piece, and
`(r-1)`-degree budget `B` for the refiner and for the vertex sets of the pieces.

* `IterSpec.trans`: one more round (`RoundSpec`) on the residue composes with the chain, via
  `IsResidualMultiRefiner.trans`; budgets add.  The budget of the composition is the sum of the
  budgets of the rounds; this is the accounting the refine-down iteration uses.
* `sum_budget_le_of_halving`: if the budgets of consecutive rounds at least halve, the total
  budget is at most twice the first one, independently of the number of rounds.
* `placedRounds`: any fixed number `m + 1` of anti-edge rounds placed inside `Fin n`.  Here the
  residue does **not** shrink (each round replaces the residue by fake edges) and the budget is
  `C_m · D` with `C_m` depending on `m`; the decreasing rounds of the paper are not formalized.
-/

@[expose] public section

namespace RefinedAbsorption.RefineDown

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement

variable {n q r : ℕ}

/-- **The invariant of a chain of rounds.** -/
structure IterSpec (q r C : ℕ) {n : ℕ} (k m : ℕ) (X : Finset (Lab n))
    (G : Finset (Finset (Fin n))) (B : ℕ) (R Y : Finset (Lab n)) (𝒲 : Finset (Finset (Lab n))) :
    Prop where
  refiner : IsResidualMultiRefiner q r C labEnds X R Y 𝒲
  residue_sub : Y ⊆ R
  tag : ∀ c ∈ R, k < c.1 ∧ c.1 ≤ k + m
  residue_simple : Set.InjOn labEnds (Y : Set (Lab n))
  avoid : ∀ c ∈ R, c.2 ∉ G
  oneX : ∀ W ∈ 𝒲, (W.filter (· ∈ X)).card ≤ 1
  degR : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg labEnds R S ≤ B
  pieceDeg : ∀ S : Finset (Fin n), S.card = r - 1 →
    (𝒲.filter fun W => S ⊆ W.biUnion labEnds).card ≤ B

theorem RoundSpec.toIterSpec {C k D : ℕ} {X : Finset (Lab n)} {G : Finset (Finset (Fin n))}
    {R Y : Finset (Lab n)} {𝒲 : Finset (Finset (Lab n))} (h : RoundSpec q r C k X G D R Y 𝒲) :
    IterSpec q r C k 1 X G (C * D) R Y 𝒲 where
  refiner := h.refiner
  residue_sub := h.residue_sub
  tag c hc := by rw [h.tag c hc]; omega
  residue_simple := h.simple.mono (coe_subset.2 h.residue_sub)
  avoid := h.avoid
  oneX := h.oneX
  degR := h.degR
  pieceDeg := h.pieceDeg

theorem deg_image_le_mdeg {R : Finset (Lab n)} (S : Finset (Fin n)) :
    deg (R.image labEnds) S ≤ mdeg labEnds R S := by
  classical
  unfold deg mdeg
  rw [filter_image]
  exact card_image_le

/-- **One more round on the residue.**  The round is run on the residue `Y` (tags `≤ k + m`)
with a host containing `G`; budgets add. -/
theorem IterSpec.trans {C C₁ k m B D' : ℕ} {X : Finset (Lab n)} {G G' : Finset (Finset (Fin n))}
    {R Y R' Y' : Finset (Lab n)} {𝒲 𝒲' : Finset (Finset (Lab n))}
    (h : IterSpec q r C k m X G B R Y 𝒲) (h' : RoundSpec q r C₁ (k + m) Y G' D' R' Y' 𝒲')
    (hXk : ∀ c ∈ X, c.1 ≤ k) (hGG' : G ⊆ G') :
    IterSpec q r (C + C₁) k (m + 1) X G (B + C₁ * D') (R ∪ R') Y' (𝒲 ∪ 𝒲') := by
  have hYXR : Y ⊆ X ∪ R := h.residue_sub.trans subset_union_right
  have hdisj : Disjoint R' (X ∪ R) := by
    rw [disjoint_left]
    intro c hc hc'
    have := h'.tag c hc
    rcases mem_union.1 hc' with hc' | hc'
    · have := hXk c hc'; omega
    · have := (h.tag c hc').2; omega
  refine ⟨h.refiner.trans h'.refiner hYXR hdisj,
    h'.residue_sub.trans subset_union_right, ?_,
    h'.simple.mono (coe_subset.2 h'.residue_sub), ?_, ?_, ?_, ?_⟩
  · intro c hc
    rcases mem_union.1 hc with hc | hc
    · have := h.tag c hc; omega
    · have := h'.tag c hc; omega
  · intro c hc
    rcases mem_union.1 hc with hc | hc
    · exact h.avoid c hc
    · exact fun hG => h'.avoid c hc (hGG' hG)
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · exact h.oneX W hW
    · -- pieces of the new round only contain new copies and copies of `Y`
      have : W.filter (· ∈ X) = ∅ := by
        rw [filter_eq_empty_iff]
        intro c hcW hcX
        have hk := hXk c hcX
        rcases mem_union.1 (h'.refiner.subset W hW hcW) with hc | hc
        · have := (h.tag c (h.residue_sub hc)).1; omega
        · have := h'.tag c hc; omega
      rw [this]; exact Nat.zero_le _
  · intro S hS
    calc mdeg labEnds (R ∪ R') S ≤ mdeg labEnds R S + mdeg labEnds R' S := by
          unfold mdeg; rw [filter_union]; exact card_union_le _ _
      _ ≤ B + C₁ * D' := Nat.add_le_add (h.degR S hS) (h'.degR S hS)
  · intro S hS
    rw [filter_union]
    exact (card_union_le _ _).trans (Nat.add_le_add (h.pieceDeg S hS) (h'.pieceDeg S hS))

/-- **Budgets of halving rounds.**  If the budgets of consecutive rounds at least halve, the
accumulated budget of any number of rounds is at most twice the first budget. -/
theorem sum_budget_le_of_halving (b : ℕ → ℕ) (hb : ∀ j, 2 * b (j + 1) ≤ b j) (m : ℕ) :
    ∑ j ∈ range m, b j ≤ 2 * b 0 := by
  have key : ∀ m, ∑ j ∈ range m, b j + 2 * b m ≤ 2 * b 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      have := hb m
      omega
  exact le_trans (Nat.le_add_right _ _) (key m)

set_option maxHeartbeats 1000000 in
/-- **A fixed number of placed rounds.**  For `1 ≤ r < q` and every `m` there is `C ≥ 1` such
that `m + 1` anti-edge rounds can be chained inside `Fin n` on any labelled `r`-multigraph `X`
with tags `≤ k` and `Δ_{r-1}(X) ≤ D`, provided `C · D ≤ n` and `C · Δ_{r-1}(G) ≤ n`.  Every
round derives the conditions of the Partial Clique Embedding Lemma from the previous one, with the
edges created so far added to the forbidden host.  The constant depends on `m`. -/
theorem placedRounds {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) (m : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (n k : ℕ) (X : Finset (Lab n)) (G : Finset (Finset (Fin n))) (D : ℕ),
      (∀ c ∈ X, c.1 ≤ k) → MIsRGraph r labEnds X →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg labEnds X S ≤ D) →
      (∀ S : Finset (Fin n), S.card = r - 1 → C * deg G S ≤ n) → C * D ≤ n → 0 < n →
      ∃ (R Y : Finset (Lab n)) (𝒲 : Finset (Finset (Lab n))),
        IterSpec q r C k (m + 1) X G (C * D) R Y 𝒲 := by
  obtain ⟨C₁, hC₁, hround⟩ := placedRound hr hrq
  induction m with
  | zero =>
    refine ⟨C₁, hC₁, fun n k X G D hXk hXr hXD hG hD hn => ?_⟩
    obtain ⟨R, Y, 𝒲, h⟩ := hround n k X G D hXk hXr hXD hG hD hn
    exact ⟨R, Y, 𝒲, h.toIterSpec⟩
  | succ m ih =>
    obtain ⟨Cm, hCm, hm⟩ := ih
    refine ⟨4 * C₁ * (Cm + 1), by nlinarith, fun n k X G D hXk hXr hXD hG hD hn => ?_⟩
    have hle : Cm ≤ 4 * C₁ * (Cm + 1) := by nlinarith
    obtain ⟨R, Y, 𝒲, h⟩ := hm n k X G D hXk hXr hXD
      (fun S hS => le_trans (Nat.mul_le_mul_right _ hle) (hG S hS))
      (le_trans (Nat.mul_le_mul_right _ hle) hD) hn
    have hYk : ∀ c ∈ Y, c.1 ≤ k + (m + 1) := fun c hc => (h.tag c (h.residue_sub hc)).2
    have hYr : MIsRGraph r labEnds Y := fun c hc =>
      h.refiner.rgraph c (mem_union_right _ (h.residue_sub hc))
    have hYD : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg labEnds Y S ≤ Cm * D :=
      fun S hS => (mdeg_mono labEnds h.residue_sub S).trans (h.degR S hS)
    have hG' : ∀ S : Finset (Fin n), S.card = r - 1 →
        C₁ * deg (G ∪ R.image labEnds) S ≤ n := by
      intro S hS
      have h1 : deg (G ∪ R.image labEnds) S ≤ deg G S + Cm * D := by
        unfold deg
        rw [filter_union]
        refine (card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
        exact (deg_image_le_mdeg S).trans (h.degR S hS)
      have h2 : 2 * C₁ * deg G S ≤ n :=
        le_trans (Nat.mul_le_mul_right _ (by nlinarith)) (hG S hS)
      have h3 : 2 * C₁ * (Cm * D) ≤ n := by
        refine le_trans ?_ hD
        have : 2 * C₁ * (Cm * D) = (2 * C₁ * Cm) * D := by ring
        rw [this]; exact Nat.mul_le_mul_right _ (by nlinarith)
      calc C₁ * deg (G ∪ R.image labEnds) S ≤ C₁ * (deg G S + Cm * D) :=
            Nat.mul_le_mul_left _ h1
        _ ≤ n := by nlinarith
    have hD' : C₁ * (Cm * D) ≤ n := by
      refine le_trans ?_ hD
      have : C₁ * (Cm * D) = (C₁ * Cm) * D := by ring
      rw [this]; exact Nat.mul_le_mul_right _ (by nlinarith)
    obtain ⟨R', Y', 𝒲', h'⟩ := hround n (k + (m + 1)) Y (G ∪ R.image labEnds) (Cm * D)
      hYk hYr hYD hG' hD' hn
    have hc := h.trans h' hXk subset_union_left
    refine ⟨R ∪ R', Y', 𝒲 ∪ 𝒲', ?_⟩
    have hCle : Cm + C₁ ≤ 4 * C₁ * (Cm + 1) := by nlinarith
    have hBle : Cm * D + C₁ * (Cm * D) ≤ 4 * C₁ * (Cm + 1) * D := by
      have : Cm * D + C₁ * (Cm * D) = (Cm + C₁ * Cm) * D := by ring
      rw [this]; exact Nat.mul_le_mul_right _ (by nlinarith)
    exact { hc with
      refiner := hc.refiner.mono hCle
      degR := fun S hS => (hc.degR S hS).trans hBle
      pieceDeg := fun S hS => (hc.pieceDeg S hS).trans hBle }

end RefinedAbsorption.RefineDown
