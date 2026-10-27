module
public import RefinedAbsorption.LinkSpread.LevelOneIter

/-!
# Tagged link refiners at level `1`

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

* **`taggedLinkRefinersE_one`**: `TaggedLinkRefinersE q r 1`, given the placed link levels
  `1 + j` for `j ≥ 1` (for `r = 3` only the last level, which is proved).
* **`steinerExistenceFor_three_unconditional`**: Steiner systems `S(n, q, 3)` exist for all
  large admissible `n`.
* **`steinerExistence_of_tagged_two`**: the Existence Conjecture from tagged link refiners at the
  levels `2 ≤ i < r - 1` only.
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown

/-- Distinct single-vertex tags lying in `U` are at most `|U|` many. -/
theorem card_image_tg_le {n : ℕ} {E : Type} {tg : E → Finset (Fin n)} {X : Finset E}
    {U : Finset (Fin n)} (htgc : ∀ x ∈ X, (tg x).card = 1) (hU : ∀ x ∈ X, tg x ⊆ U) :
    (X.image tg).card ≤ U.card := by
  have hsub : X.image tg ⊆ U.powersetCard 1 := by
    intro T hT
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hT
    exact mem_powersetCard.2 ⟨hU x hx, htgc x hx⟩
  simpa using card_le_card hsub

set_option maxHeartbeats 4000000 in
/-- **Staged tagged refiners at level `1`**: the additive term is `B' · |Z| / 2^t` for every
precision `t`, with the refinedness `C` and `B'` uniform in `t`.  Induction on `t`: one stage of
each of the four classes of tags at a high precision into its own quarter of `Z`, then precision
`t` on the residues, whose lifted degrees are bounded by the stage budget. -/
theorem taggedStaged {q r : ℕ} (hr : 2 < r) (hrq : r < q)
    (hL : ∀ j, 1 ≤ j → 1 + j < r → PlacedLinkLevelE q r (1 + j)) (K : ℕ) :
    ∃ C B' : ℕ, ∀ t : ℕ, ∃ Ct : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E]
      (tg bd : E → Finset (Fin n)) (Zc : Finset (Fin n)) (X : Finset E) (D : ℕ),
      (∀ x, Disjoint (tg x) Zc) → (∀ x, bd x ⊆ Zc) → (∀ x ∈ X, (tg x).card = 1) →
      (∀ x ∈ X, (bd x).card = r - 1) → (X.image tg).card ≤ K * Zc.card + K + 1 → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) →
      ∃ Bd : ℕ, 2 ^ t * Bd ≤ 2 ^ t * Ct * D + B' * Zc.card ∧
        TRefOut q r 1 C tg bd Zc X (fun _ => Bd) := by
  obtain ⟨Cr, B, M, hM, hst⟩ := taggedStage (i := 1) (by omega) hrq hL (K + 6)
  obtain ⟨Cd, A, A', hdense⟩ := taggedDense hr hrq hL K
  set B' := A' + B with hB'
  refine ⟨Cr + Cd, B', fun t => ?_⟩
  induction t with
  | zero =>
    refine ⟨A, fun n E _ tg bd Zc X D htg hbd htgc hbdc hTs hD1 hdeg => ⟨_, ?_,
      (hdense n tg bd Zc X D htg hbd htgc hbdc hTs hD1 hdeg).mono (by omega) fun _ _ => le_rfl⟩⟩
    simp only [pow_zero, one_mul]
    have : A' * Zc.card ≤ B' * Zc.card := Nat.mul_le_mul_right _ (by omega)
    omega
  | succ t ih =>
    obtain ⟨Ct, hCt⟩ := ih
    set s := t + 1 + (Ct + 4) with hs
    obtain ⟨Cs, Cst, hst0⟩ := hst s
    set m₀ := 4 * (Cs + q + r + K + 4) + 4 with hm₀
    refine ⟨2 * 2 ^ s * Cst + Ct + A + A' * m₀, ?_⟩
    intro n E _ tg bd Zc X D htg hbd htgc hbdc hTs hD1 hdeg
    have hpowpos : 1 ≤ 2 ^ (t + 1) := Nat.one_le_two_pow
    by_cases hsmall : Zc.card ≤ m₀
    · refine ⟨_, ?_, (hdense n tg bd Zc X D htg hbd htgc hbdc hTs hD1 hdeg).mono (by omega)
        fun _ _ => le_rfl⟩
      have h1 : A' * Zc.card ≤ A' * m₀ := Nat.mul_le_mul_left _ hsmall
      have h2 : A' * m₀ ≤ A' * m₀ * D := Nat.le_mul_of_pos_right _ hD1
      have h3 : A * D + A' * Zc.card ≤ (2 * 2 ^ s * Cst + Ct + A + A' * m₀) * D := by
        have e : (2 * 2 ^ s * Cst + Ct + A + A' * m₀) * D =
            2 * 2 ^ s * Cst * D + Ct * D + A * D + A' * m₀ * D := by ring
        rw [e]; omega
      calc 2 ^ (t + 1) * (A * D + A' * Zc.card)
          ≤ 2 ^ (t + 1) * ((2 * 2 ^ s * Cst + Ct + A + A' * m₀) * D) :=
            Nat.mul_le_mul_left _ h3
        _ = 2 ^ (t + 1) * (2 * 2 ^ s * Cst + Ct + A + A' * m₀) * D := by ring
        _ ≤ _ := Nat.le_add_right _ _
    · set mq := Zc.card / 4 with hmq
      have hmq0 : Cs + q + r + K + 4 ≤ mq := by omega
      have h4 : 4 * mq ≤ Zc.card := by omega
      set X₁ := 2 ^ s * Cst * D + B * mq with hX₁
      have hpow : 2 ^ (t + 1) * (4 + Ct) ≤ 2 ^ s := by
        have := Nat.lt_two_pow_self (n := Ct + 4)
        have e : 2 ^ s = 2 ^ (t + 1) * 2 ^ (Ct + 4) := by rw [hs, pow_add]
        rw [e]
        exact Nat.mul_le_mul_left _ (by omega)
      have hclass : ∀ (p : Finset (Fin n) → Prop) [DecidablePred p] (Q : Finset (Fin n)),
          Q ⊆ Zc → Q.card = Zc.card / 4 →
          ((X.filter fun x => p (tg x)).image tg).card ≤ K * Q.card + K + 1 →
          ∃ b₁ b₂, (2 ^ (t + 1) * (4 + Ct) * b₁ ≤ X₁ ∧
              2 ^ (t + 1) * b₂ ≤ 2 ^ (t + 1) * Ct * D + X₁ + 2 * (B' * mq)) ∧
            TRefOut q r 1 (Cr + Cd) tg bd Zc (X.filter fun x => p (tg x))
              (fun S => b₁ + if (S ∩ Zc).Nonempty ∧ S ∩ Zc ⊆ Q then b₂ else 0) := by
        intro p _ Q hQ hQc hKQ
        have hX'X : (X.filter fun x => p (tg x)) ⊆ X := filter_subset _ _
        have hUc : ((((X.filter fun x => p (tg x)).image tg).biUnion id) ∪ Zc).card ≤
            (K + 6) * Q.card := by
          have h1 := card_union_le (((X.filter fun x => p (tg x)).image tg).biUnion id) Zc
          have h2 := card_tagVerts_le (fun x hx => htgc x (hX'X hx))
          have e : (K + 6) * Q.card = K * Q.card + 6 * Q.card := by ring
          rw [hQc] at hKQ e ⊢
          omega
        obtain ⟨Bd₁, hBd₁, hso⟩ := hst0 n tg bd Zc Q _ (X.filter fun x => p (tg x)) D hQ htg hbd
          (fun x hx => htgc x (hX'X hx)) (fun x hx => hbdc x (hX'X hx)) subset_union_right
          (fun x hx => union_subset_union (subset_tagVerts hx) (hbd x)) hUc (by omega) hD1
          (by omega) (fun S hS => (mdeg_mono _ hX'X S).trans (hdeg S hS))
        rw [hQc] at hBd₁
        have hB1 : 2 ^ (t + 1) * (4 + Ct) * Bd₁ ≤ X₁ :=
          (Nat.mul_le_mul_right _ hpow).trans hBd₁
        obtain ⟨Bd₂, hBd₂, hres⟩ := TStageOut.prepend (C := Cr + Cd) (by omega) (by omega)
          hQ htg (fun x hx => htgc x (hX'X hx))
          (fun Bd₂ => 2 ^ t * Bd₂ ≤ 2 ^ t * Ct * (D + Bd₁) + B' * mq) hso
          (fun E₁ _ tg₁ bd₁ X₁' h1 h2 h3 h4' h5 _ h7 => by
            have hT1 : (X₁'.image tg₁).card ≤ K * Q.card + K + 1 := (card_le_card h5).trans hKQ
            obtain ⟨Bd₂, hBd₂, hout⟩ := hCt n tg₁ bd₁ Q X₁' (D + Bd₁)
              (fun x => disjoint_of_subset_right hQ (h1 x)) h2 h3 h4' hT1 (by omega)
              (fun S hS => (h7 S hS).trans (Nat.le_add_left _ _))
            exact ⟨Bd₂, by rw [hQc] at hBd₂; exact hBd₂, hout⟩)
        refine ⟨Bd₁, Bd₂, ⟨hB1, ?_⟩, hres⟩
        have e1 : 2 ^ (t + 1) * Bd₂ = 2 * (2 ^ t * Bd₂) := by ring
        have e2 : 2 * (2 ^ t * Ct * (D + Bd₁) + B' * mq) =
            2 ^ (t + 1) * Ct * D + 2 ^ (t + 1) * Ct * Bd₁ + 2 * (B' * mq) := by ring
        have e3 : 2 ^ (t + 1) * (4 + Ct) * Bd₁ =
            4 * (2 ^ (t + 1) * Bd₁) + 2 ^ (t + 1) * Ct * Bd₁ := by ring
        omega
      obtain ⟨b₁, b₂, hP, hout⟩ := classStep (q := q) (r := r) (i := 1) (C := Cr + Cd) hTs
        (fun b₁ b₂ => 2 ^ (t + 1) * (4 + Ct) * b₁ ≤ X₁ ∧
          2 ^ (t + 1) * b₂ ≤ 2 ^ (t + 1) * Ct * D + X₁ + 2 * (B' * mq)) hclass
      refine ⟨_, ?_, hout⟩
      have hs1 : 4 * (2 ^ (t + 1) * ∑ j, b₁ j) ≤ 4 * X₁ := by
        rw [mul_sum, mul_sum]
        calc ∑ j, 4 * (2 ^ (t + 1) * b₁ j) ≤ ∑ _j : Fin 4, X₁ := sum_le_sum fun j _ => by
              have := (hP j).1
              have e : 2 ^ (t + 1) * (4 + Ct) * b₁ j =
                  4 * (2 ^ (t + 1) * b₁ j) + 2 ^ (t + 1) * Ct * b₁ j := by ring
              omega
          _ = 4 * X₁ := by simp
      have hs2 : 2 ^ (t + 1) * univ.sup b₂ ≤ 2 ^ (t + 1) * Ct * D + X₁ + 2 * (B' * mq) := by
        obtain ⟨j, -, hj⟩ := exists_mem_eq_sup (univ : Finset (Fin 4)) univ_nonempty b₂
        rw [hj]; exact (hP j).2
      have hBB : B * mq ≤ B' * mq := Nat.mul_le_mul_right _ (by omega)
      have hBZ : 4 * (B' * mq) ≤ B' * Zc.card := by
        calc 4 * (B' * mq) = B' * (4 * mq) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ h4
      have e5 : 2 ^ (t + 1) * (∑ j, b₁ j + univ.sup b₂) =
          2 ^ (t + 1) * ∑ j, b₁ j + 2 ^ (t + 1) * univ.sup b₂ := by ring
      have e6 : 2 ^ (t + 1) * (2 * 2 ^ s * Cst + Ct + A + A' * m₀) * D =
          2 ^ (t + 1) * (2 * (2 ^ s * Cst * D)) + 2 ^ (t + 1) * Ct * D +
            2 ^ (t + 1) * ((A + A' * m₀) * D) := by ring
      have h7 : 2 * (2 ^ s * Cst * D) ≤ 2 ^ (t + 1) * (2 * (2 ^ s * Cst * D)) :=
        Nat.le_mul_of_pos_left _ hpowpos
      rw [e5, e6]
      omega

/-- **Tagged link refiners at level `1`.** -/
theorem taggedLinkRefinersE_one {q r : ℕ} (hr : 2 < r) (hrq : r < q)
    (hL : ∀ j, 1 ≤ j → 1 + j < r → PlacedLinkLevelE q r (1 + j)) :
    TaggedLinkRefinersE q r 1 := by
  intro K
  obtain ⟨C, B', h⟩ := taggedStaged hr hrq hL K
  refine ⟨3 * C, B', fun s => ?_⟩
  obtain ⟨Ct, hCt⟩ := h s
  refine ⟨0, Ct, ?_⟩
  intro n E _ tg bd Z U X D htg hbd htgc hbdc hU hUK _ hD1 _ hdeg
  have h1 := card_image_tg_le htgc fun x hx =>
    (subset_union_left : tg x ⊆ liftEnds tg bd x).trans (hU x hx)
  obtain ⟨Bd, hBd, hout⟩ := hCt n tg bd Z X D htg hbd htgc hbdc (by omega) hD1 hdeg
  exact ⟨Bd, hBd, hout.toTaggedRefOutE⟩

/-- **Steiner systems with `r = 3`** exist for every `q > 3` and all large admissible `n`. -/
theorem steinerExistenceFor_three_unconditional {q : ℕ} (hq : 3 < q) :
    RefinedAbsorption.Dense.SteinerExistenceFor q 3 := by
  refine steinerExistenceFor_three_of_tagged hq (taggedLinkRefinersE_one (by norm_num) hq ?_)
  intro j hj hj3
  obtain rfl : j = 1 := by omega
  exact (placedLinkLevel_last q 3 (by norm_num) hq).toE

/-- **The Existence Conjecture** from tagged link refiners at the levels `2 ≤ i < r - 1` (level
`1` is `taggedLinkRefinersE_one`, the last level is proved). -/
theorem steinerExistence_of_tagged_two
    (h : ∀ q r i : ℕ, 3 ≤ r → r < q → 2 ≤ i → i < r - 1 → TaggedLinkRefinersE q r i) :
    SteinerExistenceConjecture := by
  have hP : ∀ q r i : ℕ, 3 ≤ r → r < q → 2 ≤ i → i < r - 1 → PlacedLinkLevelE q r i :=
    fun q r i hr hrq hi hir => placedLinkLevelE_of_tagged (h q r i hr hrq hi hir)
  refine steinerExistence_of_tagged fun q r i hr hrq hi hir => ?_
  rcases Nat.lt_or_ge i 2 with hi2 | hi2
  · obtain rfl : i = 1 := by omega
    refine taggedLinkRefinersE_one (by omega) hrq fun j hj hjr => ?_
    rcases Nat.lt_or_ge (1 + j) (r - 1) with h' | h'
    · exact hP q r (1 + j) hr hrq (by omega) h'
    · obtain h'' : 1 + j = r - 1 := by omega
      rw [h'']
      exact (placedLinkLevel_last q r (by omega) hrq).toE
  · exact h q r i hr hrq hi2 hir

end RefinedAbsorption.LinkSpread
