module
public import RequestProject.LinkSpread.LevelOne

/-!
# Iterating tagged stages at level `1`

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

* **`taggedDense`**: complete tagged refiners of all fibres at once inside the reserve `Z`, with
  lifted degrees `≤ A · D + A' · |Z|`, when the tags are single vertices and there are at most
  `K |Z| + K + 1` of them.  Strong induction on `|Z|`: split the tags into four classes, run a
  stage of each class into its own quarter of `Z`, and recurse on the residues.
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown

/-- The vertices of the tags of a class, and the bound on their number for tags of size one. -/
theorem card_tagVerts_le {n : ℕ} {E : Type} {tg : E → Finset (Fin n)} {X : Finset E}
    (htgc : ∀ x ∈ X, (tg x).card = 1) : ((X.image tg).biUnion id).card ≤ (X.image tg).card := by
  refine card_biUnion_le.trans (le_of_eq ?_)
  rw [card_eq_sum_ones]
  refine sum_congr rfl fun T hT => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hT
  exact htgc x hx

theorem subset_tagVerts {n : ℕ} {E : Type} {tg : E → Finset (Fin n)} {X : Finset E} {x : E}
    (hx : x ∈ X) : tg x ⊆ (X.image tg).biUnion id :=
  subset_biUnion_of_mem id (mem_image_of_mem tg hx)

set_option maxHeartbeats 4000000 in
/-- **Dense tagged refiners at level `1`.** -/
theorem taggedDense {q r : ℕ} (hr : 2 < r) (hrq : r < q)
    (hL : ∀ j, 1 ≤ j → 1 + j < r → PlacedLinkLevelE q r (1 + j)) (K : ℕ) :
    ∃ C A A' : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (tg bd : E → Finset (Fin n))
      (Zc : Finset (Fin n)) (X : Finset E) (D : ℕ),
      (∀ x, Disjoint (tg x) Zc) → (∀ x, bd x ⊆ Zc) → (∀ x ∈ X, (tg x).card = 1) →
      (∀ x ∈ X, (bd x).card = r - 1) → (X.image tg).card ≤ K * Zc.card + K + 1 → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) →
      TRefOut q r 1 C tg bd Zc X (fun _ => A * D + A' * Zc.card) := by
  obtain ⟨Cr, B, M, hM, hst⟩ := taggedStage (i := 1) (by omega) hrq hL (K + 6)
  obtain ⟨Cs, Cst, hst0⟩ := hst 0
  set m₀ := 4 * (Cs + q + r + K + 4) + 4 with hm₀
  obtain ⟨Cb, Ab, hbase⟩ := taggedBase q r 1 (by omega) hrq m₀
  set A := 4 * Cst + Ab * (K + 2) with hA
  set A' := 4 * B + A * M * (K + 2) + Ab * K with hA'
  refine ⟨Cr + Cb, A, A', fun n => ?_⟩
  suffices key : ∀ m, ∀ {E : Type} [DecidableEq E] (tg bd : E → Finset (Fin n))
      (Zc : Finset (Fin n)) (X : Finset E) (D : ℕ), Zc.card = m →
      (∀ x, Disjoint (tg x) Zc) → (∀ x, bd x ⊆ Zc) → (∀ x ∈ X, (tg x).card = 1) →
      (∀ x ∈ X, (bd x).card = r - 1) → (X.image tg).card ≤ K * Zc.card + K + 1 → 1 ≤ D →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) →
      TRefOut q r 1 (Cr + Cb) tg bd Zc X (fun _ => A * D + A' * Zc.card) from
    fun E _ tg bd Zc X D => key _ tg bd Zc X D rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro E _ tg bd Zc X D hZm htg hbd htgc hbdc hTs hD1 hdeg
  by_cases hsmall : Zc.card ≤ m₀
  · refine (hbase n tg bd Zc X D hbd htgc hbdc hsmall hdeg).mono (by omega) fun S _ => ?_
    have h1 : Ab * (X.image tg).card ≤ Ab * (K * Zc.card + K + 1) := Nat.mul_le_mul_left _ hTs
    have h2 : Ab * (K + 1) ≤ Ab * (K + 1) * D := Nat.le_mul_of_pos_right _ hD1
    have e1 : Ab * (K * Zc.card + K + 1) = Ab * K * Zc.card + Ab * (K + 1) := by ring
    have e2 : A * D = 4 * Cst * D + Ab * (K + 1) * D + Ab * D := by rw [hA]; ring
    have e3 : A' * Zc.card = 4 * B * Zc.card + A * M * (K + 2) * Zc.card + Ab * K * Zc.card := by
      rw [hA']; ring
    show Ab * D + Ab * (X.image tg).card ≤ A * D + A' * Zc.card
    omega
  · set mq := Zc.card / 4 with hmq
    have hmq0 : Cs + q + r + K + 4 ≤ mq := by omega
    have h4 : 4 * mq ≤ Zc.card := by omega
    have hclass : ∀ (p : Finset (Fin n) → Prop) [DecidablePred p] (Q : Finset (Fin n)),
        Q ⊆ Zc → Q.card = Zc.card / 4 →
        ((X.filter fun x => p (tg x)).image tg).card ≤ K * Q.card + K + 1 →
        ∃ b₁ b₂, (b₁ ≤ Cst * D + B * mq ∧ b₂ ≤ A * (M * (K + 2) * mq) + A' * mq) ∧
          TRefOut q r 1 (Cr + Cb) tg bd Zc (X.filter fun x => p (tg x))
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
      simp only [pow_zero, one_mul] at hBd₁
      obtain ⟨Bd₂, hBd₂, hres⟩ := TStageOut.prepend (C := Cr + Cb) (by omega) (by omega)
        hQ htg (fun x hx => htgc x (hX'X hx))
        (fun Bd₂ => Bd₂ ≤ A * (M * (K + 2) * mq) + A' * mq) hso
        (fun E₁ _ tg₁ bd₁ X₁ h1 h2 h3 h4' h5 h6 _ => by
          have hT1 : (X₁.image tg₁).card ≤ K * Q.card + K + 1 := (card_le_card h5).trans hKQ
          have hdeg₁ : ∀ S : Finset (Fin n), S.card = r - 1 →
              mdeg (liftEnds tg₁ bd₁) X₁ S ≤ M * (K + 2) * mq := by
            intro S hS
            refine (residue_deg_one (fun x => disjoint_of_subset_right hQ (h1 x)) h2 h3 h4'
              h6 S hS hr).trans ?_
            have hQm : Q.card = mq := hQc
            rw [hQm] at hT1 ⊢
            have e : (K + 2) * mq = K * mq + 2 * mq := by ring
            calc M * (mq + _) ≤ M * ((K + 2) * mq) := Nat.mul_le_mul_left _ (by omega)
              _ = M * (K + 2) * mq := by ring
          have hlt : Q.card < m := by rw [hQc, ← hZm]; omega
          have hpos : 1 ≤ M * (K + 2) * mq := Nat.one_le_iff_ne_zero.2
            (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))
          refine ⟨_, le_of_eq (by rw [hQc]), ih Q.card hlt tg₁ bd₁ Q X₁
            (M * (K + 2) * mq) rfl (fun x => disjoint_of_subset_right hQ (h1 x)) h2 h3 h4' hT1
            hpos hdeg₁⟩)
      exact ⟨Bd₁, Bd₂, ⟨by rw [hQc] at hBd₁; exact hBd₁, hBd₂⟩, hres⟩
    obtain ⟨b₁, b₂, hP, hout⟩ := classStep (q := q) (r := r) (i := 1) (C := Cr + Cb) hTs
      (fun b₁ b₂ => b₁ ≤ Cst * D + B * mq ∧ b₂ ≤ A * (M * (K + 2) * mq) + A' * mq) hclass
    refine hout.mono le_rfl fun S _ => ?_
    have hs1 : ∑ j, b₁ j ≤ 4 * (Cst * D + B * mq) := by
      calc ∑ j, b₁ j ≤ ∑ _j : Fin 4, (Cst * D + B * mq) := sum_le_sum fun j _ => (hP j).1
        _ = 4 * (Cst * D + B * mq) := by simp
    have hs2 : univ.sup b₂ ≤ A * (M * (K + 2) * mq) + A' * mq := Finset.sup_le fun j _ => (hP j).2
    have e2 : A * D = 4 * (Cst * D) + Ab * (K + 2) * D := by rw [hA]; ring
    have e3 : A' * (4 * mq) = 4 * (4 * B * mq) + 4 * (A * (M * (K + 2) * mq)) +
        4 * (Ab * K * mq) := by rw [hA']; ring
    have h5 : A' * (4 * mq) ≤ A' * Zc.card := Nat.mul_le_mul_left _ h4
    show ∑ j, b₁ j + univ.sup b₂ ≤ A * D + A' * Zc.card
    have e4 : A' * mq = 4 * B * mq + A * (M * (K + 2) * mq) + Ab * K * mq := by rw [hA']; ring
    have e5 : A' * (4 * mq) = 4 * (A' * mq) := by ring
    have e6 : 4 * B * mq = 4 * (B * mq) := by ring
    omega

end RefinedAbsorption.LinkSpread
