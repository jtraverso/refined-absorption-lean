module
public import RequestProject.Placement.ReserveLemma52

/-!
# Placing gadgets inside a reserve when parallel edges are allowed

`reserveCliqueEmbedding` places gadgets so that their new edges are pairwise disjoint and avoid a
host graph.  For that it needs `C · D ≤ |Z|`: the edges already used must not exclude too many
vertices of the reserve.

In a *multigraph* refiner the new edges of different gadgets may coincide (they are different
labelled copies), so disjointness is not needed.  Then the same greedy argument, with no
forbidden edges at all, works for every degree `D`: only the mixed loads have to be kept below
their caps.  This is what is needed in the dense part of the refine-down construction, where
`D` is of the order of `|Z|`.

* `multiCliqueEmbedding`: for fixed `r, h, k` there is `C` such that gadgets with roots anywhere
  in `Fin n` can be placed with their auxiliary vertices in a reserve `Z` with `|Z| ≥ C`, such that
  every `(r-1)`-set lies in at most `C · D` gadget vertex sets and in at most `C · D` new edges
  counted with multiplicity, provided every `j`-set lies in at most `D · |Z|^(r-1-j)` root sets.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset

variable {n h : ℕ} {ι : Type*} [DecidableEq ι]

/-- The invariant of the outer placement without disjointness requirements. -/
structure OuterInvM (r lam D : ℕ) (Z : Finset (Fin n)) (Rs : ι → Finset (Fin n))
    (s : Finset ι) (Φ : ι → Fin h → Fin n) : Prop where
  valid : ∀ i ∈ s, ValidPlacement (Rs i) (Φ i)
  range : ∀ i ∈ s, ∀ p, Φ i p ∈ Z
  loads : ∀ J U : Finset (Fin n), U.Nonempty → J.card + U.card ≤ r - 1 →
    load Rs Φ s J U ≤ capA r lam D Z.card J.card U.card

omit [DecidableEq ι] in
/-- At the top level the sum of the mixed loads is at most `2^(r-1) λ^(r-1) D`. -/
theorem sum_loads_leM {r lam D : ℕ} (Z : Finset (Fin n)) (I : Finset ι)
    (Rs : ι → Finset (Fin n)) (s : Finset ι) (hsI : s ⊆ I) (Φ : ι → Fin h → Fin n)
    (hinv : OuterInvM r lam D Z Rs s Φ) (hlam : 1 ≤ lam)
    (hDeg : ∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ Rs i).card ≤ D)
    (S : Finset (Fin n)) (hS : S.card = r - 1) :
    ∑ J ∈ S.powerset, load Rs Φ s J (S \ J) ≤ 2 ^ (r - 1) * lam ^ (r - 1) * D := by
  calc ∑ J ∈ S.powerset, load Rs Φ s J (S \ J) ≤ ∑ _J ∈ S.powerset, lam ^ (r - 1) * D := by
        apply sum_le_sum
        intro J hJ
        rw [mem_powerset] at hJ
        have hcard : J.card + (S \ J).card = r - 1 := by
          rw [card_sdiff_of_subset hJ, ← hS]; have := card_le_card hJ; omega
        rcases (S \ J).eq_empty_or_nonempty with hU | hU
        · have hJS : J = S := by
            apply eq_of_subset_of_card_le hJ
            rw [hU, card_empty] at hcard; omega
          subst hJS
          rw [hU]
          calc load Rs Φ s J ∅ ≤ (I.filter fun i => J ⊆ Rs i).card := by
                apply card_le_card
                intro i hi
                simp only [mem_filter] at hi ⊢
                exact ⟨hsI hi.1, hi.2.1⟩
            _ ≤ D := hDeg J hS
            _ ≤ lam ^ (r - 1) * D := Nat.le_mul_of_pos_left _ (by positivity)
        · refine (hinv.loads J _ hU hcard.le).trans ?_
          unfold capA
          rw [show r - 1 - J.card - (S \ J).card = 0 by omega, pow_zero, mul_one]
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_right hlam
          omega
    _ = 2 ^ (r - 1) * (lam ^ (r - 1) * D) := by
        rw [sum_const, card_powerset, hS, smul_eq_mul]
    _ = _ := by ring

/-- **One step of the outer placement without disjointness.** -/
theorem outerInvM_step {r k : ℕ} (Z : Finset (Fin n)) (I : Finset ι) (Rs : ι → Finset (Fin n))
    (Ts : ι → Finset (Finset (Fin n ⊕ Fin h))) (D : ℕ)
    (hw : ∀ i ∈ I, GadgetWF r k (Rs i) (Ts i))
    (hZ : 8 * (k + h + 1) ≤ Z.card)
    (hRoot : ∀ J : Finset (Fin n), J.card ≤ r - 1 →
      (I.filter fun i => J ⊆ Rs i).card ≤ D * Z.card ^ (r - 1 - J.card))
    {s : Finset ι} (hsI : s ⊆ I) {i : ι} (hiI : i ∈ I) (his : i ∉ s) {Φ : ι → Fin h → Fin n}
    (hinv : OuterInvM r (placeLam h k) D Z Rs s Φ) :
    ∃ φ, OuterInvM r (placeLam h k) D Z Rs (insert i s) (Function.update Φ i φ) := by
  classical
  set a := Z.card
  have hD : 0 < D := by
    have := hRoot ∅ (by simp)
    have hmem : i ∈ I.filter fun j => (∅ : Finset (Fin n)) ⊆ Rs j := by simp [hiI]
    have h1 := card_pos.2 ⟨i, hmem⟩
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · rw [h0, zero_mul] at this; omega
    · exact h0
  have hroot : ∀ J ⊆ Rs i, J.card ≤ r - 1 → load Rs Φ s J ∅ ≤ D * a ^ (r - 1 - J.card) := by
    intro J _ hJ
    refine le_trans (card_le_card ?_) (hRoot J hJ)
    intro j hj
    simp only [mem_filter] at hj ⊢
    exact ⟨hsI hj.1, hj.2.1⟩
  have hlam : 4 * 2 ^ (k + h) * h ≤ placeLam h k := Nat.le_succ _
  have hF : ∀ B : Finset (Fin n), B.card = r - 1 → deg (∅ : Finset (Finset (Fin n))) B ≤ 0 := by
    intro B _; simp [deg]
  have hnum : 4 * (k + h + 2 ^ (k + h) * 0) < 3 * a := by omega
  obtain ⟨φ, hφ⟩ :=
    exists_innerInvA_univ Z Rs Φ s (Rs i) (Ts i) (hw i hiI) ∅ hroot hF hD hlam hnum
  have hΦ : ∀ j ∈ s, Function.update Φ i φ j = Φ j := fun j hj =>
    Function.update_of_ne (by rintro rfl; exact his hj) _ _
  have hφinj : Function.Injective φ := fun a b hab => hφ.inj (mem_univ a) (mem_univ b) hab
  refine ⟨φ, ⟨?_, ?_, ?_⟩⟩
  · intro j hj
    rcases mem_insert.1 hj with rfl | hj
    · rw [Function.update_self]
      exact ⟨hφinj, fun p => hφ.avoid p (mem_univ p)⟩
    · rw [hΦ j hj]; exact hinv.valid j hj
  · intro j hj p
    rcases mem_insert.1 hj with rfl | hj
    · rw [Function.update_self]; exact hφ.range p (mem_univ p)
    · rw [hΦ j hj]; exact hinv.range j hj p
  · intro J U hU hcard
    rw [load_insert his, Function.update_self, load_congr hΦ]
    split_ifs with hc
    · obtain ⟨hJR, hUφ⟩ := hc
      set P := univ.filter fun p => φ p ∈ U
      have hPU : P.image φ = U := by
        ext x
        simp only [P, mem_image, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨p, hp, rfl⟩; exact hp
        · intro hx
          obtain ⟨p, -, hp⟩ := mem_image.1 (hUφ hx)
          exact ⟨p, hp ▸ hx, hp⟩
      have hPc : P.card = U.card := by
        rw [← hPU, card_image_of_injective _ hφinj]
      have hPne : P.Nonempty := by
        rw [← card_pos, hPc]; exact card_pos.2 hU
      have := hφ.loads J hJR P (subset_univ _) hPne (by omega)
      rw [hPU, hPc] at this
      omega
    · rw [add_zero]; exact hinv.loads J U hU hcard

/-- The constant of `multiCliqueEmbedding`. -/
def multiC (r h k : ℕ) : ℕ :=
  8 * (k + h + 1) + (2 ^ (k + h) + 1) * 2 ^ (r - 1) * placeLam h k ^ (r - 1)

/-- The edges of one placed gadget containing `S` are at most `2^(k+h)`, and there are none
unless `S` lies in the vertex set of the gadget. -/
theorem card_newEdges_filter_le {r k : ℕ} {R : Finset (Fin n)}
    {T : Finset (Finset (Fin n ⊕ Fin h))} (hw : GadgetWF r k R T) (φ : Fin h → Fin n)
    (S : Finset (Fin n)) :
    ((newEdges T φ).filter fun e => S ⊆ e).card ≤
      if S ⊆ R ∪ auxImage φ then 2 ^ (k + h) else 0 := by
  split_ifs with hS
  · exact (card_le_card (filter_subset _ _)).trans (card_image_le.trans (card_template_le hw))
  · apply le_of_eq
    rw [card_eq_zero, filter_eq_empty_iff]
    intro e he hSe
    simp only [newEdges, mem_image] at he
    obtain ⟨t, ht, rfl⟩ := he
    exact hS (hSe.trans (placeEdge_subset hw φ ht))

/-- **Gadget placement inside a reserve with parallel edges allowed.**  For fixed `r`, `h`, `k`
there is `C` such that gadgets with at most `k` (and at least `r - 1`) roots anywhere in `Fin n`
and `h` auxiliary vertices can be placed with all auxiliary vertices in the reserve `Z`
(`|Z| ≥ C`), by injective maps avoiding their roots, such that every `(r-1)`-set lies in the
vertex sets of at most `C · D` gadgets and in at most `C · D` new edges counted with
multiplicity.  Hypothesis: every `j`-set (`j ≤ r - 1`) lies in at most `D · |Z|^(r-1-j)` root
sets.  There is no upper bound on `D`. -/
theorem multiCliqueEmbedding (r h k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ) {ι : Type*} [DecidableEq ι] (I : Finset ι)
      (R : ι → Finset (Fin n)) (T : ι → Finset (Finset (Fin n ⊕ Fin h)))
      (Z : Finset (Fin n)) (D : ℕ),
      (∀ i ∈ I, GadgetWF r k (R i) (T i)) → C ≤ Z.card →
      (∀ J : Finset (Fin n), J.card ≤ r - 1 →
        (I.filter fun i => J ⊆ R i).card ≤ D * Z.card ^ (r - 1 - J.card)) →
      ∃ Φ : ι → Fin h → Fin n,
        (∀ i ∈ I, ValidPlacement (R i) (Φ i)) ∧
        (∀ i ∈ I, ∀ p, Φ i p ∈ Z) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          (I.filter fun i => S ⊆ R i ∪ auxImage (Φ i)).card ≤ C * D) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          ∑ i ∈ I, ((newEdges (T i) (Φ i)).filter fun e => S ⊆ e).card ≤ C * D) := by
  refine ⟨multiC r h k, by unfold multiC; omega, ?_⟩
  intro n ι _ I R T Z D hw hZ hRoot
  have hZ8 : 8 * (k + h + 1) ≤ Z.card := le_trans (by unfold multiC; omega) hZ
  have hZ0 : 0 < Z.card := by omega
  have hDeg : ∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ R i).card ≤ D := by
    intro S hS
    have := hRoot S hS.le
    rwa [hS, Nat.sub_self, pow_zero, mul_one] at this
  obtain ⟨z₀, -⟩ := card_pos.1 hZ0
  have key : ∀ s ⊆ I, ∃ Φ : ι → Fin h → Fin n, OuterInvM r (placeLam h k) D Z R s Φ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun _ _ => z₀, ⟨by simp, by simp, ?_⟩⟩
      intro J U _ _
      simp [load]
    | insert i s his ih =>
      intro hsI
      obtain ⟨Φ, hΦ⟩ := ih ((subset_insert i s).trans hsI)
      obtain ⟨φ, hφ⟩ := outerInvM_step Z I R T D hw hZ8 hRoot
        ((subset_insert i s).trans hsI) (hsI (mem_insert_self i s)) his hΦ
      exact ⟨_, hφ⟩
  obtain ⟨Φ, hΦ⟩ := key I subset_rfl
  have hlam1 : 1 ≤ placeLam h k := Nat.le_add_left _ _
  have hcov : ∀ S : Finset (Fin n), S.card = r - 1 →
      (I.filter fun i => S ⊆ R i ∪ auxImage (Φ i)).card ≤
        2 ^ (r - 1) * placeLam h k ^ (r - 1) * D := fun S hS =>
    (card_cover_le_loads R Φ I S).trans
      (sum_loads_leM Z I R I subset_rfl Φ hΦ hlam1 hDeg S hS)
  refine ⟨Φ, hΦ.valid, hΦ.range, fun S hS => (hcov S hS).trans ?_, fun S hS => ?_⟩
  · apply Nat.mul_le_mul_right
    unfold multiC
    nlinarith [Nat.zero_le (2 ^ (k + h) * 2 ^ (r - 1) * placeLam h k ^ (r - 1))]
  · calc ∑ i ∈ I, ((newEdges (T i) (Φ i)).filter fun e => S ⊆ e).card
        ≤ ∑ i ∈ I, if S ⊆ R i ∪ auxImage (Φ i) then 2 ^ (k + h) else 0 :=
          sum_le_sum fun i hi => card_newEdges_filter_le (hw i hi) (Φ i) S
      _ = 2 ^ (k + h) * (I.filter fun i => S ⊆ R i ∪ auxImage (Φ i)).card := by
          rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 ^ (k + h) * (2 ^ (r - 1) * placeLam h k ^ (r - 1) * D) :=
          Nat.mul_le_mul_left _ (hcov S hS)
      _ ≤ multiC r h k * D := by
          rw [← mul_assoc, ← mul_assoc]
          apply Nat.mul_le_mul_right
          unfold multiC
          nlinarith [Nat.zero_le (2 ^ (r - 1) * placeLam h k ^ (r - 1))]

end RefinedAbsorption.Placement
