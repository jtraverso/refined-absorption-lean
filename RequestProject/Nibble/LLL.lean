module
public import RequestProject.Nibble.FiniteProb

/-!
# The Lovász Local Lemma for random subsets

For the `p`-random subset of a finite set `E` of coins we prove:

* `Ex_mul_of_local`: if `f` only depends on the coins in `C` and `g` only on the coins in `C'`,
  with `C, C'` disjoint, then `f` and `g` are independent;
* `lll`: the symmetric Lovász Local Lemma.  If every bad event `A i` only depends on the coins
  in `Cs i`, has probability at most `q`, and the coin sets of at most `d` events (including
  itself) meet `Cs i`, then `4 q (d + 1) ≤ 1` guarantees an outcome avoiding all bad events.

There is no bound on the number of events.
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset

variable {β : Type*} [DecidableEq β]

theorem insert_inter_eq_of_notMem {a : β} {S C : Finset β} (ha : a ∉ C) :
    insert a S ∩ C = S ∩ C := by
  ext x; simp only [mem_inter, mem_insert]
  constructor
  · rintro ⟨rfl | h, hx⟩
    · exact absurd hx ha
    · exact ⟨h, hx⟩
  · rintro ⟨h, hx⟩; exact ⟨Or.inr h, hx⟩

theorem insert_inter_inter (a : β) (S C : Finset β) :
    insert a S ∩ C = insert a (S ∩ C) ∩ C := by
  ext x; simp only [mem_inter, mem_insert]; tauto

/-- Independence of functions depending on disjoint sets of coins. -/
theorem Ex_mul_of_local (p : ℝ) (E : Finset β) {C C' : Finset β} (hCC : Disjoint C C') :
    ∀ {f g : Finset β → ℝ}, (∀ S ⊆ E, f S = f (S ∩ C)) → (∀ S ⊆ E, g S = g (S ∩ C')) →
      Ex p E (fun S => f S * g S) = Ex p E f * Ex p E g := by
  induction E using Finset.induction_on with
  | empty => intro f g _ _; simp [Ex_empty]
  | insert a E ha ih =>
    intro f g hf hg
    have hfE : ∀ S ⊆ E, f S = f (S ∩ C) := fun S hS => hf S (hS.trans (subset_insert a E))
    have hgE : ∀ S ⊆ E, g S = g (S ∩ C') := fun S hS => hg S (hS.trans (subset_insert a E))
    have hfI' : ∀ S ⊆ E, (fun S => f (insert a S)) S = (fun S => f (insert a S)) (S ∩ C) := by
      intro S hS
      simp only
      rw [hf _ (insert_subset_insert a hS),
        hf _ (insert_subset_insert a ((inter_subset_left).trans hS))]
      congr 1; ext x; simp only [mem_inter, mem_insert]; tauto
    have hgI' : ∀ S ⊆ E, (fun S => g (insert a S)) S = (fun S => g (insert a S)) (S ∩ C') := by
      intro S hS
      simp only
      rw [hg _ (insert_subset_insert a hS),
        hg _ (insert_subset_insert a ((inter_subset_left).trans hS))]
      congr 1; ext x; simp only [mem_inter, mem_insert]; tauto
    by_cases haC' : a ∈ C'
    · have haC : a ∉ C := fun h => disjoint_left.1 hCC h haC'
      have hfc : ∀ S ⊆ E, f (insert a S) = f S := by
        intro S hS
        rw [hf _ (insert_subset_insert a hS), insert_inter_eq_of_notMem haC, ← hfE S hS]
      rw [Ex_insert p ha, Ex_insert p ha, Ex_insert p ha]
      rw [Ex_congr p E (f := fun S => f (insert a S) * g (insert a S))
        (g := fun S => f S * g (insert a S)) fun S hS => by simp only [hfc S hS]]
      rw [Ex_congr p E (f := fun S => f (insert a S)) (g := f) hfc]
      rw [ih hfE hgE, ih hfE hgI']
      ring
    · have hgc : ∀ S ⊆ E, g (insert a S) = g S := by
        intro S hS
        rw [hg _ (insert_subset_insert a hS), insert_inter_eq_of_notMem haC', ← hgE S hS]
      rw [Ex_insert p ha, Ex_insert p ha, Ex_insert p ha]
      rw [Ex_congr p E (f := fun S => f (insert a S) * g (insert a S))
        (g := fun S => f (insert a S) * g S) fun S hS => by simp only [hgc S hS]]
      rw [Ex_congr p E (f := fun S => g (insert a S)) (g := g) hgc]
      rw [ih hfE hgE, ih hfI' hgE]
      ring

/-- Independence of events depending on disjoint sets of coins. -/
theorem Pr_and_of_local (p : ℝ) (E : Finset β) {C C' : Finset β} (hCC : Disjoint C C')
    {A B : Finset β → Prop} (hA : ∀ S ⊆ E, A S ↔ A (S ∩ C)) (hB : ∀ S ⊆ E, B S ↔ B (S ∩ C')) :
    Pr p E (fun S => A S ∧ B S) = Pr p E A * Pr p E B := by
  classical
  unfold Pr
  refine Eq.trans (Ex_congr p E
    (g := fun S => (if A S then (1 : ℝ) else 0) * (if B S then (1 : ℝ) else 0))
    fun S _ => by by_cases hA : A S <;> by_cases hB : B S <;> simp [hA, hB]) ?_
  refine Ex_mul_of_local p E hCC (fun S hS => ?_) (fun S hS => ?_)
  · simp only [hA S hS]
  · simp only [hB S hS]

omit [DecidableEq β] in
theorem Pr_split (p : ℝ) (E : Finset β) (P Q : Finset β → Prop) :
    Pr p E P = Pr p E (fun S => P S ∧ Q S) + Pr p E (fun S => P S ∧ ¬ Q S) := by
  classical
  unfold Pr
  rw [← Ex_add]
  refine Ex_congr p E fun S _ => ?_
  by_cases hP : P S <;> by_cases hQ : Q S <;> simp [hP, hQ]

/-- **The symmetric Lovász Local Lemma** for random subsets. -/
theorem lll {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β) {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Finset β → Prop) (Cs : ι → Finset β) (d : ℕ)
    (hloc : ∀ i ∈ I, ∀ S ⊆ E, A i S ↔ A i (S ∩ Cs i))
    (hpr : ∀ i ∈ I, Pr p E (A i) ≤ q)
    (hdep : ∀ i ∈ I, (I.filter (fun j => ¬ Disjoint (Cs i) (Cs j))).card ≤ d)
    (hq : 4 * q * (d + 1) ≤ 1) :
    ∃ S ⊆ E, ∀ i ∈ I, ¬ A i S := by
  classical
  rcases I.eq_empty_or_nonempty with hI | ⟨i₀, hi₀⟩
  · exact ⟨∅, empty_subset _, by simp [hI]⟩
  have hq0 : 0 ≤ q := (Pr_nonneg hp0 hp1 E _).trans (hpr i₀ hi₀)
  set x : ℝ := 2 * q with hx
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hx2 : x ≤ 1 / 2 := by nlinarith
  have hx0 : 0 ≤ x := by positivity
  set P : Finset ι → ℝ := fun J => Pr p E (fun S => ∀ j ∈ J, ¬ A j S) with hP
  have hP0 : ∀ J, 0 ≤ P J := fun J => Pr_nonneg hp0 hp1 E _
  -- adding one event
  have hstep : ∀ (K : Finset ι) (j : ι), P (insert j K) =
      P K - Pr p E (fun S => A j S ∧ ∀ m ∈ K, ¬ A m S) := by
    intro K j
    have h := Pr_split p E (fun S => ∀ m ∈ K, ¬ A m S) (fun S => A j S)
    have h1 : P (insert j K) = Pr p E (fun S => (∀ m ∈ K, ¬ A m S) ∧ ¬ A j S) := by
      simp only [hP]
      refine Pr_congr p E fun S _ => ?_
      simp only [mem_insert, forall_eq_or_imp]; tauto
    have h2 : Pr p E (fun S => (∀ m ∈ K, ¬ A m S) ∧ A j S) =
        Pr p E (fun S => A j S ∧ ∀ m ∈ K, ¬ A m S) :=
      Pr_congr p E fun S _ => and_comm
    have h3 : P K = Pr p E (fun S => ∀ m ∈ K, ¬ A m S) := rfl
    rw [h1, h3, h, h2]; ring
  -- the main claim
  have claim : ∀ n, ∀ J : Finset ι, J.card = n → J ⊆ I → ∀ i ∈ I, i ∉ J →
      Pr p E (fun S => A i S ∧ ∀ j ∈ J, ¬ A j S) ≤ x * P J := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro J hJn hJI i hi hiJ
    set J1 := J.filter (fun j => ¬ Disjoint (Cs i) (Cs j)) with hJ1
    set J2 := J.filter (fun j => Disjoint (Cs i) (Cs j)) with hJ2
    -- step a: independence from the far events
    have ha : Pr p E (fun S => A i S ∧ ∀ j ∈ J, ¬ A j S) ≤ q * P J2 := by
      have hmono : Pr p E (fun S => A i S ∧ ∀ j ∈ J, ¬ A j S) ≤
          Pr p E (fun S => A i S ∧ ∀ j ∈ J2, ¬ A j S) :=
        Pr_mono hp0 hp1 E fun S _ h => ⟨h.1, fun j hj => h.2 j (mem_filter.1 hj).1⟩
      have hind : Pr p E (fun S => A i S ∧ ∀ j ∈ J2, ¬ A j S) = Pr p E (A i) * P J2 := by
        refine Pr_and_of_local p E (C := Cs i) (C' := J2.biUnion Cs) ?_ (hloc i hi) ?_
        · rw [disjoint_biUnion_right]
          intro j hj; exact (mem_filter.1 hj).2
        · intro S hS
          have key : ∀ j ∈ J2, A j S ↔ A j (S ∩ J2.biUnion Cs) := by
            intro j hj
            have hjI : j ∈ I := hJI (mem_filter.1 hj).1
            have : S ∩ J2.biUnion Cs ∩ Cs j = S ∩ Cs j := by
              rw [inter_assoc]
              congr 1
              exact inter_eq_right.2 (subset_biUnion_of_mem Cs hj)
            have h2 := hloc j hjI (S ∩ J2.biUnion Cs) ((inter_subset_left).trans hS)
            rw [this] at h2
            exact (hloc j hjI S hS).trans h2.symm
          constructor
          · intro h j hj hA; exact h j hj ((key j hj).2 hA)
          · intro h j hj hA; exact h j hj ((key j hj).1 hA)
      rw [hind] at hmono
      have := mul_le_mul_of_nonneg_right (hpr i hi) (hP0 J2)
      linarith
    -- step b: the near events cost a factor `(1-x)` each
    have hb : ∀ L ⊆ J1, (1 - x) ^ L.card * P J2 ≤ P (J2 ∪ L) := by
      intro L
      induction L using Finset.induction_on with
      | empty => intro _; simp
      | insert j L hjL ihL =>
        intro hL
        have hjJ1 : j ∈ J1 := hL (mem_insert_self j L)
        have hLJ1 : L ⊆ J1 := (subset_insert j L).trans hL
        have hjJ : j ∈ J := (mem_filter.1 hjJ1).1
        have hjJ2 : j ∉ J2 := fun h => (mem_filter.1 hjJ1).2 (mem_filter.1 h).2
        have hKJ : J2 ∪ L ⊆ J := union_subset (filter_subset _ _)
          (hLJ1.trans (filter_subset _ _))
        have hjK : j ∉ J2 ∪ L := by
          rw [mem_union]; rintro (h | h)
          · exact hjJ2 h
          · exact hjL h
        have hKlt : (J2 ∪ L).card < n := by
          rw [← hJn]
          refine card_lt_card ⟨hKJ, fun h => hjK (h hjJ)⟩
        have hIH := ih _ hKlt (J2 ∪ L) rfl (hKJ.trans hJI) j (hJI hjJ) hjK
        have he : J2 ∪ insert j L = insert j (J2 ∪ L) := by
          ext m; simp only [mem_union, mem_insert]; tauto
        rw [he, hstep, card_insert_of_notMem hjL, pow_succ]
        have h1 := ihL hLJ1
        have h1x : 0 ≤ 1 - x := by linarith
        nlinarith [hP0 (J2 ∪ L)]
    have hJ12 : J2 ∪ J1 = J := by
      rw [hJ1, hJ2]; exact filter_union_filter_not_eq _ _
    have hcard : J1.card ≤ d := by
      refine le_trans (card_le_card ?_) (hdep i hi)
      exact filter_subset_filter _ hJI
    have hpow : 1 / 2 ≤ (1 - x) ^ d := by
      have := one_add_mul_le_pow (a := -x) (by linarith) d
      rw [← sub_eq_add_neg] at this
      have hxd : x * d ≤ 1 / 2 := by nlinarith
      nlinarith
    have hpow2 : (1 - x) ^ d ≤ (1 - x) ^ J1.card :=
      pow_le_pow_of_le_one (by linarith) (by linarith) hcard
    have hbJ := hb J1 Subset.rfl
    rw [hJ12] at hbJ
    have hP2 := hP0 J2
    have h5 : q ≤ x * (1 - x) ^ J1.card := by
      have := hpow.trans hpow2
      rw [hx] at this ⊢; nlinarith
    have : q * P J2 ≤ x * ((1 - x) ^ J1.card * P J2) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h5 hP2
    calc Pr p E (fun S => A i S ∧ ∀ j ∈ J, ¬ A j S) ≤ q * P J2 := ha
      _ ≤ x * ((1 - x) ^ J1.card * P J2) := this
      _ ≤ x * P J := mul_le_mul_of_nonneg_left hbJ hx0
  -- positivity of the probability of avoiding everything
  have hpos : ∀ L ⊆ I, (1 - x) ^ L.card ≤ P L := by
    intro L
    induction L using Finset.induction_on with
    | empty =>
      intro _
      simp only [card_empty, pow_zero, hP]
      have : Pr p E (fun S => ∀ j ∈ (∅ : Finset ι), ¬ A j S) = 1 := by
        unfold Pr; simp [Ex_const]
      rw [this]
    | insert j L hjL ihL =>
      intro hL
      have hLI : L ⊆ I := (subset_insert j L).trans hL
      have h1 := ihL hLI
      have h2 := claim _ L rfl hLI j (hL (mem_insert_self j L)) hjL
      rw [hstep, card_insert_of_notMem hjL, pow_succ]
      have h1x : 0 ≤ 1 - x := by linarith
      have : (1 - x) ^ L.card * (1 - x) ≤ P L * (1 - x) := mul_le_mul_of_nonneg_right h1 h1x
      nlinarith [hP0 L]
  have hPI : 0 < P I := lt_of_lt_of_le (pow_pos (by linarith) _) (hpos I Subset.rfl)
  by_contra hcon
  push_neg at hcon
  have : P I = 0 := by
    simp only [hP]
    refine (Pr_congr p E (Q := fun _ => False) fun S hS => ?_).trans ?_
    · obtain ⟨i, hi, hAi⟩ := hcon S hS
      exact ⟨fun h => h i hi hAi, False.elim⟩
    · exact Pr_eq_zero p E fun S _ h => h
  linarith

/-- The Lovász Local Lemma with a real dependency bound. -/
theorem lll_real {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β) {ι : Type*}
    [DecidableEq ι] (I : Finset ι) (A : ι → Finset β → Prop) (Cs : ι → Finset β) (d : ℝ)
    (hloc : ∀ i ∈ I, ∀ S ⊆ E, A i S ↔ A i (S ∩ Cs i))
    (hpr : ∀ i ∈ I, Pr p E (A i) ≤ q)
    (hdep : ∀ i ∈ I, ((I.filter (fun j => ¬ Disjoint (Cs i) (Cs j))).card : ℝ) ≤ d)
    (hq0 : 0 ≤ q) (hd : 0 ≤ d) (hq : 4 * q * (d + 1) ≤ 1) :
    ∃ S ⊆ E, ∀ i ∈ I, ¬ A i S := by
  refine lll hp0 hp1 E I A Cs ⌊d⌋₊ hloc hpr (fun i hi => Nat.le_floor (hdep i hi)) ?_
  have := Nat.floor_le hd
  have h4 : 4 * q * ((⌊d⌋₊ : ℝ) + 1) ≤ 4 * q * (d + 1) := by gcongr
  linarith

end RefinedAbsorption.Nibble
