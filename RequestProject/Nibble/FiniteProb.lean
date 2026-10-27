module
public import RequestProject.MathlibImports

/-!
# Finite product probability for random subsets

For a finite set `E` of "coins" and a probability `p`, we consider the random subset `S ⊆ E`
obtained by keeping every element of `E` independently with probability `p`.  Everything is
expressed with finite sums over `E.powerset`, so no measure theory is needed:

* `wt p E S = p^{|S|} (1-p)^{|E|-|S|}` is the probability of the outcome `S`;
* `Ex p E f` is the expectation of `f : Finset β → ℝ` and `Pr p E P` the probability of `P`.

We prove the basic toolkit used in the nibble: linearity, monotonicity, the decomposition along
one coin (`Ex_insert`), the probability that `S` contains a fixed set or avoids a fixed set,
the union bound, the first-moment existence principle, and a Bernstein-type concentration
inequality for functions with bounded differences (`Ex_exp_le`, `Pr_ge_le`, `Pr_le_le`), in
which the variance proxy is `p ∑ c_a²`.
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset

variable {β : Type*} [DecidableEq β]

/-- Probability of the outcome `S` when every element of `E` is kept independently with
probability `p`. -/
noncomputable def wt (p : ℝ) (E S : Finset β) : ℝ := p ^ S.card * (1 - p) ^ (E.card - S.card)

/-- Expectation of `f` for the `p`-random subset of `E`. -/
noncomputable def Ex (p : ℝ) (E : Finset β) (f : Finset β → ℝ) : ℝ :=
  ∑ S ∈ E.powerset, wt p E S * f S

open Classical in
/-- Probability of the event `P` for the `p`-random subset of `E`. -/
noncomputable def Pr (p : ℝ) (E : Finset β) (P : Finset β → Prop) : ℝ :=
  Ex p E (fun S => if P S then 1 else 0)

omit [DecidableEq β] in
theorem Ex_empty (p : ℝ) (f : Finset β → ℝ) : Ex p ∅ f = f ∅ := by
  simp [Ex, wt]

/-- Decomposition of the expectation along one coin. -/
theorem Ex_insert (p : ℝ) {a : β} {E : Finset β} (ha : a ∉ E) (f : Finset β → ℝ) :
    Ex p (insert a E) f = (1 - p) * Ex p E f + p * Ex p E (fun S => f (insert a S)) := by
  unfold Ex
  rw [sum_powerset_insert ha, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun S hS => ?_
    have hSE : S.card ≤ E.card := card_le_card (mem_powerset.1 hS)
    unfold wt
    rw [card_insert_of_notMem ha, show E.card + 1 - S.card = (E.card - S.card) + 1 by omega,
      pow_succ]
    ring
  · refine sum_congr rfl fun S hS => ?_
    have hS' : S ⊆ E := mem_powerset.1 hS
    have haS : a ∉ S := fun h => ha (hS' h)
    have hSE : S.card ≤ E.card := card_le_card hS'
    unfold wt
    rw [card_insert_of_notMem ha, card_insert_of_notMem haS,
      show E.card + 1 - (S.card + 1) = E.card - S.card by omega, pow_succ]
    ring

omit [DecidableEq β] in
theorem Ex_congr (p : ℝ) (E : Finset β) {f g : Finset β → ℝ} (h : ∀ S ⊆ E, f S = g S) :
    Ex p E f = Ex p E g :=
  sum_congr rfl fun S hS => by rw [h S (mem_powerset.1 hS)]

omit [DecidableEq β] in
theorem wt_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E S : Finset β) : 0 ≤ wt p E S :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

omit [DecidableEq β] in
theorem Ex_add (p : ℝ) (E : Finset β) (f g : Finset β → ℝ) :
    Ex p E (fun S => f S + g S) = Ex p E f + Ex p E g := by
  unfold Ex; rw [← sum_add_distrib]; exact sum_congr rfl fun S _ => by ring

omit [DecidableEq β] in
theorem Ex_const_mul (p : ℝ) (E : Finset β) (c : ℝ) (f : Finset β → ℝ) :
    Ex p E (fun S => c * f S) = c * Ex p E f := by
  unfold Ex; rw [mul_sum]; exact sum_congr rfl fun S _ => by ring

omit [DecidableEq β] in
theorem Ex_neg (p : ℝ) (E : Finset β) (f : Finset β → ℝ) :
    Ex p E (fun S => -f S) = -Ex p E f := by
  unfold Ex; rw [← sum_neg_distrib]; exact sum_congr rfl fun S _ => by ring

omit [DecidableEq β] in
theorem Ex_sub (p : ℝ) (E : Finset β) (f g : Finset β → ℝ) :
    Ex p E (fun S => f S - g S) = Ex p E f - Ex p E g := by
  unfold Ex; rw [← sum_sub_distrib]; exact sum_congr rfl fun S _ => by ring

omit [DecidableEq β] in
theorem Ex_sum (p : ℝ) (E : Finset β) {ι : Type*} (s : Finset ι) (f : ι → Finset β → ℝ) :
    Ex p E (fun S => ∑ i ∈ s, f i S) = ∑ i ∈ s, Ex p E (f i) := by
  unfold Ex; simp_rw [mul_sum]; rw [sum_comm]

/-- The weights sum to one. -/
theorem Ex_const (p : ℝ) (E : Finset β) (c : ℝ) : Ex p E (fun _ => c) = c := by
  induction E using Finset.induction_on with
  | empty => simp [Ex_empty]
  | insert a E ha ih => rw [Ex_insert p ha]; simp only [ih]; ring

omit [DecidableEq β] in
theorem Ex_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β) {f g : Finset β → ℝ}
    (h : ∀ S ⊆ E, f S ≤ g S) : Ex p E f ≤ Ex p E g :=
  sum_le_sum fun S hS => mul_le_mul_of_nonneg_left (h S (mem_powerset.1 hS))
    (wt_nonneg hp0 hp1 E S)

theorem Ex_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β) {f : Finset β → ℝ}
    (h : ∀ S ⊆ E, 0 ≤ f S) : 0 ≤ Ex p E f := by
  have := Ex_mono hp0 hp1 E (f := fun _ => 0) h
  rwa [Ex_const] at this

theorem abs_Ex_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β) {f : Finset β → ℝ}
    {c : ℝ} (h : ∀ S ⊆ E, |f S| ≤ c) : |Ex p E f| ≤ c := by
  rw [abs_le]
  constructor
  · have := Ex_mono hp0 hp1 E (f := fun _ => -c) (g := f) fun S hS => (abs_le.1 (h S hS)).1
    rwa [Ex_const] at this
  · have := Ex_mono hp0 hp1 E (f := f) (g := fun _ => c) fun S hS => (abs_le.1 (h S hS)).2
    rwa [Ex_const] at this

/-! ### Probabilities -/

theorem Pr_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β) (P : Finset β → Prop) :
    0 ≤ Pr p E P := by
  classical
  unfold Pr
  exact Ex_nonneg hp0 hp1 E fun S _ => by split_ifs <;> norm_num

omit [DecidableEq β] in
theorem Pr_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β) {P Q : Finset β → Prop}
    (h : ∀ S ⊆ E, P S → Q S) : Pr p E P ≤ Pr p E Q := by
  classical
  unfold Pr
  refine Ex_mono hp0 hp1 E fun S hS => ?_
  by_cases hP : P S
  · rw [if_pos hP, if_pos (h S hS hP)]
  · rw [if_neg hP]; split_ifs <;> norm_num

omit [DecidableEq β] in
theorem Pr_or_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β) (P Q : Finset β → Prop) :
    Pr p E (fun S => P S ∨ Q S) ≤ Pr p E P + Pr p E Q := by
  classical
  unfold Pr
  rw [← Ex_add]
  refine Ex_mono hp0 hp1 E fun S _ => ?_
  by_cases hP : P S <;> by_cases hQ : Q S <;> simp [hP, hQ]

omit [DecidableEq β] in
/-- The union bound. -/
theorem Pr_exists_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β) {ι : Type*}
    (s : Finset ι) (P : ι → Finset β → Prop) :
    Pr p E (fun S => ∃ i ∈ s, P i S) ≤ ∑ i ∈ s, Pr p E (P i) := by
  classical
  unfold Pr
  rw [← Ex_sum]
  refine Ex_mono hp0 hp1 E fun S _ => ?_
  by_cases h : ∃ i ∈ s, P i S
  · rw [if_pos h]
    obtain ⟨i, hi, hPi⟩ := h
    refine le_trans ?_ (single_le_sum (f := fun j => if P j S then (1 : ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) hi)
    simp [hPi]
  · rw [if_neg h]
    exact sum_nonneg fun j _ => by split_ifs <;> norm_num

/-- First-moment principle: an event of probability `< 1` fails for some outcome. -/
theorem exists_not_of_Pr_lt_one {p : ℝ} (E : Finset β) {P : Finset β → Prop}
    (h : Pr p E P < 1) : ∃ S ⊆ E, ¬ P S := by
  classical
  by_contra hcon
  push_neg at hcon
  have : Pr p E P = 1 := by
    unfold Pr
    rw [Ex_congr p E (g := fun _ => 1) fun S hS => by rw [if_pos (hcon S hS)], Ex_const]
  linarith

omit [DecidableEq β] in
theorem Ex_ite (p : ℝ) (E : Finset β) (P : Finset β → Prop) [DecidablePred P] :
    Ex p E (fun S => if P S then (1 : ℝ) else 0) = Pr p E P := by
  unfold Pr
  refine Ex_congr p E fun S _ => ?_
  by_cases h : P S <;> simp [h]

theorem Pr_insert (p : ℝ) {a : β} {E : Finset β} (ha : a ∉ E) (P : Finset β → Prop) :
    Pr p (insert a E) P = (1 - p) * Pr p E P + p * Pr p E (fun S => P (insert a S)) := by
  unfold Pr; rw [Ex_insert p ha]

omit [DecidableEq β] in
theorem Pr_congr (p : ℝ) (E : Finset β) {P Q : Finset β → Prop} (h : ∀ S ⊆ E, P S ↔ Q S) :
    Pr p E P = Pr p E Q := by
  unfold Pr
  refine Ex_congr p E fun S hS => ?_
  by_cases hP : P S
  · rw [if_pos hP, if_pos ((h S hS).1 hP)]
  · rw [if_neg hP, if_neg (fun hQ => hP ((h S hS).2 hQ))]

theorem Pr_eq_zero (p : ℝ) (E : Finset β) {P : Finset β → Prop} (h : ∀ S ⊆ E, ¬ P S) :
    Pr p E P = 0 := by
  unfold Pr
  rw [Ex_congr p E (g := fun _ => 0) fun S hS => if_neg (h S hS), Ex_const]

/-- The random set avoids a fixed `G ⊆ E` with probability `(1-p)^{|G|}`. -/
theorem Pr_disjoint (p : ℝ) {E G : Finset β} (hG : G ⊆ E) :
    Pr p E (fun S => Disjoint S G) = (1 - p) ^ G.card := by
  induction E using Finset.induction_on generalizing G with
  | empty =>
    rw [subset_empty.1 hG]; simp [Pr, Ex_empty]
  | insert a E ha ih =>
    rw [Pr_insert p ha]
    by_cases haG : a ∈ G
    · have hG' : G.erase a ⊆ E := by
        intro x hx
        rcases mem_insert.1 (hG (mem_of_mem_erase hx)) with h | h
        · exact absurd h (ne_of_mem_erase hx)
        · exact h
      have h1 : Pr p E (fun S => Disjoint S G) = Pr p E (fun S => Disjoint S (G.erase a)) := by
        refine Pr_congr p E fun S hS => ?_
        constructor
        · exact fun h => disjoint_of_subset_right (erase_subset _ _) h
        · intro h
          rw [disjoint_right]
          intro x hx hxS
          by_cases hxa : x = a
          · exact ha (hxa ▸ hS hxS)
          · exact disjoint_right.1 h (mem_erase.2 ⟨hxa, hx⟩) hxS
      have h2 : Pr p E (fun S => Disjoint (insert a S) G) = 0 :=
        Pr_eq_zero p E fun S _ h => disjoint_left.1 h (mem_insert_self a S) haG
      rw [h1, h2, ih hG', card_erase_of_mem haG]
      have hpos : 0 < G.card := card_pos.2 ⟨a, haG⟩
      rw [mul_zero, add_zero, ← pow_succ', Nat.sub_add_cancel hpos]
    · have hG' : G ⊆ E := by
        intro x hx
        rcases mem_insert.1 (hG hx) with h | h
        · exact absurd (h ▸ hx) haG
        · exact h
      have h2 : Pr p E (fun S => Disjoint (insert a S) G) = Pr p E (fun S => Disjoint S G) :=
        Pr_congr p E fun S _ => by simp [disjoint_insert_left, haG]
      rw [h2, ih hG']
      ring

/-- The random set contains a fixed `F ⊆ E` with probability `p^{|F|}`. -/
theorem Pr_subset (p : ℝ) {E F : Finset β} (hF : F ⊆ E) :
    Pr p E (fun S => F ⊆ S) = p ^ F.card := by
  induction E using Finset.induction_on generalizing F with
  | empty =>
    rw [subset_empty.1 hF]; simp [Pr, Ex_empty]
  | insert a E ha ih =>
    rw [Pr_insert p ha]
    by_cases haF : a ∈ F
    · have hF' : F.erase a ⊆ E := by
        intro x hx
        rcases mem_insert.1 (hF (mem_of_mem_erase hx)) with h | h
        · exact absurd h (ne_of_mem_erase hx)
        · exact h
      have h1 : Pr p E (fun S => F ⊆ S) = 0 :=
        Pr_eq_zero p E fun S hS h => ha (hS (h haF))
      have h2 : Pr p E (fun S => F ⊆ insert a S) = Pr p E (fun S => F.erase a ⊆ S) := by
        refine Pr_congr p E fun S _ => ?_
        constructor
        · intro h x hx
          rcases mem_insert.1 (h (mem_of_mem_erase hx)) with h' | h'
          · exact absurd h' (ne_of_mem_erase hx)
          · exact h'
        · intro h x hx
          by_cases hxa : x = a
          · exact hxa ▸ mem_insert_self a S
          · exact mem_insert_of_mem (h (mem_erase.2 ⟨hxa, hx⟩))
      rw [h1, h2, ih hF', card_erase_of_mem haF]
      have hpos : 0 < F.card := card_pos.2 ⟨a, haF⟩
      rw [mul_zero, zero_add, ← pow_succ', Nat.sub_add_cancel hpos]
    · have hF' : F ⊆ E := by
        intro x hx
        rcases mem_insert.1 (hF hx) with h | h
        · exact absurd (h ▸ hx) haF
        · exact h
      have h2 : Pr p E (fun S => F ⊆ insert a S) = Pr p E (fun S => F ⊆ S) := by
        refine Pr_congr p E fun S _ => ?_
        constructor
        · intro h x hx
          rcases mem_insert.1 (h hx) with h' | h'
          · exact absurd (h' ▸ hx) haF
          · exact h'
        · exact fun h => h.trans (subset_insert _ _)
      rw [h2, ih hF']
      ring

/-- Union bound over a family of sets: the probability that the random set contains some
member of `𝓕` is at most `∑_{F ∈ 𝓕} p^{|F|}`. -/
theorem Pr_exists_subset_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {E : Finset β}
    (𝓕 : Finset (Finset β)) (h𝓕 : ∀ F ∈ 𝓕, F ⊆ E) :
    Pr p E (fun S => ∃ F ∈ 𝓕, F ⊆ S) ≤ ∑ F ∈ 𝓕, p ^ F.card := by
  refine (Pr_exists_le hp0 hp1 E 𝓕 (fun F S => F ⊆ S)).trans (le_of_eq ?_)
  exact sum_congr rfl fun F hF => Pr_subset p (h𝓕 F hF)

omit [DecidableEq β] in
/-- Exponential Markov inequality. -/
theorem Pr_ge_le_exp {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β)
    (f : Finset β → ℝ) (t lam : ℝ) (hlam : 0 ≤ lam) :
    Pr p E (fun S => t ≤ f S) ≤
      Real.exp (-(lam * t)) * Ex p E (fun S => Real.exp (lam * f S)) := by
  classical
  unfold Pr
  rw [← Ex_const_mul]
  refine Ex_mono hp0 hp1 E fun S _ => ?_
  split_ifs with h
  · rw [← Real.exp_add]
    exact Real.one_le_exp (by nlinarith)
  · positivity

/-! ### Bernstein-type concentration for bounded differences -/

/-- `f` has differences bounded by `c` with respect to the coins of `E`. -/
def LipOn (E : Finset β) (f : Finset β → ℝ) (c : β → ℝ) : Prop :=
  ∀ a ∈ E, ∀ S ⊆ E, |f (insert a S) - f (S.erase a)| ≤ c a

theorem bernoulli_mgf_le {p x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx : |x| ≤ 1) :
    (1 - p) * Real.exp (-(p * x)) + p * Real.exp ((1 - p) * x) ≤ Real.exp (p * x ^ 2) := by
  have hx' := abs_le.1 hx
  have hq : 0 ≤ 1 - p := by linarith
  have h1 : |-(p * x)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have h2 : |(1 - p) * x| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have e1' := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le h1)).2
  have e2' := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le h2)).2
  have a1 : (1 - p) * Real.exp (-(p * x)) ≤ (1 - p) * (1 + -(p * x) + (-(p * x)) ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hq
  have a2 : p * Real.exp ((1 - p) * x) ≤ p * (1 + (1 - p) * x + ((1 - p) * x) ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hp0
  have : (1 - p) * Real.exp (-(p * x)) + p * Real.exp ((1 - p) * x) ≤ 1 + p * x ^ 2 := by
    nlinarith [sq_nonneg x, mul_nonneg hp0 hq, mul_nonneg (mul_nonneg hp0 hq) (sq_nonneg x),
      mul_nonneg (mul_nonneg hp0 hp0) (sq_nonneg x)]
  exact this.trans (by linarith [Real.add_one_le_exp (p * x ^ 2)])

/-- **Exponential moment bound** for functions with bounded differences of the `p`-random
subset: `E[e^{λ(f - Ef)}] ≤ exp(λ² p ∑ c_a²)` whenever `|λ| c_a ≤ 1` for every coin. -/
theorem Ex_exp_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β) (f : Finset β → ℝ)
    (c : β → ℝ) (lam : ℝ) (hc : ∀ a ∈ E, |lam| * c a ≤ 1) (hf : LipOn E f c) :
    Ex p E (fun S => Real.exp (lam * (f S - Ex p E f))) ≤
      Real.exp (lam ^ 2 * p * ∑ a ∈ E, c a ^ 2) := by
  induction E using Finset.induction_on generalizing f with
  | empty => simp [Ex_empty]
  | insert a E ha ih =>
    set g1 : Finset β → ℝ := fun S => f (insert a S) with hg1
    have hLip0 : LipOn E f c := fun b hb S hS =>
      hf b (mem_insert_of_mem hb) S (hS.trans (subset_insert _ _))
    have hLip1 : LipOn E g1 c := by
      intro b hb S hS
      have hab : a ≠ b := fun h => ha (h ▸ hb)
      have h1 : insert a (insert b S) = insert b (insert a S) := insert_comm _ _ _
      have h2 : insert a (S.erase b) = (insert a S).erase b := (erase_insert_of_ne hab).symm
      simp only [hg1, h1, h2]
      exact hf b (mem_insert_of_mem hb) (insert a S) (insert_subset_insert _ hS)
    have hc' : ∀ b ∈ E, |lam| * c b ≤ 1 := fun b hb => hc b (mem_insert_of_mem hb)
    set μ0 := Ex p E f
    set μ1 := Ex p E g1
    set B := Real.exp (lam ^ 2 * p * ∑ b ∈ E, c b ^ 2)
    have hμ : Ex p (insert a E) f = (1 - p) * μ0 + p * μ1 := Ex_insert p ha f
    set d := μ1 - μ0
    have hd : |d| ≤ c a := by
      have : d = Ex p E (fun S => g1 S - f S) := by rw [Ex_sub]
      rw [this]
      refine abs_Ex_le hp0 hp1 E fun S hS => ?_
      have haS : a ∉ S := fun h => ha (hS h)
      have := hf a (mem_insert_self a E) S (hS.trans (subset_insert _ _))
      rwa [erase_eq_of_notMem haS] at this
    rw [Ex_insert p ha, hμ]
    have hI0 : Ex p E (fun S => Real.exp (lam * (f S - ((1 - p) * μ0 + p * μ1)))) =
        Real.exp (lam * (-(p * d))) * Ex p E (fun S => Real.exp (lam * (f S - μ0))) := by
      conv_rhs => rw [← Ex_const_mul]
      refine Ex_congr p E fun S _ => ?_
      rw [← Real.exp_add]; congr 1; simp only [d]; ring
    have hI1 : Ex p E (fun S => Real.exp (lam * (f (insert a S) - ((1 - p) * μ0 + p * μ1)))) =
        Real.exp (lam * ((1 - p) * d)) * Ex p E (fun S => Real.exp (lam * (g1 S - μ1))) := by
      conv_rhs => rw [← Ex_const_mul]
      refine Ex_congr p E fun S _ => ?_
      rw [← Real.exp_add]; congr 1; simp only [d, hg1]; ring
    rw [hI0, hI1]
    have hB0 := ih f hc' hLip0
    have hB1 := ih g1 hc' hLip1
    have hq : 0 ≤ 1 - p := by linarith
    have hx : |lam * d| ≤ 1 := by
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_left hd (abs_nonneg _)) (hc a (mem_insert_self a E))
    have hmgf := bernoulli_mgf_le hp0 hp1 hx
    have hsq : p * (lam * d) ^ 2 ≤ lam ^ 2 * p * c a ^ 2 := by
      have : d ^ 2 ≤ c a ^ 2 := sq_le_sq' (abs_le.1 hd).1 (abs_le.1 hd).2
      nlinarith [sq_nonneg lam, mul_nonneg hp0 (sq_nonneg lam)]
    calc (1 - p) * (Real.exp (lam * (-(p * d))) * Ex p E (fun S => Real.exp (lam * (f S - μ0))))
          + p * (Real.exp (lam * ((1 - p) * d)) * Ex p E (fun S => Real.exp (lam * (g1 S - μ1))))
        ≤ (1 - p) * (Real.exp (lam * (-(p * d))) * B)
          + p * (Real.exp (lam * ((1 - p) * d)) * B) := by
          gcongr
      _ = B * ((1 - p) * Real.exp (-(p * (lam * d))) + p * Real.exp ((1 - p) * (lam * d))) := by
          ring_nf
      _ ≤ B * Real.exp (p * (lam * d) ^ 2) := by gcongr
      _ ≤ B * Real.exp (lam ^ 2 * p * c a ^ 2) := by gcongr
      _ = Real.exp (lam ^ 2 * p * ∑ b ∈ insert a E, c b ^ 2) := by
          rw [sum_insert ha, ← Real.exp_add]; ring_nf

/-- **Upper tail** for bounded differences. -/
theorem Pr_ge_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β) (f : Finset β → ℝ)
    (c : β → ℝ) (hf : LipOn E f c) (t lam : ℝ) (hlam : 0 ≤ lam) (hc : ∀ a ∈ E, lam * c a ≤ 1) :
    Pr p E (fun S => Ex p E f + t ≤ f S) ≤
      Real.exp (-(lam * t) + lam ^ 2 * p * ∑ a ∈ E, c a ^ 2) := by
  have h1 := Pr_ge_le_exp hp0 hp1 E (fun S => f S - Ex p E f) t lam hlam
  have h2 := Ex_exp_le hp0 hp1 E f c lam
    (fun a ha => by rw [abs_of_nonneg hlam]; exact hc a ha) hf
  calc Pr p E (fun S => Ex p E f + t ≤ f S)
      = Pr p E (fun S => t ≤ f S - Ex p E f) := by
        unfold Pr; refine Ex_congr p E fun S _ => ?_
        simp only [show (Ex p E f + t ≤ f S) ↔ (t ≤ f S - Ex p E f) from by
          constructor <;> intro h <;> linarith]
    _ ≤ Real.exp (-(lam * t)) * Ex p E (fun S => Real.exp (lam * (f S - Ex p E f))) := h1
    _ ≤ Real.exp (-(lam * t)) * Real.exp (lam ^ 2 * p * ∑ a ∈ E, c a ^ 2) := by gcongr
    _ = _ := by rw [← Real.exp_add]

/-- **Lower tail** for bounded differences. -/
theorem Pr_le_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β) (f : Finset β → ℝ)
    (c : β → ℝ) (hf : LipOn E f c) (t lam : ℝ) (hlam : 0 ≤ lam) (hc : ∀ a ∈ E, lam * c a ≤ 1) :
    Pr p E (fun S => f S ≤ Ex p E f - t) ≤
      Real.exp (-(lam * t) + lam ^ 2 * p * ∑ a ∈ E, c a ^ 2) := by
  have hf' : LipOn E (fun S => -f S) c := fun a ha S hS => by
    have := hf a ha S hS
    rw [show -f (insert a S) - -f (S.erase a) = -(f (insert a S) - f (S.erase a)) by ring,
      abs_neg]
    exact this
  have := Pr_ge_le hp0 hp1 E (fun S => -f S) c hf' t lam hlam hc
  rw [Ex_neg] at this
  refine le_trans (le_of_eq ?_) this
  unfold Pr; refine Ex_congr p E fun S _ => ?_
  simp only [show (f S ≤ Ex p E f - t) ↔ (-Ex p E f + t ≤ -f S) from by
    constructor <;> intro h <;> linarith]

end RefinedAbsorption.Nibble
