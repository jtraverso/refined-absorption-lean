module
public import RequestProject.Nibble.FiniteProb
public import RequestProject.Sharp.SparsCount

/-!
# Quasi-random partitions (Proposition 3.17)

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Proposition 3.17.

A uniformly random map `φ : V → Fin k` has, for every fixed part `i`, the part
`U ∩ φ⁻¹(i)` distributed as a `1/k`-random subset of `U` (`card_filter_fibre`).  With the
Bernstein inequality of `Nibble/FiniteProb.lean` and the union bound over the parts and the
`(r-1)`-sets we obtain (**`exists_partition`**): if

`k · (exp(-|U|/(4k)) + |U|^{r-1} · exp(-D*/(4 M₀ k))) < 1`,

then for every `r`-multigraph `X` inside `U` with multiplicity `≤ M₀` and `Δ_{r-1}(X) ≤ D ≤ D*`
there is a partition of the vertices into `k` parts such that every part meets `U` in at most
`2|U|/k` vertices and, for every `(r-1)`-set `S` and part `i`, at most `2D*/k` copies consist of
`S` and a vertex of part `i`.
-/

@[expose] public section

namespace RefinedAbsorption.Sharp

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Nibble

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The part `i` of `φ` inside `U`. -/
def fib {k : ℕ} (U : Finset V) (φ : V → Fin k) (i : Fin k) : Finset V := U.filter fun v => φ v = i

/-- Number of maps with a prescribed part `i` inside `U`. -/
theorem card_fib_eq {k : ℕ} (U A : Finset V) (hAU : A ⊆ U) (i : Fin k) :
    ((univ : Finset (V → Fin k)).filter fun φ => fib U φ i = A).card =
      (k - 1) ^ (U.card - A.card) * k ^ (Fintype.card V - U.card) := by
  classical
  set s : V → Finset (Fin k) := fun v =>
    if v ∈ A then {i} else if v ∈ U then univ.erase i else univ with hs
  have hfilt : (univ : Finset (V → Fin k)).filter (fun φ => fib U φ i = A) =
      Fintype.piFinset s := by
    ext φ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, hs]
    constructor
    · intro h v
      have hv : v ∈ fib U φ i ↔ v ∈ A := by rw [h]
      unfold fib at hv
      rw [mem_filter] at hv
      split_ifs with h1 h2
      · exact mem_singleton.2 (hv.2 h1).2
      · exact mem_erase.2 ⟨fun he => h1 (hv.1 ⟨h2, he⟩), mem_univ _⟩
      · exact mem_univ _
    · intro h
      ext v
      unfold fib
      rw [mem_filter]
      have hv := h v
      constructor
      · rintro ⟨hvU, hvi⟩
        by_contra hvA
        rw [if_neg hvA, if_pos hvU] at hv
        exact (mem_erase.1 hv).1 hvi
      · intro hvA
        rw [if_pos hvA] at hv
        exact ⟨hAU hvA, mem_singleton.1 hv⟩
  rw [hfilt, Fintype.card_piFinset]
  have hval : ∀ v, (s v).card =
      if v ∈ A then 1 else if v ∈ U then k - 1 else k := by
    intro v
    simp only [hs]
    split_ifs
    · rfl
    · rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    · rw [card_univ, Fintype.card_fin]
  simp only [hval]
  rw [prod_ite, prod_const_one, one_mul, prod_ite, prod_const, prod_const]
  have e1 : ((univ.filter fun v => v ∉ A).filter fun v => v ∈ U) = U \ A := by
    ext v; simp only [mem_filter, mem_univ, true_and, mem_sdiff]; tauto
  have e2 : ((univ.filter fun v => v ∉ A).filter fun v => v ∉ U) = Uᶜ := by
    ext v; simp only [mem_filter, mem_univ, true_and, mem_compl]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨fun hA => h (hAU hA), h⟩
  rw [e1, e2, card_sdiff_of_subset hAU, card_compl]

/-- **The parts of a uniform random map are `1/k`-random subsets.**  The number of maps whose
part `i` inside `U` satisfies `Pd` is `k^{|V|} · Pr_{1/k}(Pd)`. -/
theorem card_filter_fib {k : ℕ} (hk : 1 ≤ k) (U : Finset V) (i : Fin k)
    (Pd : Finset V → Prop) [DecidablePred Pd] :
    (((univ : Finset (V → Fin k)).filter fun φ => Pd (fib U φ i)).card : ℝ) =
      (k : ℝ) ^ Fintype.card V * Pr (1 / (k : ℝ)) U Pd := by
  have hfib : ∀ φ ∈ (univ : Finset (V → Fin k)).filter (fun φ => Pd (fib U φ i)),
      fib U φ i ∈ U.powerset.filter Pd := by
    intro φ hφ
    rw [mem_filter] at hφ ⊢
    exact ⟨mem_powerset.2 (filter_subset _ _), hφ.2⟩
  rw [card_eq_sum_card_fiberwise hfib]
  unfold Pr Ex
  rw [Nat.cast_sum, mul_sum, sum_filter]
  refine sum_congr rfl fun A hA => ?_
  have hAU := mem_powerset.1 hA
  split_ifs with hPA
  · have hset : ((univ : Finset (V → Fin k)).filter fun φ => Pd (fib U φ i)).filter
        (fun φ => fib U φ i = A) = (univ : Finset (V → Fin k)).filter fun φ => fib U φ i = A := by
      ext φ
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hPA, h⟩
    rw [hset, card_fib_eq U A hAU i]
    simp only [hPA, if_true, mul_one]
    unfold wt
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hUV : U.card ≤ Fintype.card V := card_le_univ U
    have hAU' : A.card ≤ U.card := card_le_card hAU
    push_cast
    rw [Nat.cast_sub hk, Nat.cast_one]
    have e1 : (k : ℝ) ^ Fintype.card V =
        (k : ℝ) ^ (Fintype.card V - U.card) * (k : ℝ) ^ A.card * (k : ℝ) ^ (U.card - A.card) := by
      rw [mul_assoc, ← pow_add, ← pow_add]; congr 1; omega
    have e2 : (1 - 1 / (k : ℝ)) = ((k : ℝ) - 1) / k := by field_simp
    rw [e1, e2, div_pow, div_pow, one_pow]
    field_simp
  · simp [hPA]

/-- **Union bound over parts and constraints.** -/
theorem exists_good_map {k : ℕ} (hk : 1 ≤ k) (U : Finset V) {ι : Type*} (Cs : Finset ι)
    (Bad : ι → Finset V → Prop) [∀ j, DecidablePred (Bad j)]
    (h : ∑ j ∈ Cs, (k : ℝ) * Pr (1 / (k : ℝ)) U (Bad j) < 1) :
    ∃ φ : V → Fin k, ∀ j ∈ Cs, ∀ i, ¬ Bad j (fib U φ i) := by
  by_contra hcon
  push_neg at hcon
  have hall : (univ : Finset (V → Fin k)) ⊆ Cs.biUnion fun j => (univ : Finset (Fin k)).biUnion
      fun i => (univ : Finset (V → Fin k)).filter fun φ => Bad j (fib U φ i) := by
    intro φ _
    obtain ⟨j, hj, i, hi⟩ := hcon φ
    exact mem_biUnion.2 ⟨j, hj, mem_biUnion.2 ⟨i, mem_univ _, mem_filter.2 ⟨mem_univ _, hi⟩⟩⟩
  have h1 := card_le_card hall
  have h2 : ((Cs.biUnion fun j => (univ : Finset (Fin k)).biUnion fun i =>
      (univ : Finset (V → Fin k)).filter fun φ => Bad j (fib U φ i)).card : ℝ) ≤
      ∑ j ∈ Cs, (k : ℝ) * ((k : ℝ) ^ Fintype.card V * Pr (1 / (k : ℝ)) U (Bad j)) := by
    refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    refine sum_le_sum fun j _ => ?_
    refine (Nat.cast_le.2 card_biUnion_le).trans ?_
    push_cast
    simp only [card_filter_fib hk, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_rfl
  have hcard : ((univ : Finset (V → Fin k)).card : ℝ) = (k : ℝ) ^ Fintype.card V := by
    rw [card_univ, Fintype.card_fun, Fintype.card_fin]; push_cast; rfl
  have hk0 : (0 : ℝ) < (k : ℝ) ^ Fintype.card V := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have h3 : ∑ j ∈ Cs, (k : ℝ) * ((k : ℝ) ^ Fintype.card V * Pr (1 / (k : ℝ)) U (Bad j)) =
      (k : ℝ) ^ Fintype.card V * ∑ j ∈ Cs, (k : ℝ) * Pr (1 / (k : ℝ)) U (Bad j) := by
    rw [mul_sum]; refine sum_congr rfl fun j _ => by ring
  have h4 : ((univ : Finset (V → Fin k)).card : ℝ) ≤
      (k : ℝ) ^ Fintype.card V * ∑ j ∈ Cs, (k : ℝ) * Pr (1 / (k : ℝ)) U (Bad j) := by
    rw [← h3]; exact (Nat.cast_le.2 h1).trans h2
  rw [hcard] at h4
  have : (k : ℝ) ^ Fintype.card V * ∑ j ∈ Cs, (k : ℝ) * Pr (1 / (k : ℝ)) U (Bad j) <
      (k : ℝ) ^ Fintype.card V := by
    calc _ < (k : ℝ) ^ Fintype.card V * 1 := mul_lt_mul_of_pos_left h hk0
      _ = _ := mul_one _
  linarith

/-! ### Bernstein for weighted sums -/

omit [Fintype V] in
theorem Ex_wsum {p : ℝ} (U : Finset V) (w : V → ℝ) :
    Ex p U (fun A => ∑ v ∈ A, w v) = p * ∑ v ∈ U, w v := by
  rw [Ex_congr p U (g := fun A => ∑ v ∈ U, (if v ∈ A then w v else 0)) fun A hA => by
    show ∑ v ∈ A, w v = ∑ v ∈ U, (if v ∈ A then w v else 0)
    rw [sum_ite_mem, inter_eq_right.2 hA]]
  rw [Ex_sum, mul_sum]
  refine sum_congr rfl fun v hv => ?_
  have : Ex p U (fun A => if v ∈ A then w v else 0) =
      w v * Ex p U (fun A => if ({v} : Finset V) ⊆ A then (1 : ℝ) else 0) := by
    rw [← Ex_const_mul]
    refine Ex_congr p U fun A _ => ?_
    simp only [singleton_subset_iff]
    split_ifs <;> simp
  rw [this, Ex_ite, Pr_subset p (singleton_subset_iff.2 hv), card_singleton, pow_one, mul_comm]

omit [Fintype V] in
/-- **Bernstein bound for a weighted sum over a `p`-random subset.** -/
theorem Pr_wsum_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (U : Finset V) (w : V → ℝ)
    (hw0 : ∀ v ∈ U, 0 ≤ w v) {Mw : ℝ} (hMw : 0 < Mw) (hwM : ∀ v ∈ U, w v ≤ Mw) (t : ℝ) :
    Pr p U (fun A => p * ∑ v ∈ U, w v + t ≤ ∑ v ∈ A, w v) ≤
      Real.exp (-(t / (2 * Mw)) + p * (∑ v ∈ U, w v) / (4 * Mw)) := by
  have hlip : LipOn U (fun A => ∑ v ∈ A, w v) w := by
    intro a ha S hS
    have hins : insert a S = insert a (S.erase a) := by
      ext x; by_cases hx : x = a <;> simp [hx]
    show |∑ v ∈ insert a S, w v - ∑ v ∈ S.erase a, w v| ≤ w a
    rw [hins, sum_insert (notMem_erase a S), add_sub_cancel_right, abs_of_nonneg (hw0 a ha)]
  have hlam : (0 : ℝ) ≤ 1 / (2 * Mw) := by positivity
  have hc : ∀ a ∈ U, 1 / (2 * Mw) * w a ≤ 1 := by
    intro a ha
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith [hwM a ha, hw0 a ha]
  have h := Pr_ge_le hp0 hp1 U (fun A => ∑ v ∈ A, w v) w hlip t (1 / (2 * Mw)) hlam hc
  rw [Ex_wsum] at h
  refine h.trans (Real.exp_le_exp.2 ?_)
  have hsq : ∑ a ∈ U, w a ^ 2 ≤ Mw * ∑ a ∈ U, w a := by
    rw [mul_sum]
    refine sum_le_sum fun a ha => ?_
    rw [sq]; exact mul_le_mul_of_nonneg_right (hwM a ha) (hw0 a ha)
  have e1 : 1 / (2 * Mw) * t = t / (2 * Mw) := by ring
  rw [e1]
  have : (1 / (2 * Mw)) ^ 2 * p * ∑ a ∈ U, w a ^ 2 ≤ p * (∑ v ∈ U, w v) / (4 * Mw) := by
    calc (1 / (2 * Mw)) ^ 2 * p * ∑ a ∈ U, w a ^ 2
        ≤ (1 / (2 * Mw)) ^ 2 * p * (Mw * ∑ a ∈ U, w a) := by gcongr
      _ = p * (∑ v ∈ U, w v) / (4 * Mw) := by field_simp; ring
  linarith

/-! ### The partition of Proposition 3.17 -/

section Degrees

variable {E : Type} [DecidableEq E]

/-- The copies consisting of `S` and one more vertex `v` with `Q v`, counted through the
multiplicities of the sets `S ∪ {v}`. -/
theorem card_split_eq {r : ℕ} {ends : E → Finset V} {X : Finset E} {U : Finset V}
    (hXr : MIsRGraph r ends X) (hXU : ∀ x ∈ X, ends x ⊆ U) {S : Finset V} (hS : S.card = r - 1)
    (hr : 1 ≤ r) (Q : V → Prop) [DecidablePred Q] :
    (X.filter fun x => S ⊆ ends x ∧ ∀ v ∈ ends x \ S, Q v).card =
      ∑ v ∈ U.filter Q, (X.filter fun x => v ∉ S ∧ ends x = insert v S).card := by
  rw [← card_biUnion]
  · congr 1
    ext x
    simp only [mem_filter, mem_biUnion]
    constructor
    · rintro ⟨hx, hSx, hQ⟩
      have hc : (ends x \ S).card = 1 := by rw [card_sdiff_of_subset hSx, hXr x hx, hS]; omega
      obtain ⟨v, hv⟩ := card_eq_one.1 hc
      have hvx : v ∈ ends x \ S := by rw [hv]; exact mem_singleton_self v
      refine ⟨v, ⟨hXU x hx (mem_sdiff.1 hvx).1, hQ v hvx⟩, hx, (mem_sdiff.1 hvx).2, ?_⟩
      rw [← sdiff_union_of_subset hSx, hv]; rfl
    · rintro ⟨v, ⟨-, hQv⟩, hx, hvS, he⟩
      refine ⟨hx, by rw [he]; exact subset_insert v S, fun u hu => ?_⟩
      rw [he, mem_sdiff, mem_insert] at hu
      rcases hu.1 with rfl | h
      · exact hQv
      · exact absurd h hu.2
  · intro v _ v' _ hvv'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro x hx hx'
    rw [mem_filter] at hx hx'
    have : v ∈ insert v' S := by rw [← hx'.2.2, hx.2.2]; exact mem_insert_self v S
    rcases mem_insert.1 this with h | h
    · exact hvv' h
    · exact hx.2.1 h

/-- The weight of `v` for the `(r-1)`-set `S`: the multiplicity of `S ∪ {v}` (zero on `S`). -/
def wS (ends : E → Finset V) (X : Finset E) (S : Finset V) (v : V) : ℕ :=
  (X.filter fun x => v ∉ S ∧ ends x = insert v S).card

omit [Fintype V] [DecidableEq E] in
theorem wS_le {ends : E → Finset V} {X : Finset E} {M₀ : ℕ}
    (hmult : ∀ e, mult ends X e ≤ M₀) (S : Finset V) (v : V) : wS ends X S v ≤ M₀ :=
  (card_le_card (monotone_filter_right _ fun _ _ h => h.2)).trans (hmult _)

/-- **Quasi-random partition** (Proposition 3.17); see the module docstring. -/
theorem exists_partition (ends : E → Finset V) (X : Finset E) (U : Finset V) {r k M₀ D : ℕ}
    (hr : 1 ≤ r) (hk : 1 ≤ k) (hM₀ : 1 ≤ M₀) (hXr : MIsRGraph r ends X)
    (hXU : ∀ x ∈ X, ends x ⊆ U) (hmult : ∀ e, mult ends X e ≤ M₀)
    (hdeg : ∀ S : Finset V, S.card = r - 1 → mdeg ends X S ≤ D) (Dst : ℝ) (hDst : (D : ℝ) ≤ Dst)
    (hunion : (k : ℝ) * (Real.exp (-((U.card : ℝ) / (4 * k))) +
      (U.card : ℝ) ^ (r - 1) * Real.exp (-(Dst / (4 * M₀ * k)))) < 1) :
    ∃ φ : V → Fin k, (∀ i, ((U.filter fun v => φ v = i).card : ℝ) ≤ 2 * U.card / k) ∧
      ∀ S : Finset V, S.card = r - 1 → ∀ i,
        ((X.filter fun x => S ⊆ ends x ∧ ∀ v ∈ ends x \ S, φ v = i).card : ℝ) ≤ 2 * Dst / k := by
  classical
  set m := U.card with hm
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set p : ℝ := 1 / (k : ℝ) with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hk0]; exact_mod_cast hk
  have hM0 : (0 : ℝ) < M₀ := by exact_mod_cast hM₀
  have hD0 : (0 : ℝ) ≤ Dst := le_trans (Nat.cast_nonneg _) hDst
  set Bad : Option (Finset V) → Finset V → Prop := fun j A =>
    match j with
    | none => 2 * (m : ℝ) / k < (A.card : ℝ)
    | some S => 2 * Dst / k < ∑ v ∈ A, (wS ends X S v : ℝ) with hBad
  set Cs : Finset (Option (Finset V)) := insert none ((U.powersetCard (r - 1)).image some)
    with hCs
  -- the size event
  have hPnone : (k : ℝ) * Pr p U (Bad none) ≤ (k : ℝ) * Real.exp (-((m : ℝ) / (4 * k))) := by
    refine mul_le_mul_of_nonneg_left ?_ hk0.le
    have h1 : Pr p U (Bad none) ≤
        Pr p U (fun A => p * ∑ v ∈ U, (1 : ℝ) + (m : ℝ) / k ≤ ∑ v ∈ A, (1 : ℝ)) := by
      refine Pr_mono hp0 hp1 U fun A _ hA => ?_
      simp only [hBad] at hA
      simp only [sum_const, nsmul_eq_mul, mul_one, hp]
      rw [← hm]
      have : (m : ℝ) / k + m / k = 2 * m / k := by ring
      linarith [show (1 / (k : ℝ)) * m = m / k by ring]
    refine h1.trans ((Pr_wsum_le hp0 hp1 U (fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
      one_pos (fun _ _ => le_rfl) _).trans (Real.exp_le_exp.2 (le_of_eq ?_)))
    simp only [sum_const, nsmul_eq_mul, mul_one, hp, ← hm]
    field_simp
    ring
  -- the degree events
  have hPsome : ∀ S ∈ U.powersetCard (r - 1),
      (k : ℝ) * Pr p U (Bad (some S)) ≤ (k : ℝ) * Real.exp (-(Dst / (4 * M₀ * k))) := by
    intro S hS
    have hSc := (mem_powersetCard.1 hS).2
    refine mul_le_mul_of_nonneg_left ?_ hk0.le
    set w : V → ℝ := fun v => (wS ends X S v : ℝ) with hw
    have hsumU : ∑ v ∈ U, w v ≤ D := by
      have := card_split_eq hXr hXU hSc hr (fun _ => True)
      have h3 : (X.filter fun x => S ⊆ ends x ∧ ∀ v ∈ ends x \ S, True) =
          X.filter (fun x => S ⊆ ends x) := filter_congr fun x _ => by simp
      have h4 : U.filter (fun _ => True) = U := filter_true_of_mem (fun _ _ => trivial)
      rw [h3, h4] at this
      have h2 : ∑ v ∈ U, w v = (mdeg ends X S : ℝ) := by
        unfold mdeg; rw [this]; push_cast; rfl
      rw [h2]; exact_mod_cast hdeg S hSc
    have h1 : Pr p U (Bad (some S)) ≤
        Pr p U (fun A => p * ∑ v ∈ U, w v + Dst / k ≤ ∑ v ∈ A, w v) := by
      refine Pr_mono hp0 hp1 U fun A _ hA => ?_
      simp only [hBad] at hA
      have : p * ∑ v ∈ U, w v ≤ Dst / k := by
        rw [hp, one_div_mul_eq_div]
        exact div_le_div_of_nonneg_right (hsumU.trans hDst) hk0.le
      have e : (2 * Dst / k) = Dst / k + Dst / k := by ring
      linarith
    refine h1.trans ((Pr_wsum_le hp0 hp1 U w (fun _ _ => Nat.cast_nonneg _) hM0
      (fun v _ => by simp only [hw]; exact_mod_cast wS_le hmult S v) _).trans (Real.exp_le_exp.2 ?_))
    have : p * (∑ v ∈ U, w v) / (4 * M₀) ≤ Dst / k / (4 * M₀) := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      rw [hp, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right (hsumU.trans hDst) hk0.le
    have e1 : Dst / k / (2 * M₀) = Dst / (4 * M₀ * k) + Dst / (4 * M₀ * k) := by
      field_simp; ring
    have e2 : Dst / k / (4 * M₀) = Dst / (4 * M₀ * k) := by field_simp
    linarith
  -- the union bound
  have hsum : ∑ j ∈ Cs, (k : ℝ) * Pr p U (Bad j) < 1 := by
    rw [hCs, sum_insert (by simp), sum_image (fun a _ b _ h => Option.some_injective _ h)]
    have h2 : ∑ S ∈ U.powersetCard (r - 1), (k : ℝ) * Pr p U (Bad (some S)) ≤
        (m : ℝ) ^ (r - 1) * ((k : ℝ) * Real.exp (-(Dst / (4 * M₀ * k)))) := by
      refine (sum_le_sum hPsome).trans ?_
      rw [sum_const, card_powersetCard, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast Nat.choose_le_pow _ _
    calc (k : ℝ) * Pr p U (Bad none) + ∑ S ∈ U.powersetCard (r - 1), (k : ℝ) * Pr p U (Bad (some S))
        ≤ (k : ℝ) * Real.exp (-((m : ℝ) / (4 * k))) +
            (m : ℝ) ^ (r - 1) * ((k : ℝ) * Real.exp (-(Dst / (4 * M₀ * k)))) := add_le_add hPnone h2
      _ = (k : ℝ) * (Real.exp (-((m : ℝ) / (4 * k))) +
            (m : ℝ) ^ (r - 1) * Real.exp (-(Dst / (4 * M₀ * k)))) := by ring
      _ < 1 := hunion
  obtain ⟨φ, hφ⟩ := exists_good_map hk U Cs Bad hsum
  refine ⟨φ, fun i => ?_, fun S hS i => ?_⟩
  · have := hφ none (mem_insert_self _ _) i
    simp only [hBad, not_lt] at this
    exact this
  · by_cases hSU : S ⊆ U
    · have := hφ (some S) (mem_insert_of_mem (mem_image_of_mem _
        (mem_powersetCard.2 ⟨hSU, hS⟩))) i
      simp only [hBad, not_lt] at this
      rw [card_split_eq hXr hXU hS hr (fun v => φ v = i)]
      push_cast
      exact this
    · have : (X.filter fun x => S ⊆ ends x ∧ ∀ v ∈ ends x \ S, φ v = i) = ∅ := by
        rw [filter_eq_empty_iff]
        intro x hx h
        exact hSU (h.1.trans (hXU x hx))
      rw [this, card_empty, Nat.cast_zero]
      positivity

end Degrees

end RefinedAbsorption.Sharp
