module
public import RequestProject.Original2024.Defs
public import RequestProject.Boost
public import RequestProject.ExistenceProof
public import RequestProject.Nibble.FiniteProb

/-!
# Reserves inside a dense host graph

`relWeakReserves`: for `q > r ≥ 1` and `α > 0` there are `ε, δ > 0` such that for all large `n`,
every `r`-graph `G` on `n` vertices with `δ_{r-1}(G) ≥ (1 - ε) n` contains `X ⊆ G` with
`Δ_{r-1}(X) ≤ n^{1-δ}` such that every edge `e ∈ G` lies in at least `n^{q-r-α}` copies of
`K_q^r` in `X ∪ {e}`.

`X` is a `p`-random subset of `G` with `p = n^{-δ}`.  The cliques of `G` through an edge are
counted with the boost lemma; the concentration comes from the bounded-differences inequality of
`Nibble/FiniteProb.lean`.
-/

@[expose] public section

namespace RefinedAbsorption.Original2024

open Finset RefinedAbsorption.Nibble

section Counting

variable {n : ℕ}

/-- The copies of `K_q^r` in `G` containing the edge `e`. -/
def cliquesThrough (q r : ℕ) (G : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (cliquesOf q r G).filter (fun Q => e ⊆ Q)

/-- The number of cliques of `G` through `e` all of whose other edges lie in `S`. -/
noncomputable def resCount (q r : ℕ) (G : Finset (Finset (Fin n))) (e : Finset (Fin n))
    (S : Finset (Finset (Fin n))) : ℝ :=
  (((cliquesThrough q r G e).filter (fun Q => (cliqueEdges r Q).erase e ⊆ S)).card : ℝ)

/-- The Lipschitz constant of `resCount` in the coin `a`. -/
noncomputable def resLip (q r : ℕ) (G : Finset (Finset (Fin n))) (e : Finset (Fin n))
    (a : Finset (Fin n)) : ℝ :=
  (((cliquesThrough q r G e).filter (fun Q => a ∈ (cliqueEdges r Q).erase e)).card : ℝ)

theorem resCount_le_reserve (q r : ℕ) (G : Finset (Finset (Fin n))) (e : Finset (Fin n))
    (S : Finset (Finset (Fin n))) :
    resCount q r G e S ≤ (reserveCliques q r S e).card := by
  unfold resCount
  refine Nat.cast_le.2 (card_le_card ?_)
  intro Q hQ
  simp only [cliquesThrough, cliquesOf, mem_filter] at hQ
  obtain ⟨⟨⟨hQq, -⟩, heQ⟩, hsub⟩ := hQ
  refine mem_filter.2 ⟨hQq, heQ, fun f hf hfe => hsub (mem_erase.2 ⟨hfe, hf⟩)⟩

theorem mem_cliqueEdges_of {r : ℕ} {e Q : Finset (Fin n)} (he : e.card = r) (heQ : e ⊆ Q) :
    e ∈ cliqueEdges r Q := mem_powersetCard.2 ⟨heQ, he⟩

theorem card_erase_cliqueEdges {q r : ℕ} {e Q : Finset (Fin n)} (he : e.card = r) (heQ : e ⊆ Q)
    (hQ : Q.card = q) : ((cliqueEdges r Q).erase e).card = q.choose r - 1 := by
  rw [card_erase_of_mem (mem_cliqueEdges_of he heQ), cliqueEdges, card_powersetCard, hQ]

/-- The expected reserve count. -/
theorem Ex_resCount {q r : ℕ} (p : ℝ) (G : Finset (Finset (Fin n))) {e : Finset (Fin n)}
    (he : e.card = r) :
    Ex p G (resCount q r G e) = (cliquesThrough q r G e).card * p ^ (q.choose r - 1) := by
  classical
  have h1 : ∀ S, resCount q r G e S = ∑ Q ∈ cliquesThrough q r G e,
      (if (cliqueEdges r Q).erase e ⊆ S then (1 : ℝ) else 0) := by
    intro S
    unfold resCount
    rw [card_filter]; push_cast; rfl
  rw [Ex_congr p G (g := fun S => ∑ Q ∈ cliquesThrough q r G e,
      (if (cliqueEdges r Q).erase e ⊆ S then (1 : ℝ) else 0)) (fun S _ => h1 S), Ex_sum]
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_congr rfl fun Q hQ => ?_
  simp only [cliquesThrough, cliquesOf, mem_filter, mem_powersetCard] at hQ
  obtain ⟨⟨⟨-, hQq⟩, hQG⟩, heQ⟩ := hQ
  rw [Ex_ite, Pr_subset p ((erase_subset _ _).trans hQG), card_erase_cliqueEdges he heQ hQq]

theorem lipOn_resCount (q r : ℕ) (G : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    LipOn G (resCount q r G e) (resLip q r G e) := by
  classical
  intro a _ S _
  unfold resCount resLip
  set T := cliquesThrough q r G e
  have hsub : T.filter (fun Q => (cliqueEdges r Q).erase e ⊆ S.erase a) ⊆
      T.filter (fun Q => (cliqueEdges r Q).erase e ⊆ insert a S) := by
    intro Q hQ
    rw [mem_filter] at hQ ⊢
    exact ⟨hQ.1, hQ.2.trans ((erase_subset _ _).trans (subset_insert _ _))⟩
  have hdiff : T.filter (fun Q => (cliqueEdges r Q).erase e ⊆ insert a S) ⊆
      T.filter (fun Q => (cliqueEdges r Q).erase e ⊆ S.erase a) ∪
        T.filter (fun Q => a ∈ (cliqueEdges r Q).erase e) := by
    intro Q hQ
    rw [mem_filter] at hQ
    by_cases ha : a ∈ (cliqueEdges r Q).erase e
    · exact mem_union_right _ (mem_filter.2 ⟨hQ.1, ha⟩)
    · refine mem_union_left _ (mem_filter.2 ⟨hQ.1, fun f hf => ?_⟩)
      have hfa : f ≠ a := fun h => ha (h ▸ hf)
      exact mem_erase.2 ⟨hfa, (mem_insert.1 (hQ.2 hf)).resolve_left hfa⟩
  have h1 := card_le_card hsub
  have h2 := (card_le_card hdiff).trans (card_union_le _ _)
  rw [abs_le]
  constructor
  · have : ((T.filter (fun Q => (cliqueEdges r Q).erase e ⊆ S.erase a)).card : ℝ) ≤
        (T.filter (fun Q => (cliqueEdges r Q).erase e ⊆ insert a S)).card := by exact_mod_cast h1
    have h0 : (0 : ℝ) ≤ (T.filter (fun Q => a ∈ (cliqueEdges r Q).erase e)).card := by positivity
    linarith
  · have : ((T.filter (fun Q => (cliqueEdges r Q).erase e ⊆ insert a S)).card : ℝ) ≤
        (T.filter (fun Q => (cliqueEdges r Q).erase e ⊆ S.erase a)).card +
          (T.filter (fun Q => a ∈ (cliqueEdges r Q).erase e)).card := by exact_mod_cast h2
    linarith

/-- The number of `q`-sets containing a fixed set `T` with `|T| ≥ t` is at most `n^{q-t}`. -/
theorem card_supersets_le {q t : ℕ} (T : Finset (Fin n)) (hT : t ≤ T.card) :
    (((univ : Finset (Fin n)).powersetCard q).filter (fun Q => T ⊆ Q)).card ≤ n ^ (q - t) := by
  by_cases hTq : T.card ≤ q
  · rw [card_powersetCard_filter_superset (subset_univ _) hTq, card_univ, Fintype.card_fin]
    rcases Nat.eq_zero_or_pos (q - t) with h | h
    · rw [h, show q - T.card = 0 by omega]; simp
    · rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        have hT0 : T.card = 0 := Finset.card_eq_zero.2 (Finset.eq_empty_of_isEmpty T)
        rw [Nat.zero_sub, Nat.choose_eq_zero_of_lt (by omega)]; exact Nat.zero_le _
      · exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (Nat.sub_le _ _) _).trans
          (Nat.pow_le_pow_right hpos (by omega)))
  · rw [card_eq_zero.2]
    · exact Nat.zero_le _
    rw [filter_eq_empty_iff]
    intro Q hQ hTQ
    have := card_le_card hTQ
    rw [(mem_powersetCard.1 hQ).2] at this
    omega

theorem card_cliquesThrough_le {q r : ℕ} (G : Finset (Finset (Fin n))) {e : Finset (Fin n)}
    (he : e.card = r) : ((cliquesThrough q r G e).card : ℝ) ≤ (n : ℝ) ^ (q - r) := by
  have : (cliquesThrough q r G e).card ≤ n ^ (q - r) := by
    refine le_trans (card_le_card ?_) (card_supersets_le e he.ge)
    intro Q hQ
    simp only [cliquesThrough, cliquesOf, mem_filter] at hQ ⊢
    exact ⟨hQ.1.1, hQ.2⟩
  exact_mod_cast this

theorem resLip_le {q r : ℕ} (G : Finset (Finset (Fin n))) {e : Finset (Fin n)} (he : e.card = r)
    (a : Finset (Fin n)) (ha : a.card = r) : resLip q r G e a ≤ (n : ℝ) ^ (q - r - 1) := by
  unfold resLip
  by_cases hae : a = e
  · subst hae
    rw [card_eq_zero.2 (by rw [filter_eq_empty_iff]; intro Q _ h; simp at h)]
    simp
  · have hcard : r + 1 ≤ (e ∪ a).card := by
      have h1 : e ⊂ e ∪ a := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨subset_union_left, fun h => hae ?_⟩
        have : a ⊆ e := h ▸ subset_union_right
        exact eq_of_subset_of_card_le this (by omega)
      have := card_lt_card h1
      omega
    have : ((cliquesThrough q r G e).filter (fun Q => a ∈ (cliqueEdges r Q).erase e)).card ≤
        n ^ (q - r - 1) := by
      refine le_trans (card_le_card ?_) ((card_supersets_le (q := q) (e ∪ a) hcard).trans
        (le_of_eq (by congr 1)))
      intro Q hQ
      simp only [cliquesThrough, cliquesOf, mem_filter] at hQ ⊢
      refine ⟨hQ.1.1.1, union_subset hQ.1.2 ?_⟩
      exact (mem_powersetCard.1 (mem_of_mem_erase hQ.2)).1
    exact_mod_cast this

theorem sum_resLip_le {q r : ℕ} (G : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    ∑ a ∈ G, resLip q r G e a ≤ (q.choose r : ℝ) * (cliquesThrough q r G e).card := by
  classical
  unfold resLip
  have h1 : ∀ a, (((cliquesThrough q r G e).filter
      (fun Q => a ∈ (cliqueEdges r Q).erase e)).card : ℝ) =
      ∑ Q ∈ cliquesThrough q r G e, (if a ∈ (cliqueEdges r Q).erase e then (1 : ℝ) else 0) := by
    intro a; rw [card_filter]; push_cast; rfl
  simp_rw [h1]
  rw [sum_comm]
  calc ∑ Q ∈ cliquesThrough q r G e, ∑ a ∈ G,
        (if a ∈ (cliqueEdges r Q).erase e then (1 : ℝ) else 0)
      ≤ ∑ Q ∈ cliquesThrough q r G e, (q.choose r : ℝ) := by
        refine sum_le_sum fun Q hQ => ?_
        simp only [cliquesThrough, cliquesOf, mem_filter, mem_powersetCard] at hQ
        have e2 : (∑ a ∈ G, if a ∈ (cliqueEdges r Q).erase e then (1 : ℝ) else 0) =
            ((G.filter (fun a => a ∈ (cliqueEdges r Q).erase e)).card : ℝ) := by
          rw [card_filter]; push_cast; rfl
        rw [e2]
        have : (G.filter (fun a => a ∈ (cliqueEdges r Q).erase e)).card ≤ q.choose r := by
          refine (card_le_card (fun a ha => (mem_filter.1 ha).2)).trans ?_
          refine (card_erase_le).trans ?_
          rw [cliqueEdges, card_powersetCard, hQ.1.1.2]
        exact_mod_cast this
    _ = (q.choose r : ℝ) * (cliquesThrough q r G e).card := by
        rw [sum_const, nsmul_eq_mul]; ring

end Counting


section Degrees

variable {n : ℕ}

/-- The degree of `S₀` in the random set, as a real number. -/
noncomputable def degCount (S₀ : Finset (Fin n)) (S : Finset (Finset (Fin n))) : ℝ :=
  (deg S S₀ : ℝ)

/-- The Lipschitz constant of `degCount`. -/
noncomputable def degLip (S₀ : Finset (Fin n)) (a : Finset (Fin n)) : ℝ :=
  if S₀ ⊆ a then 1 else 0

theorem lipOn_degCount (G : Finset (Finset (Fin n))) (S₀ : Finset (Fin n)) :
    LipOn G (degCount S₀) (degLip S₀) := by
  intro a _ S _
  unfold degCount degLip deg
  rw [filter_insert, filter_erase]
  by_cases h : S₀ ⊆ a
  · rw [if_pos h, if_pos h]
    set F := S.filter fun e => S₀ ⊆ e
    have hc : (insert a F).card = (F.erase a).card + 1 := by
      by_cases ha : a ∈ F
      · rw [insert_eq_of_mem ha, card_erase_of_mem ha]
        have : 0 < F.card := card_pos.2 ⟨a, ha⟩
        omega
      · rw [card_insert_of_notMem ha, erase_eq_of_notMem ha]
    rw [hc]; push_cast; simp
  · rw [if_neg h, if_neg h]
    have : (S.filter fun e => S₀ ⊆ e).erase a = S.filter fun e => S₀ ⊆ e := by
      apply erase_eq_of_notMem
      intro ha
      exact h (mem_filter.1 ha).2
    rw [this]; simp

theorem Ex_degCount (p : ℝ) (G : Finset (Finset (Fin n))) (S₀ : Finset (Fin n)) :
    Ex p G (degCount S₀) = deg G S₀ * p := by
  classical
  have h1 : ∀ S ⊆ G, degCount S₀ S = ∑ a ∈ G.filter (fun e => S₀ ⊆ e),
      (if {a} ⊆ S then (1 : ℝ) else 0) := by
    intro S hS
    unfold degCount deg
    rw [show (S.filter fun e => S₀ ⊆ e) = (G.filter fun e => S₀ ⊆ e).filter (fun a => {a} ⊆ S)
      from ?_, card_filter]
    · push_cast; rfl
    ext a
    simp only [mem_filter, singleton_subset_iff]
    constructor
    · rintro ⟨haS, h⟩; exact ⟨⟨hS haS, h⟩, haS⟩
    · rintro ⟨⟨-, h⟩, haS⟩; exact ⟨haS, h⟩
  rw [Ex_congr p G h1, Ex_sum, deg, ← nsmul_eq_mul, ← sum_const]
  refine sum_congr rfl fun a ha => ?_
  rw [Ex_ite, Pr_subset p (singleton_subset_iff.2 (mem_filter.1 ha).1), card_singleton, pow_one]

theorem sum_degLip_sq (G : Finset (Finset (Fin n))) (S₀ : Finset (Fin n)) :
    ∑ a ∈ G, degLip S₀ a ^ 2 = deg G S₀ := by
  unfold degLip deg
  rw [card_filter]; push_cast
  refine sum_congr rfl fun a _ => ?_
  split_ifs <;> norm_num

theorem deg_le_of_rgraph {r : ℕ} {G : Finset (Finset (Fin n))} (hG : IsRGraph r G)
    {S₀ : Finset (Fin n)} (hS : S₀.card + 1 = r) : deg G S₀ ≤ n := by
  have hsub : G ⊆ completeRGraph (Fin n) r := fun e he =>
    mem_powersetCard.2 ⟨subset_univ _, hG e he⟩
  refine (card_le_card (filter_subset_filter _ hsub)).trans ?_
  have := deg_completeRGraph (n := n) (r := r) (S := S₀) (by omega)
  unfold deg at this
  rw [this, show r - S₀.card = 1 by omega, Nat.choose_one_right]
  omega

end Degrees

section Tails

variable {β : Type*} [DecidableEq β]

/-- **Lower tail at half the mean.**  If `f` has bounded differences `c_a ≤ M` with
`∑ c_a ≤ T1` and `E f ≥ μ₀ > 0`, then `P(f ≤ E f / 2) ≤ exp(-μ₀² / (16 p M T1))`, provided
`μ₀ ≤ 4 p T1`. -/
theorem lower_tail_half {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (E : Finset β)
    (f : Finset β → ℝ) (c : β → ℝ) (hf : LipOn E f c) (M T1 μ₀ : ℝ) (hM : 0 < M) (hT1 : 0 < T1)
    (hc0 : ∀ a ∈ E, 0 ≤ c a) (hcM : ∀ a ∈ E, c a ≤ M) (hcT : ∑ a ∈ E, c a ≤ T1)
    (hμ0 : 0 ≤ μ₀) (hμ : μ₀ ≤ Ex p E f) (hμT : μ₀ ≤ 4 * p * T1) :
    Pr p E (fun S => f S ≤ Ex p E f - Ex p E f / 2) ≤
      Real.exp (-(μ₀ ^ 2 / (16 * p * M * T1))) := by
  set lam := μ₀ / (4 * p * M * T1) with hlam
  have hden : 0 < 4 * p * M * T1 := by positivity
  have hlam0 : 0 ≤ lam := div_nonneg hμ0 hden.le
  have hc : ∀ a ∈ E, lam * c a ≤ 1 := by
    intro a ha
    calc lam * c a ≤ lam * M := mul_le_mul_of_nonneg_left (hcM a ha) hlam0
      _ = μ₀ / (4 * p * T1) := by rw [hlam]; field_simp
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact hμT
  have hsq : ∑ a ∈ E, c a ^ 2 ≤ M * T1 := by
    calc ∑ a ∈ E, c a ^ 2 ≤ ∑ a ∈ E, M * c a :=
          sum_le_sum fun a ha => by rw [sq]; exact mul_le_mul_of_nonneg_right (hcM a ha) (hc0 a ha)
      _ = M * ∑ a ∈ E, c a := by rw [mul_sum]
      _ ≤ M * T1 := mul_le_mul_of_nonneg_left hcT hM.le
  refine (Pr_le_le hp0.le hp1 E f c hf (Ex p E f / 2) lam hlam0 hc).trans ?_
  apply Real.exp_le_exp.2
  have h1 : lam * (μ₀ / 2) ≤ lam * (Ex p E f / 2) := by
    apply mul_le_mul_of_nonneg_left _ hlam0; linarith
  have h2 : lam ^ 2 * p * ∑ a ∈ E, c a ^ 2 ≤ lam ^ 2 * p * (M * T1) := by
    apply mul_le_mul_of_nonneg_left hsq; positivity
  have h3 : -(lam * (μ₀ / 2)) + lam ^ 2 * p * (M * T1) = -(μ₀ ^ 2 / (16 * p * M * T1)) := by
    rw [hlam]; field_simp; ring
  linarith

/-- **Upper tail for degrees.** -/
theorem upper_tail_deg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β)
    (f : Finset β → ℝ) (c : β → ℝ) (hf : LipOn E f c) (hc1 : ∀ a ∈ E, c a ≤ 1)
    (N : ℝ) (hN : ∑ a ∈ E, c a ^ 2 ≤ N) (t : ℝ) (htN : p * N ≤ t) :
    Pr p E (fun S => Ex p E f + t ≤ f S) ≤ Real.exp (-(t / 4)) := by
  refine (Pr_ge_le hp0 hp1 E f c hf t (1 / 2) (by norm_num) fun a ha => by
    have := hc1 a ha; linarith).trans ?_
  apply Real.exp_le_exp.2
  have : (1 / 2 : ℝ) ^ 2 * p * ∑ a ∈ E, c a ^ 2 ≤ (1 / 4) * (p * N) := by
    have := mul_le_mul_of_nonneg_left hN hp0
    nlinarith
  linarith

end Tails


section Numerics

theorem four_pow_mul_exp_le {n r : ℕ} (hn : 1 ≤ n) {Y : ℝ}
    (hY : Real.log 4 + r * Real.log n ≤ Y) : 4 * (n : ℝ) ^ r * Real.exp (-Y) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h4 : (4 : ℝ) * (n : ℝ) ^ r = Real.exp (Real.log 4 + r * Real.log n) := by
    rw [Real.exp_add, Real.exp_log (by norm_num), ← Real.log_pow, Real.exp_log (by positivity)]
  rw [h4, ← Real.exp_add]
  exact Real.exp_le_one_iff.2 (by linarith)

/-- `A + B log n ≤ n^s / K` for large `n`. -/
theorem ev_log_le_rpow_div {s K A B : ℝ} (hs : 0 < s) (hK : 0 < K) (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in Filter.atTop, A + B * Real.log n ≤ (n : ℝ) ^ s / K := by
  filter_upwards [Filter.eventually_ge_atTop 1, ev_le_rpow (2 * K * |A|) hs,
    ev_log_div_rpow_le hs (show 0 < 1 / (2 * K * (B + 1)) by positivity)] with n hn1 h1 h2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : 0 < (n : ℝ) ^ s := by positivity
  have hlog : Real.log n ≤ (n : ℝ) ^ s / (2 * K * (B + 1)) := by
    rw [div_le_iff₀ hpow] at h2
    rw [le_div_iff₀ (by positivity)]
    calc Real.log n * (2 * K * (B + 1)) = Real.log n * (2 * K * (B + 1)) := rfl
      _ ≤ 1 / (2 * K * (B + 1)) * (n : ℝ) ^ s * (2 * K * (B + 1)) := by
          gcongr
      _ = (n : ℝ) ^ s := by field_simp
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hA : A ≤ (n : ℝ) ^ s / (2 * K) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [le_abs_self A]
  have hB' : B * Real.log n ≤ (n : ℝ) ^ s / (2 * K) := by
    calc B * Real.log n ≤ (B + 1) * Real.log n := by nlinarith
      _ ≤ (B + 1) * ((n : ℝ) ^ s / (2 * K * (B + 1))) := by gcongr
      _ = (n : ℝ) ^ s / (2 * K) := by field_simp
  have : (n : ℝ) ^ s / (2 * K) + (n : ℝ) ^ s / (2 * K) = (n : ℝ) ^ s / K := by field_simp; ring
  linarith

/-- The exponent in the lower tail bound for the reserve count. -/
noncomputable def resExponent (q r n : ℕ) (δ : ℝ) : ℝ :=
  ((1 / 4) * ((n : ℝ) ^ (-δ)) ^ (q.choose r - 1) * (n.choose (q - r))) ^ 2 /
    (16 * (n : ℝ) ^ (-δ) * (n : ℝ) ^ (q - r - 1) *
      ((q.choose r : ℝ) * (n : ℝ) ^ (q - r) / (n : ℝ) ^ (-δ)))

/-- The numerical facts used in the proof of `relWeakReserves`. -/
theorem reserve_numerics {q r : ℕ} (hrq : r < q) {α δ : ℝ} (hα : 0 < α)
    (hδ : 0 < δ) (hδ1 : δ * (2 * (q.choose r : ℝ)) ≤ 1 / 2)
    (hδα : δ * ((q.choose r : ℝ) - 1) ≤ α / 4) :
    ∀ᶠ n : ℕ in Filter.atTop, 2 * (q - r) ≤ n ∧ 2 ≤ n ∧
      (n : ℝ) ^ (-(1 / 3 : ℝ)) + ((r * (q - r) : ℕ) : ℝ) / (2 * n) ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) ∧
      (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 / 4 ∧
      (n : ℝ) ^ ((q : ℝ) - r - α) ≤
        (1 / 8) * ((n : ℝ) ^ (-δ)) ^ (q.choose r - 1) * (n.choose (q - r)) ∧
      2 * (n : ℝ) ^ (-δ) * n ≤ (n : ℝ) ^ (1 - δ / 2) ∧
      4 * (n : ℝ) ^ r * Real.exp (-((n : ℝ) ^ (-δ) * n / 4)) ≤ 1 ∧
      4 * (n : ℝ) ^ r * Real.exp (-resExponent q r n δ) ≤ 1 := by
  set k := q - r with hk
  set m := q.choose r with hm
  have hk1 : 1 ≤ k := by omega
  set K₁ : ℝ := 2 ^ k * (k.factorial : ℝ) with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.choose_pos hrq.le
  have hδα' : δ * ((m : ℝ) - 1) ≤ (α / 2) / 2 := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.choose_pos hrq.le
  have hδ14 : δ ≤ 1 / 4 := by nlinarith
  filter_upwards [Filter.eventually_ge_atTop (2 * k), Filter.eventually_ge_atTop 2,
    ev_error_conversion ((r * k : ℕ) : ℝ), ev_rpow_neg_le (show 0 < (1 / 4 : ℝ) by norm_num)
      (show (0 : ℝ) < 1 / 4 by norm_num),
    ev_reserve_cliques_large q r hrq (α / 2) δ (by positivity) hδα',
    ev_le_rpow 4 (show 0 < α / 2 by positivity), ev_two_p_n_le δ hδ,
    ev_log_le_rpow_div (s := 1 - δ) (K := 4) (A := Real.log 4) (B := r) (by linarith) (by norm_num)
      (Nat.cast_nonneg r),
    ev_log_le_rpow_div (s := 1 / 2) (K := 256 * m * K₁ ^ 2) (A := Real.log 4) (B := r)
      (by norm_num) (by positivity) (Nat.cast_nonneg r)]
    with n hn1 hn2 hconv hquart hres h4 h2pn hY1 hY2
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1' : (1 : ℝ) ≤ n := by linarith
  set p := (n : ℝ) ^ (-δ) with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1' (by linarith)
  set B := (n.choose k : ℝ) with hB
  refine ⟨hn1, hn2, hconv, hquart, ?_, h2pn, ?_, ?_⟩
  · -- reserve count
    have hpos : 0 ≤ (1 / 2 : ℝ) * p ^ (m - 1) * B := by positivity
    have e1 : (n : ℝ) ^ ((q : ℝ) - r - α) * 4 ≤ (n : ℝ) ^ ((q : ℝ) - r - α / 2) := by
      have : (n : ℝ) ^ ((q : ℝ) - r - α / 2) = (n : ℝ) ^ ((q : ℝ) - r - α) * (n : ℝ) ^ (α / 2) := by
        rw [← Real.rpow_add hn0]; ring_nf
      rw [this]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    nlinarith
  · -- degree tail
    apply four_pow_mul_exp_le (by omega)
    have : (n : ℝ) ^ (1 - δ) = p * n := by
      rw [hp, sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one, mul_comm]
    rw [← this]; exact hY1
  · -- reserve tail
    apply four_pow_mul_exp_le (by omega)
    refine hY2.trans ?_
    unfold resExponent
    -- lower bound for the exponent
    set y := (n : ℝ) ^ (k - 1) with hy
    have hy0 : 0 < y := by positivity
    have hxk : (n : ℝ) ^ k = n * y := by
      rw [hy, ← pow_succ']; congr 1; omega
    have hBlow : (n : ℝ) * y / K₁ ≤ B := by
      rw [← hxk]
      have hB' : ((n : ℝ) / 2) ^ k / k.factorial ≤ (n.choose k : ℝ) := by
        refine le_trans ?_ (Nat.pow_le_choose k n)
        gcongr
        rw [Nat.cast_sub (by omega)]; push_cast
        have : (2 * k : ℝ) ≤ n := by exact_mod_cast hn1
        linarith
      calc (n : ℝ) ^ k / K₁ = ((n : ℝ) / 2) ^ k / k.factorial := by
            rw [hK₁, div_pow]; field_simp
        _ ≤ B := hB'
    have hP : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (p ^ (m - 1)) ^ 2 := by
      have e : (p ^ (m - 1)) ^ 2 = (n : ℝ) ^ (-(δ * (2 * ((m - 1 : ℕ) : ℝ)))) := by
        rw [hp, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 1; push_cast; ring
      rw [e]
      apply Real.rpow_le_rpow_of_exponent_le hn1'
      have : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
      nlinarith
    have hhalf : (n : ℝ) ^ (-(1 / 2 : ℝ)) * n = (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add_one hn0.ne']; norm_num
    have hden : 16 * p * y * ((m : ℝ) * (n * y) / p) = 16 * m * n * y ^ 2 := by
      field_simp
    rw [hxk, hden]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hB0 : 0 ≤ (n : ℝ) * y / K₁ := by positivity
    have hBsq : ((n : ℝ) * y / K₁) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hB0 hBlow 2
    have hsq : ((1 / 4) * p ^ (m - 1) * B) ^ 2 = (1 / 16) * (p ^ (m - 1)) ^ 2 * B ^ 2 := by ring
    rw [hsq, ← hhalf]
    have hK : ((n : ℝ) * y / K₁) ^ 2 * K₁ ^ 2 = (n : ℝ) ^ 2 * y ^ 2 := by field_simp
    have hA0 : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have step : (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) * y / K₁) ^ 2 ≤ (p ^ (m - 1)) ^ 2 * B ^ 2 :=
      mul_le_mul hP hBsq (by positivity) (by positivity)
    calc (n : ℝ) ^ (-(1 / 2 : ℝ)) * n * (16 * m * n * y ^ 2)
        = 16 * m * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (((n : ℝ) * y / K₁) ^ 2 * K₁ ^ 2)) := by
          rw [hK]; ring
      _ = 16 * m * K₁ ^ 2 * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) * y / K₁) ^ 2) := by ring
      _ ≤ 16 * m * K₁ ^ 2 * ((p ^ (m - 1)) ^ 2 * B ^ 2) :=
          mul_le_mul_of_nonneg_left step (by positivity)
      _ = 1 / 16 * (p ^ (m - 1)) ^ 2 * B ^ 2 * (256 * m * K₁ ^ 2) := by ring

end Numerics


/-- **Reserves inside a dense host.** -/
theorem relWeakReserves {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) (α : ℝ) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : Finset (Finset (Fin n)),
      IsRGraph r G → MinDegGE r G ((1 - ε) * n) →
      ∃ X ⊆ G, MaxDegLE r X ((n : ℝ) ^ (1 - δ)) ∧
        ∀ e ∈ G, (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e).card := by
  classical
  obtain ⟨εB, hεB, -, nB, hBoost⟩ := boostLemma q r hr hrq
  set m := q.choose r with hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.choose_pos hrq.le
  set δ : ℝ := min (α / (4 * m)) (1 / (4 * m)) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ * (2 * (m : ℝ)) ≤ 1 / 2 := by
    have h := min_le_right (α / (4 * m)) (1 / (4 * (m : ℝ)))
    calc δ * (2 * (m : ℝ)) ≤ 1 / (4 * m) * (2 * m) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = 1 / 2 := by field_simp; ring
  have hδα : δ * ((m : ℝ) - 1) ≤ α / 4 := by
    have h := min_le_left (α / (4 * m)) (1 / (4 * (m : ℝ)))
    calc δ * ((m : ℝ) - 1) ≤ α / (4 * m) * m :=
          mul_le_mul h (by linarith) (by linarith) (by positivity)
      _ = α / 4 := by field_simp
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1 (reserve_numerics hrq hα hδ hδ1 hδα)
  refine ⟨εB, hεB, δ / 2, by positivity, max n₁ nB, fun n hn G hG hδG => ?_⟩
  obtain ⟨hn2k, hn2, hconv, hquart, hresN, h2pn, hdegT, hresT⟩ := hn₁ n (le_of_max_le_left hn)
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hn1' : (1 : ℝ) ≤ n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  set p := (n : ℝ) ^ (-δ) with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1' (by linarith)
  have hGK : G ⊆ completeRGraph (Fin n) r := fun e he =>
    mem_powersetCard.2 ⟨subset_univ _, hG e he⟩
  obtain ⟨H, hHG, hHreg⟩ := hBoost n (le_of_max_le_right hn) G hGK hδG
  set B := (n.choose (q - r) : ℝ) with hB
  have hBle : B ≤ (n : ℝ) ^ (q - r) := by
    rw [hB]; exact_mod_cast Nat.choose_le_pow n (q - r)
  -- every edge lies in many cliques of `G`
  have hCT : ∀ e ∈ G, B / 4 ≤ (cliquesThrough q r G e).card := by
    intro e he
    have h1 := clique_deg_conversion (by omega) (hHreg e he) hconv
    have h2 : (cliqueMult H e : ℝ) ≤ (cliquesThrough q r G e).card := by
      unfold cliqueMult cliquesThrough
      exact_mod_cast card_le_card (filter_subset_filter _ hHG)
    have h3 : (n : ℝ) ^ (-(1 / 4 : ℝ)) * B ≤ 1 / 4 * B :=
      mul_le_mul_of_nonneg_right hquart (by positivity)
    have := (abs_le.1 h1).1
    linarith
  set 𝒮 := (univ : Finset (Fin n)).powersetCard (r - 1) with h𝒮
  set μ₀ := (1 / 4) * p ^ (m - 1) * B with hμ₀
  -- the bad event has probability `< 1`
  have hPr : Pr p G (fun S => (∃ S₀ ∈ 𝒮, Ex p G (degCount S₀) + p * n ≤ degCount S₀ S) ∨
      (∃ e ∈ G, resCount q r G e S ≤
        Ex p G (resCount q r G e) - Ex p G (resCount q r G e) / 2)) < 1 := by
    refine lt_of_le_of_lt (Pr_or_le hp0.le hp1 G _ _) ?_
    have hD : Pr p G (fun S => ∃ S₀ ∈ 𝒮, Ex p G (degCount S₀) + p * n ≤ degCount S₀ S) ≤
        𝒮.card * Real.exp (-(p * n / 4)) := by
      refine (Pr_exists_le hp0.le hp1 G 𝒮 _).trans ?_
      rw [← nsmul_eq_mul]
      refine sum_le_card_nsmul _ _ _ fun S₀ hS₀ => ?_
      have hS₀c : S₀.card + 1 = r := by
        rw [(mem_powersetCard.1 hS₀).2]; omega
      refine upper_tail_deg hp0.le hp1 G (degCount S₀) (degLip S₀) (lipOn_degCount G S₀)
        (fun a _ => by unfold degLip; split_ifs <;> norm_num) n ?_ (p * n) le_rfl
      rw [sum_degLip_sq]
      exact_mod_cast deg_le_of_rgraph hG hS₀c
    have hR : Pr p G (fun S => ∃ e ∈ G, resCount q r G e S ≤
        Ex p G (resCount q r G e) - Ex p G (resCount q r G e) / 2) ≤
        G.card * Real.exp (-resExponent q r n δ) := by
      refine (Pr_exists_le hp0.le hp1 G G _).trans ?_
      rw [← nsmul_eq_mul]
      refine sum_le_card_nsmul _ _ _ fun e he => ?_
      have her : e.card = r := hG e he
      have hEx := Ex_resCount (q := q) p G her
      have hCTe := hCT e he
      have hCTle := card_cliquesThrough_le (q := q) G her
      have hpm : 0 ≤ p ^ (m - 1) := by positivity
      have hpm1 : p ^ (m - 1) ≤ 1 := pow_le_one₀ hp0.le hp1
      refine lower_tail_half hp0 hp1 G (resCount q r G e) (resLip q r G e)
        (lipOn_resCount q r G e) ((n : ℝ) ^ (q - r - 1)) ((m : ℝ) * (n : ℝ) ^ (q - r) / p) μ₀
        (by positivity) (by positivity) (fun a _ => by unfold resLip; positivity)
        (fun a ha => resLip_le G her a (hG a ha)) ?_ (by positivity) ?_ ?_
      · refine (sum_resLip_le G e).trans ?_
        rw [le_div_iff₀ hp0]
        calc (m : ℝ) * (cliquesThrough q r G e).card * p ≤ m * (n : ℝ) ^ (q - r) * 1 := by
              gcongr
          _ = m * (n : ℝ) ^ (q - r) := mul_one _
      · rw [hEx, hμ₀]
        calc 1 / 4 * p ^ (m - 1) * B = B / 4 * p ^ (m - 1) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hCTe hpm
      · rw [hμ₀]
        have : 4 * p * ((m : ℝ) * (n : ℝ) ^ (q - r) / p) = 4 * m * (n : ℝ) ^ (q - r) := by
          field_simp
        rw [this]
        have hB0 : 0 ≤ B := by positivity
        nlinarith
    have hS : (𝒮.card : ℝ) ≤ (n : ℝ) ^ r := by
      rw [h𝒮, card_powersetCard, card_univ, Fintype.card_fin]
      have := Nat.choose_le_pow n (r - 1)
      have h2 : n ^ (r - 1) ≤ n ^ r := Nat.pow_le_pow_right (by omega) (by omega)
      exact_mod_cast this.trans h2
    have hGc : (G.card : ℝ) ≤ (n : ℝ) ^ r := by
      have h1 := card_le_card hGK
      rw [completeRGraph, card_powersetCard, card_univ, Fintype.card_fin] at h1
      exact_mod_cast h1.trans (Nat.choose_le_pow n r)
    have he1 : 0 ≤ Real.exp (-(p * n / 4)) := (Real.exp_pos _).le
    have he2 : 0 ≤ Real.exp (-resExponent q r n δ) := (Real.exp_pos _).le
    have hpn : p * n = (n : ℝ) ^ (-δ) * n := rfl
    have t1 := mul_le_mul_of_nonneg_right hS he1
    have t2 := mul_le_mul_of_nonneg_right hGc he2
    rw [hpn] at hD t1
    linarith
  obtain ⟨X, hXG, hX⟩ := exists_not_of_Pr_lt_one G hPr
  push_neg at hX
  obtain ⟨hXD, hXR⟩ := hX
  refine ⟨X, hXG, fun S₀ hS₀ => ?_, fun e he => ?_⟩
  · have hS₀m : S₀ ∈ 𝒮 := mem_powersetCard.2 ⟨subset_univ _, by omega⟩
    have h1 := hXD S₀ hS₀m
    rw [Ex_degCount] at h1
    have h2 : (deg G S₀ : ℝ) ≤ n := by exact_mod_cast deg_le_of_rgraph hG hS₀
    have h3 : (deg G S₀ : ℝ) * p ≤ n * p := mul_le_mul_of_nonneg_right h2 hp0.le
    unfold degCount at h1
    have : (n : ℝ) ^ (1 - δ / 2) = (n : ℝ) ^ (1 - δ / 2) := rfl
    linarith
  · have h1 := hXR e he
    have her : e.card = r := hG e he
    rw [Ex_resCount (q := q) p G her] at h1
    have h2 := resCount_le_reserve q r G e X
    have hCTe := hCT e he
    have hpm : 0 ≤ p ^ (m - 1) := by positivity
    have h3 : B / 4 * p ^ (m - 1) ≤ (cliquesThrough q r G e).card * p ^ (m - 1) :=
      mul_le_mul_of_nonneg_right hCTe hpm
    linarith

end RefinedAbsorption.Original2024
