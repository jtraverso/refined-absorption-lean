module
public import RefinedAbsorption.GridRefiner.Labels
public import RefinedAbsorption.LocalRefiner.Gadgets

/-!
# The parity obstruction for odd `q` (`r = 2`)

Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

The local refiner of `RequestProject/LocalRefiner/` (even `q`) splits every edge `uv` of `X` into a
*token at `u`*, a *token at `v`* and a degree-free bundle.  A token at `u` is a small multigraph
whose degrees are `≡ 1` at `u` and `≡ 0` at every other vertex modulo `d = q - 1`.  This file
proves, in Lean, why that route is closed for odd `q`, and what remains possible.

* `sum_mdeg_singleton`, `even_sum_mdeg`: the handshake lemma for multigraphs.
* `even_sum_classes`: if `d` is even, the degree classes of a multigraph modulo `d` have even sum.
* **`single_vertex_class_iff`**: if `d` is even, a multigraph whose degrees are `≡ a` at `u` and
  `≡ 0` elsewhere modulo `d` exists **iff `a` is even** (for `n ≥ 3`).
* **`no_local_unit_token`** (`q` odd): there is no token at `u` alone; and
  `unit_token_needs_partner`: every multigraph with degree `≡ 1` at `u` has a second vertex whose
  degree is not divisible by `q - 1`.
* **`local_token_half_iff`** (`q` odd): a local token at `u` with degree `≡ (q-1)/2 + 1` exists iff
  `q ≡ 3 (mod 4)`.  For such `q` the class of an edge `uv` splits into two local tokens and the
  order-`2` class `(q-1)/2 · (1_u + 1_v)`.
* **`eq_of_forall_sum_eq_zero`**: if every `d`-subset of a family of at least `d + 1` elements of an
  abelian group sums to `0`, all elements are equal.  Applied to the degree classes of the tokens
  absorbed by one chain, it says that all tokens of a chain have the same class.
-/

@[expose] public section

namespace RefinedAbsorption.GridRefiner

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner

section Handshake

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- **Handshake lemma** for labelled multigraphs. -/
theorem sum_mdeg_singleton (ends : E → Finset V) (F : Finset E) :
    ∑ v, mdeg ends F {v} = ∑ c ∈ F, (ends c).card := by
  unfold mdeg
  simp only [singleton_subset_iff, card_filter]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun c _ => ?_
  rw [← card_filter, filter_mem_eq_inter, univ_inter]

/-- In a multigraph (every copy a `2`-set) the degree sum is even. -/
theorem even_sum_mdeg {ends : E → Finset V} {F : Finset E} (h2 : MIsRGraph 2 ends F) :
    Even (∑ v, mdeg ends F {v}) := by
  rw [sum_mdeg_singleton, sum_congr rfl h2, sum_const, smul_eq_mul]
  exact even_two.mul_left _

/-- If `d` is even, the degree classes modulo `d` of a multigraph have even sum. -/
theorem even_sum_classes {ends : E → Finset V} {F : Finset E} (h2 : MIsRGraph 2 ends F) {d : ℕ}
    (hd : Even d) (c : V → ℕ) (hc : ∀ v, mdeg ends F {v} ≡ c v [MOD d]) : Even (∑ v, c v) := by
  have h := even_sum_mdeg h2
  rw [← ZMod.natCast_eq_zero_iff_even] at h ⊢
  rw [Nat.cast_sum] at h ⊢
  rw [← h]
  refine sum_congr rfl fun v _ => ?_
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).2 ((hc v).of_dvd (even_iff_two_dvd.1 hd))).symm

end Handshake

section SingleVertex

/-- The segments of a local token at `u` with degree `2b` at `u`: `b` copies of `{u, u+1}` and of
`{u, u+2}`, and `(d - 1) b` copies of `{u+1, u+2}`. -/
def evenTokSg {n : ℕ} [NeZero n] (d b : ℕ) (u : Fin n) : Unit → List (Finset (Fin n) × ℕ) :=
  fun _ => [({u, u + 1}, b), ({u, u + 2}, b), ({u + 1, u + 2}, (d - 1) * b)]

lemma evenTok_deg {n : ℕ} [NeZero n] (hn : 3 ≤ n) {d : ℕ} (hd : 1 ≤ d) (b : ℕ) (u v : Fin n) :
    mdeg (cpEnds (evenTokSg d b u)) (liftS (evenTokSg d b u) {()}) {v} =
      if v = u then 2 * b else if v = u + 1 ∨ v = u + 2 then d * b else 0 := by
  obtain ⟨h01, h02, h12⟩ := tok_ne_all hn u
  rw [mdeg_liftS, sum_singleton, wdeg_list]
  simp only [evenTokSg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    singleton_subset_iff, mem_insert, mem_singleton]
  have hdb : b + (d - 1) * b = d * b := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  by_cases hu : v = u
  · subst hu; simp [h01, h02]; ring
  · by_cases h1 : v = u + 1
    · subst h1; simp [hu, h12, hdb]
    · by_cases h2 : v = u + 2
      · subst h2; simp [hu, h1, hdb]
      · simp [hu, h1, h2]

lemma evenTok_rgraph {n : ℕ} [NeZero n] (hn : 3 ≤ n) (d b : ℕ) (u : Fin n) :
    MIsRGraph 2 (cpEnds (evenTokSg d b u)) (liftS (evenTokSg d b u) {()}) := by
  obtain ⟨h01, h02, h12⟩ := tok_ne_all hn u
  intro c hc
  have h := cpEnds_mem_of_mem_liftS hc
  simp only [evenTokSg, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h <;> rw [cpEnds, h] <;> simp [h01, h02, h12]

/-- **Single-vertex degree classes.**  For even `d` and `n ≥ 3`, a multigraph on `Fin n` whose
degrees are `≡ a` at `u` and `≡ 0` at every other vertex modulo `d` exists iff `a` is even. -/
theorem single_vertex_class_iff {n : ℕ} [NeZero n] (hn : 3 ≤ n) {d : ℕ} (hd : Even d) (hd1 : 1 ≤ d)
    (u : Fin n) (a : ℕ) :
    (∃ (E : Type) (_ : DecidableEq E) (ends : E → Finset (Fin n)) (F : Finset E),
      MIsRGraph 2 ends F ∧ mdeg ends F {u} ≡ a [MOD d] ∧ ∀ v ≠ u, d ∣ mdeg ends F {v}) ↔
      Even a := by
  constructor
  · rintro ⟨E, _, ends, F, h2, hu, hv⟩
    have h := even_sum_classes h2 hd (fun v => if v = u then a else 0) (fun v => by
      by_cases h : v = u
      · subst h; simpa using hu
      · simpa [h] using (Nat.modEq_zero_iff_dvd.2 (hv v h)))
    simpa using h
  · rintro ⟨b, rfl⟩
    refine ⟨Unit × ℕ × ℕ, inferInstance, cpEnds (evenTokSg d b u), liftS (evenTokSg d b u) {()},
      evenTok_rgraph hn d b u, ?_, fun v hv => ?_⟩
    · rw [evenTok_deg hn hd1, if_pos rfl, two_mul]
    · rw [evenTok_deg hn hd1, if_neg hv]
      split_ifs
      · exact dvd_mul_right d b
      · exact dvd_zero d

/-- **No local unit token for odd `q`.**  For odd `q` there is no multigraph whose degrees are
`≡ 1` at `u` and `≡ 0` at every other vertex modulo `q - 1`. -/
theorem no_local_unit_token {n q : ℕ} {E : Type} [DecidableEq E] (hq : Odd q)
    {ends : E → Finset (Fin n)} {F : Finset E} (h2 : MIsRGraph 2 ends F) (u : Fin n)
    (hu : mdeg ends F {u} ≡ 1 [MOD q - 1]) : ¬ ∀ v ≠ u, (q - 1) ∣ mdeg ends F {v} := by
  intro hv
  have hd : Even (q - 1) := hq.tsub_odd odd_one
  have h := even_sum_classes h2 hd (fun v => if v = u then 1 else 0) (fun v => by
    by_cases h : v = u
    · subst h; simpa using hu
    · simpa [h] using (Nat.modEq_zero_iff_dvd.2 (hv v h)))
  simp at h

/-- **Every unit token needs a partner** (odd `q`). -/
theorem unit_token_needs_partner {n q : ℕ} {E : Type} [DecidableEq E] (hq : Odd q)
    {ends : E → Finset (Fin n)} {F : Finset E} (h2 : MIsRGraph 2 ends F) (u : Fin n)
    (hu : mdeg ends F {u} ≡ 1 [MOD q - 1]) : ∃ v ≠ u, ¬ (q - 1) ∣ mdeg ends F {v} := by
  by_contra h
  push_neg at h
  exact no_local_unit_token hq h2 u hu h

/-- **Half tokens** (odd `q ≥ 3`).  A multigraph on `Fin n` (`n ≥ 3`) with degree
`≡ (q-1)/2 + 1` at `u` and `≡ 0` elsewhere modulo `q - 1` exists iff `q ≡ 3 (mod 4)`. -/
theorem local_token_half_iff {n q : ℕ} [NeZero n] (hn : 3 ≤ n) (hq : Odd q) (hq3 : 3 ≤ q)
    (u : Fin n) :
    (∃ (E : Type) (_ : DecidableEq E) (ends : E → Finset (Fin n)) (F : Finset E),
      MIsRGraph 2 ends F ∧ mdeg ends F {u} ≡ (q - 1) / 2 + 1 [MOD q - 1] ∧
        ∀ v ≠ u, (q - 1) ∣ mdeg ends F {v}) ↔ q % 4 = 3 := by
  rw [single_vertex_class_iff hn (hq.tsub_odd odd_one) (by omega)]
  obtain ⟨k, rfl⟩ := hq
  rw [Nat.even_iff]
  omega

end SingleVertex

section Chains

/-- **Tokens of one chain have one class.**  If every `d`-subset of `s` (with `|s| ≥ d + 1`)
has sum `0`, then `a` is constant on `s`. -/
theorem eq_of_forall_sum_eq_zero {ι G : Type*} [DecidableEq ι] [AddCommGroup G] (a : ι → G)
    {s : Finset ι} {d : ℕ} (hd : 1 ≤ d) (hs : d + 1 ≤ s.card)
    (h : ∀ T ⊆ s, T.card = d → ∑ i ∈ T, a i = 0) : ∀ i ∈ s, ∀ j ∈ s, a i = a j := by
  intro i hi j hj
  by_cases hij : i = j
  · rw [hij]
  have hcard : d - 1 ≤ (s \ {i, j}).card := by
    rw [card_sdiff_of_subset (by simp [insert_subset_iff, hi, hj]), card_pair hij]
    omega
  obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hcard
  have hiT : i ∉ T := fun h => by simpa using hT h
  have hjT : j ∉ T := fun h => by simpa using hT h
  have hTs : T ⊆ s := hT.trans sdiff_subset
  have h1 := h (insert i T) (insert_subset hi hTs) (by rw [card_insert_of_notMem hiT]; omega)
  have h2 := h (insert j T) (insert_subset hj hTs) (by rw [card_insert_of_notMem hjT]; omega)
  rw [sum_insert hiT] at h1
  rw [sum_insert hjT] at h2
  exact add_right_cancel (h1.trans h2.symm)

end Chains

section Partner

/-- A *partner token*: `1 + (q-1)^2` copies of `{u, h}` and `q - 2` copies of `{h, p}`. -/
def partnerTokSg {V : Type} [DecidableEq V] (q : ℕ) (u h p : V) : Unit → List (Finset V × ℕ) :=
  fun _ => [({u, h}, 1 + (q - 1) * (q - 1)), ({h, p}, q - 2)]

/-- **Partner tokens exist** (any `q ≥ 2`): for distinct `u, h, p` the partner token is a
multigraph with degrees `≡ 1` at `u`, `≡ -1` at `p` and `≡ 0` elsewhere modulo `q - 1`. -/
theorem partnerTok_deg {V : Type} [DecidableEq V] {q : ℕ} (hq : 2 ≤ q) {u h p : V} (huh : u ≠ h)
    (hup : u ≠ p) (hhp : h ≠ p) :
    MIsRGraph 2 (cpEnds (partnerTokSg q u h p)) (liftS (partnerTokSg q u h p) {()}) ∧
    (mdeg (cpEnds (partnerTokSg q u h p)) (liftS (partnerTokSg q u h p) {()}) {u} : ZMod (q - 1))
      = 1 ∧
    (mdeg (cpEnds (partnerTokSg q u h p)) (liftS (partnerTokSg q u h p) {()}) {p} : ZMod (q - 1))
      = -1 ∧
    ∀ v, v ≠ u → v ≠ p →
      (mdeg (cpEnds (partnerTokSg q u h p)) (liftS (partnerTokSg q u h p) {()}) {v} :
        ZMod (q - 1)) = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, q = d + 2 := ⟨q - 2, by omega⟩
  have hd : (d + 2 - 1 : ℕ) = d + 1 := by omega
  have hd2 : (d + 2 - 2 : ℕ) = d := by omega
  have hdeg : ∀ v, mdeg (cpEnds (partnerTokSg (d + 2) u h p))
      (liftS (partnerTokSg (d + 2) u h p) {()}) {v} =
      (if v = u ∨ v = h then 1 + (d + 1) * (d + 1) else 0) + (if v = h ∨ v = p then d else 0) := by
    intro v
    rw [mdeg_liftS, sum_singleton, wdeg_list]
    simp [partnerTokSg, hd, hd2]
  have hz : (d : ZMod (d + 1)) + 1 = 0 := by exact_mod_cast ZMod.natCast_self (d + 1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    have hm := cpEnds_mem_of_mem_liftS hc
    simp only [partnerTokSg, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm <;> rw [cpEnds, hm] <;> simp [huh, hhp]
  · rw [hdeg, hd]; simp only [huh, hup, or_false, if_true, if_false]; push_cast
    linear_combination ((d : ZMod (d + 1)) + 1) * hz
  · rw [hdeg, hd]; simp only [Ne.symm hup, Ne.symm hhp, or_true, false_or, if_true, if_false]
    push_cast
    linear_combination hz
  · intro v hvu hvp
    rw [hdeg, hd]
    by_cases hvh : v = h
    · subst hvh; simp only [true_or, or_true, if_true]; push_cast
      linear_combination ((d : ZMod (d + 1)) + 2) * hz
    · simp [hvu, hvp, hvh]

end Partner

section Cuts

variable {V E : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Degree sum over a vertex set `S`. -/
theorem sum_mdeg_singleton_on (ends : E → Finset V) (F : Finset E) (S : Finset V) :
    ∑ v ∈ S, mdeg ends F {v} = ∑ c ∈ F, (ends c ∩ S).card := by
  unfold mdeg
  simp only [singleton_subset_iff, card_filter]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun c _ => ?_
  rw [← card_filter, filter_mem_eq_inter, inter_comm]

omit [Fintype V] in
/-- **Cut parity** (odd `q`, `r = 2`).  In a divisible multigraph every vertex set `S` is crossed
by an even number of copies.  This is the only parity information a refiner for odd `q` can use
beyond single vertices. -/
theorem even_cut_of_divisible {q : ℕ} (hq : Odd q) {ends : E → Finset V} {L : Finset E}
    (h2 : MIsRGraph 2 ends L) (hL : MIsDivisible q 2 ends L) (S : Finset V) :
    Even (L.filter fun c => (ends c ∩ S).card = 1).card := by
  have hd : Even (q - 1) := hq.tsub_odd odd_one
  have hS : Even (∑ v ∈ S, mdeg ends L {v}) := by
    refine Finset.even_sum _ fun v _ => ?_
    have h := hL {v} (by simp)
    simp only [card_singleton, Nat.choose_one_right, show 2 - 1 = 1 from rfl] at h
    exact (even_iff_two_dvd.2 ((even_iff_two_dvd.1 hd).trans h))
  rw [sum_mdeg_singleton_on] at hS
  have hsplit : ∑ c ∈ L, (ends c ∩ S).card =
      (L.filter fun c => (ends c ∩ S).card = 1).card +
        2 * (L.filter fun c => (ends c ∩ S).card = 2).card := by
    rw [card_eq_sum_ones, card_eq_sum_ones, sum_filter, sum_filter, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun c hc => ?_
    have hle : (ends c ∩ S).card ≤ 2 := (h2 c hc) ▸ card_le_card inter_subset_left
    interval_cases h : (ends c ∩ S).card <;> simp
  rw [hsplit] at hS
  exact (Nat.even_add.1 hS).2 (even_two.mul_right _)

end Cuts

end RefinedAbsorption.GridRefiner
