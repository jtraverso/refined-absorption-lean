module
public import Mathlib

/-!
# Integer-weighted `r`-graphs, null designs and trades

Preparation for the theorem of Graver–Jurkat and Wilson (Theorem 3.2 of the paper).

An integer-weighted hypergraph on a finite vertex type `V` is a function `f : Finset V → ℤ`.
Its *degree* at a set `S` is `wdeg f S = ∑_{e ⊇ S} f e`.  A function is *`r`-supported* if it
vanishes off the `r`-sets, and an `r`-supported function is a *null design* if all its degrees
at sets of size `< r` vanish.

The *trade* (or *pod*) on pairwise disjoint pairs `(a₁,b₁), …, (a_r,b_r)` is the signed sum of
the `2^r` transversals `{c₁,…,c_r}` (`cᵢ ∈ {aᵢ,bᵢ}`), with sign `(-1)^{#{i : cᵢ = bᵢ}}`.

Main result: `null_mem_tradeSpan`, every null design supported inside `U` is an integer
combination of trades whose vertices lie in `U`.
-/

@[expose] public section

namespace RefinedAbsorption.GJW

open Finset

variable {V : Type*} [DecidableEq V]

/-- The trade on a list of pairs. -/
def tradeFn : List (V × V) → Finset V → ℤ
  | [], e => if e = ∅ then 1 else 0
  | (a, b) :: ps, e =>
      (if a ∈ e ∧ b ∉ e then tradeFn ps (e.erase a) else 0) -
      (if b ∈ e ∧ a ∉ e then tradeFn ps (e.erase b) else 0)

/-- The vertices of a list of pairs. -/
def tverts : List (V × V) → Finset V
  | [] => ∅
  | (a, b) :: ps => insert a (insert b (tverts ps))

/-- A list of pairs is valid if all its `2 * length` vertices are distinct. -/
def TValid : List (V × V) → Prop
  | [] => True
  | (a, b) :: ps => a ≠ b ∧ a ∉ tverts ps ∧ b ∉ tverts ps ∧ TValid ps

theorem card_tverts : ∀ {ps : List (V × V)}, TValid ps → (tverts ps).card = 2 * ps.length
  | [], _ => by simp [tverts]
  | (a, b) :: ps, h => by
    obtain ⟨hab, ha, hb, hps⟩ := h
    simp only [tverts, List.length_cons]
    rw [card_insert_of_notMem, card_insert_of_notMem hb, card_tverts hps]
    · ring
    · simp [hab, ha]

theorem tradeFn_support : ∀ {ps : List (V × V)} {e : Finset V}, tradeFn ps e ≠ 0 →
    e ⊆ tverts ps ∧ e.card = ps.length
  | [], e, h => by
    simp only [tradeFn, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
    subst h; simp [tverts]
  | (a, b) :: ps, e, h => by
    simp only [tradeFn] at h
    by_cases h1 : a ∈ e ∧ b ∉ e
    · rw [if_pos h1, if_neg (by tauto), sub_zero] at h
      obtain ⟨hs, hc⟩ := tradeFn_support h
      refine ⟨?_, ?_⟩
      · intro x hx
        by_cases hxa : x = a
        · simp [tverts, hxa]
        · have := hs (mem_erase.2 ⟨hxa, hx⟩)
          simp [tverts, this]
      · rw [List.length_cons, ← hc, card_erase_of_mem h1.1]
        have : 0 < e.card := card_pos.2 ⟨a, h1.1⟩
        omega
    · rw [if_neg h1, zero_sub] at h
      by_cases h2 : b ∈ e ∧ a ∉ e
      · rw [if_pos h2, neg_ne_zero] at h
        obtain ⟨hs, hc⟩ := tradeFn_support h
        refine ⟨?_, ?_⟩
        · intro x hx
          by_cases hxb : x = b
          · simp [tverts, hxb]
          · have := hs (mem_erase.2 ⟨hxb, hx⟩)
            simp [tverts, this]
        · rw [List.length_cons, ← hc, card_erase_of_mem h2.1]
          have : 0 < e.card := card_pos.2 ⟨b, h2.1⟩
          omega
      · simp [if_neg h2] at h

theorem tradeFn_eq_zero_of_mem {ps : List (V × V)} {e : Finset V} {x : V} (hx : x ∉ tverts ps)
    (hxe : x ∈ e) : tradeFn ps e = 0 := by
  by_contra h
  exact hx ((tradeFn_support h).1 hxe)

variable [Fintype V]

/-- The weighted degree of `S`: the sum of `f` over all supersets of `S`. -/
def wdeg (f : Finset V → ℤ) (S : Finset V) : ℤ :=
  ∑ e ∈ univ.filter (fun e => S ⊆ e), f e

theorem wdeg_add (f g : Finset V → ℤ) (S : Finset V) : wdeg (f + g) S = wdeg f S + wdeg g S := by
  simp [wdeg, sum_add_distrib]

theorem wdeg_sub (f g : Finset V → ℤ) (S : Finset V) : wdeg (f - g) S = wdeg f S - wdeg g S := by
  simp [wdeg, sum_sub_distrib]

theorem wdeg_smul (c : ℤ) (f : Finset V → ℤ) (S : Finset V) : wdeg (c • f) S = c * wdeg f S := by
  simp [wdeg, mul_sum]

theorem wdeg_zero (S : Finset V) : wdeg (0 : Finset V → ℤ) S = 0 := by simp [wdeg]

/-- If `f` vanishes on every set containing `x`, then its degree at any `S ∋ x` vanishes. -/
theorem wdeg_eq_zero_of_mem {f : Finset V → ℤ} {x : V} (hf : ∀ e, x ∈ e → f e = 0)
    {S : Finset V} (hxS : x ∈ S) : wdeg f S = 0 := by
  refine sum_eq_zero fun e he => hf e ((mem_filter.1 he).2 hxS)

/-- Shifting: if `f` vanishes on the sets containing `x`, then the sum over `e ⊇ S` with
`x ∈ e` of `f (e.erase x)` is the degree of `f` at `S.erase x`. -/
theorem sum_erase_eq_wdeg {f : Finset V → ℤ} {x : V} (hf : ∀ e, x ∈ e → f e = 0) (S : Finset V) :
    ∑ e ∈ univ.filter (fun e => S ⊆ e), (if x ∈ e then f (e.erase x) else 0) =
      wdeg f (S.erase x) := by
  rw [← sum_filter, filter_filter, wdeg]
  have h2 : ∑ e ∈ univ.filter (fun e => S.erase x ⊆ e), f e =
      ∑ e ∈ univ.filter (fun e => S.erase x ⊆ e ∧ x ∉ e), f e := by
    rw [← filter_filter, sum_filter (fun e => x ∉ e)]
    refine sum_congr rfl fun e _ => ?_
    split_ifs with h
    · exact hf e h
    · rfl
  rw [h2]
  refine sum_nbij' (fun e => e.erase x) (fun e => insert x e) ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    exact ⟨erase_subset_erase x he.1, notMem_erase x e⟩
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    refine ⟨?_, mem_insert_self x e⟩
    intro y hy
    by_cases hyx : y = x
    · simp [hyx]
    · exact mem_insert_of_mem (he.1 (mem_erase.2 ⟨hyx, hy⟩))
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    exact insert_erase he.2
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    exact erase_insert he.2
  · intro e _; rfl

/-- Trades are null designs. -/
theorem wdeg_tradeFn : ∀ {ps : List (V × V)}, TValid ps → ∀ S : Finset V, S.card < ps.length →
    wdeg (tradeFn ps) S = 0
  | [], _, S, hS => by simp at hS
  | (a, b) :: ps, h, S, hS => by
    obtain ⟨hab, ha, hb, hps⟩ := h
    set t := tradeFn ps with ht
    have hta : ∀ e, a ∈ e → t e = 0 := fun e he => tradeFn_eq_zero_of_mem ha he
    have htb : ∀ e, b ∈ e → t e = 0 := fun e he => tradeFn_eq_zero_of_mem hb he
    have h1 : ∀ e : Finset V, (if a ∈ e ∧ b ∉ e then t (e.erase a) else 0) =
        (if a ∈ e then t (e.erase a) else 0) := by
      intro e
      by_cases hae : a ∈ e
      · by_cases hbe : b ∈ e
        · rw [if_neg (by tauto), if_pos hae, htb _ (mem_erase.2 ⟨Ne.symm hab, hbe⟩)]
        · rw [if_pos ⟨hae, hbe⟩, if_pos hae]
      · rw [if_neg (by tauto), if_neg hae]
    have h2 : ∀ e : Finset V, (if b ∈ e ∧ a ∉ e then t (e.erase b) else 0) =
        (if b ∈ e then t (e.erase b) else 0) := by
      intro e
      by_cases hbe : b ∈ e
      · by_cases hae : a ∈ e
        · rw [if_neg (by tauto), if_pos hbe, hta _ (mem_erase.2 ⟨hab, hae⟩)]
        · rw [if_pos ⟨hbe, hae⟩, if_pos hbe]
      · rw [if_neg (by tauto), if_neg hbe]
    have hw : wdeg (tradeFn ((a, b) :: ps)) S = wdeg t (S.erase a) - wdeg t (S.erase b) := by
      rw [← sum_erase_eq_wdeg hta, ← sum_erase_eq_wdeg htb, ← sum_sub_distrib, wdeg]
      refine sum_congr rfl fun e _ => ?_
      simp only [tradeFn]
      rw [h1, h2]
    rw [hw]
    simp only [List.length_cons] at hS
    by_cases haS : a ∈ S
    · by_cases hbS : b ∈ S
      · rw [wdeg_eq_zero_of_mem htb (mem_erase.2 ⟨Ne.symm hab, hbS⟩),
          wdeg_eq_zero_of_mem hta (mem_erase.2 ⟨hab, haS⟩), sub_zero]
      · rw [erase_eq_of_notMem hbS, wdeg_eq_zero_of_mem hta haS, sub_zero]
        refine wdeg_tradeFn hps _ ?_
        have := card_pos.2 ⟨a, haS⟩
        rw [card_erase_of_mem haS]; omega
    · by_cases hbS : b ∈ S
      · rw [erase_eq_of_notMem haS, wdeg_eq_zero_of_mem htb hbS, zero_sub, neg_eq_zero]
        refine wdeg_tradeFn hps _ ?_
        have := card_pos.2 ⟨b, hbS⟩
        rw [card_erase_of_mem hbS]; omega
      · rw [erase_eq_of_notMem haS, erase_eq_of_notMem hbS, sub_self]

/-- `f` vanishes off the `r`-sets. -/
def Supp (r : ℕ) (f : Finset V → ℤ) : Prop := ∀ e, f e ≠ 0 → e.card = r

/-- The null designs of uniformity `r` supported inside `U`, as a submodule. -/
def nullSub (r : ℕ) (U : Finset V) : Submodule ℤ (Finset V → ℤ) where
  carrier := {f | Supp r f ∧ (∀ S : Finset V, S.card < r → wdeg f S = 0) ∧
    ∀ e, f e ≠ 0 → e ⊆ U}
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨fun e he => ?_, fun S hS => by rw [wdeg_add, hf2 S hS, hg2 S hS, add_zero],
      fun e he => ?_⟩
    · by_cases h : f e = 0
      · exact hg1 e (by simpa [h] using he)
      · exact hf1 e h
    · by_cases h : f e = 0
      · exact hg3 e (by simpa [h] using he)
      · exact hf3 e h
  zero_mem' := ⟨fun e he => absurd rfl he, fun S _ => wdeg_zero S, fun e he => absurd rfl he⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    refine ⟨fun e he => hf1 e ?_, fun S hS => by rw [wdeg_smul, hf2 S hS, mul_zero],
      fun e he => hf3 e ?_⟩
    · intro h; apply he; simp [h]
    · intro h; apply he; simp [h]

/-- The integer span of the trades of uniformity `r` with all vertices in `U`. -/
def tradeSpan (r : ℕ) (U : Finset V) : Submodule ℤ (Finset V → ℤ) :=
  Submodule.span ℤ {g | ∃ ps : List (V × V), ps.length = r ∧ TValid ps ∧ tverts ps ⊆ U ∧
    g = tradeFn ps}

theorem tradeSpan_le_nullSub (r : ℕ) (U : Finset V) : tradeSpan r U ≤ nullSub r U := by
  refine Submodule.span_le.2 ?_
  rintro g ⟨ps, hlen, hv, hU, rfl⟩
  refine ⟨fun e he => (tradeFn_support he).2.trans hlen, fun S hS => wdeg_tradeFn hv S
    (hlen ▸ hS), fun e he => (tradeFn_support he).1.trans hU⟩

omit [Fintype V] in
theorem tradeSpan_mono (r : ℕ) {U U' : Finset V} (h : U ⊆ U') :
    tradeSpan r U ≤ tradeSpan r U' := by
  refine Submodule.span_mono ?_
  rintro g ⟨ps, hlen, hv, hU, rfl⟩
  exact ⟨ps, hlen, hv, hU.trans h, rfl⟩

/-- **Null designs on few vertices vanish.**  An `r`-supported function with vanishing degrees
at all sets of size `< r`, supported inside a set `U` of fewer than `2r` vertices, is zero
(inclusion–exclusion). -/
theorem null_eq_zero_of_card_lt {r : ℕ} {f : Finset V → ℤ} {U : Finset V} (hs : Supp r f)
    (hn : ∀ S : Finset V, S.card < r → wdeg f S = 0) (hU : ∀ e, f e ≠ 0 → e ⊆ U)
    (hcard : U.card < 2 * r) : f = 0 := by
  funext e₀
  by_contra hne
  have hc : e₀.card = r := hs e₀ hne
  have hsub : e₀ ⊆ U := hU e₀ hne
  set B := U \ e₀ with hB
  have hBc : B.card < r := by
    rw [hB, card_sdiff_of_subset hsub]; omega
  have hsum : ∑ T ∈ B.powerset, (-1 : ℤ) ^ T.card * wdeg f T = 0 := by
    refine sum_eq_zero fun T hT => ?_
    rw [hn T ((card_le_card (mem_powerset.1 hT)).trans_lt hBc), mul_zero]
  have hexp : ∑ T ∈ B.powerset, (-1 : ℤ) ^ T.card * wdeg f T =
      ∑ e : Finset V, f e * (if B ∩ e = ∅ then 1 else 0) := by
    simp only [wdeg, mul_sum]
    rw [sum_comm' (t' := univ) (s' := fun e => (B ∩ e).powerset)]
    · refine sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_powerset_neg_one_pow_card, mul_sum]
      refine sum_congr rfl fun T _ => by ring
    · intro T e
      simp only [mem_powerset, mem_filter, mem_univ, true_and, subset_inter_iff, and_true]
  rw [hexp] at hsum
  have hone : ∑ e : Finset V, f e * (if B ∩ e = ∅ then 1 else 0) = f e₀ := by
    rw [sum_eq_single e₀]
    · rw [if_pos, mul_one]
      rw [hB, eq_empty_iff_forall_notMem]
      intro x hx
      simp only [mem_inter, mem_sdiff] at hx
      exact hx.1.2 hx.2
    · intro e _ he
      by_cases hfe : f e = 0
      · rw [hfe, zero_mul]
      · have hec : e.card = r := hs e hfe
        have heU : e ⊆ U := hU e hfe
        rw [if_neg, mul_zero]
        intro hBe
        apply he
        have : e ⊆ e₀ := by
          intro x hx
          by_contra hx0
          have : x ∈ B ∩ e := mem_inter.2 ⟨mem_sdiff.2 ⟨heU hx, hx0⟩, hx⟩
          rw [hBe] at this
          simp at this
        exact eq_of_subset_of_card_le this (by omega)
    · intro h; exact absurd (mem_univ _) h
  rw [hone] at hsum
  exact hne hsum

/-- The link of `f` at `v`: `T ↦ f (T ∪ {v})` for `v ∉ T`. -/
def linkFn (f : Finset V → ℤ) (v : V) : Finset V → ℤ :=
  fun T => if v ∈ T then 0 else f (insert v T)

theorem wdeg_linkFn (f : Finset V → ℤ) (v : V) (S : Finset V) (hvS : v ∉ S) :
    wdeg (linkFn f v) S = wdeg f (insert v S) := by
  rw [wdeg, wdeg]
  have : ∑ e ∈ univ.filter (fun e => S ⊆ e), linkFn f v e =
      ∑ e ∈ univ.filter (fun e => S ⊆ e ∧ v ∉ e), f (insert v e) := by
    rw [← filter_filter, sum_filter (fun e => v ∉ e)]
    refine sum_congr rfl fun e _ => ?_
    simp only [linkFn]
    split_ifs <;> simp_all
  rw [this]
  refine sum_nbij' (fun e => insert v e) (fun e => e.erase v) ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    exact insert_subset_insert v he.1
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    refine ⟨?_, notMem_erase v e⟩
    intro y hy
    have hyv : y ≠ v := fun h => hvS (h ▸ hy)
    exact mem_erase.2 ⟨hyv, he (mem_insert_of_mem hy)⟩
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    exact erase_insert he.2
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    exact insert_erase (he (mem_insert_self v S))
  · intro e _; rfl

omit [Fintype V] in
/-- Lifting along a fresh vertex: every element `h` of the trade span of uniformity `r` inside
`U \ {v}` is the link at `v` of an element of the trade span of uniformity `r + 1` inside `U`,
provided `U \ {v}` has more than `2r` vertices. -/
theorem exists_lift {r : ℕ} {U : Finset V} {v : V} (hcard : 2 * r < (U.erase v).card)
    (hvU : v ∈ U) {h : Finset V → ℤ} (hh : h ∈ tradeSpan r (U.erase v)) :
    ∃ F ∈ tradeSpan (r + 1) U, ∀ e, v ∈ e → F e = h (e.erase v) := by
  induction hh using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨ps, hlen, hv, hU, rfl⟩ := hg
    have hlt : (tverts ps).card < (U.erase v).card := by
      rw [card_tverts hv, hlen]; exact hcard
    obtain ⟨w, hw, hwps⟩ := exists_mem_notMem_of_card_lt_card hlt
    have hwv : w ≠ v := (mem_erase.1 hw).1
    have hvps : v ∉ tverts ps := fun h' => by simpa using hU h'
    refine ⟨tradeFn ((v, w) :: ps), Submodule.subset_span ⟨(v, w) :: ps, by simp [hlen],
      ⟨Ne.symm hwv, hvps, hwps, hv⟩, ?_, rfl⟩, fun e he => ?_⟩
    · intro x hx
      simp only [tverts, mem_insert] at hx
      rcases hx with rfl | rfl | hx
      · exact hvU
      · exact (mem_erase.1 hw).2
      · exact (mem_erase.1 (hU hx)).2
    · simp only [tradeFn]
      by_cases hwe : w ∈ e
      · rw [if_neg (by tauto), if_neg (by tauto), sub_zero]
        exact (tradeFn_eq_zero_of_mem hwps (mem_erase.2 ⟨hwv, hwe⟩)).symm
      · rw [if_pos ⟨he, hwe⟩, if_neg (by tauto), sub_zero]
  | zero => exact ⟨0, Submodule.zero_mem _, fun e _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, hF'⟩ := hx
    obtain ⟨G, hG, hG'⟩ := hy
    exact ⟨F + G, Submodule.add_mem _ hF hG, fun e he => by simp [hF' e he, hG' e he]⟩
  | smul c x _ hx =>
    obtain ⟨F, hF, hF'⟩ := hx
    exact ⟨c • F, Submodule.smul_mem _ c hF, fun e he => by simp [hF' e he]⟩

/-- **Null designs are integer combinations of trades** (Graver–Jurkat).  Every null design of
uniformity `r` supported inside `U` lies in the integer span of the trades inside `U`. -/
theorem null_mem_tradeSpan : ∀ (r : ℕ) (U : Finset V) (f : Finset V → ℤ), f ∈ nullSub r U →
    f ∈ tradeSpan r U
  | 0, U, f, ⟨hs, _, _⟩ => by
    have hf : f = f ∅ • tradeFn ([] : List (V × V)) := by
      funext e
      by_cases he : e = ∅
      · subst he; simp [tradeFn]
      · have : f e = 0 := by
          by_contra h; exact he (card_eq_zero.1 (hs e h))
        simp [tradeFn, he, this]
    rw [hf]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl, trivial, by simp [tverts], rfl⟩)
  | r + 1, U, f, hf => by
    induction hc : U.card using Nat.strong_induction_on generalizing U f with
    | _ n ih =>
    obtain ⟨hs, hn, hU⟩ := hf
    by_cases hsmall : U.card < 2 * (r + 1)
    · rw [null_eq_zero_of_card_lt hs hn hU hsmall]; exact Submodule.zero_mem _
    push_neg at hsmall
    obtain ⟨v, hvU⟩ : U.Nonempty := card_pos.1 (by omega)
    have hcard : 2 * r < (U.erase v).card := by rw [card_erase_of_mem hvU]; omega
    have hg : linkFn f v ∈ nullSub r (U.erase v) := by
      refine ⟨fun T hT => ?_, fun S hS => ?_, fun T hT => ?_⟩
      · simp only [linkFn] at hT
        split_ifs at hT with hvT
        · exact absurd rfl hT
        · have := hs _ hT
          rw [card_insert_of_notMem hvT] at this; omega
      · by_cases hvS : v ∈ S
        · refine wdeg_eq_zero_of_mem (fun e he => ?_) hvS
          simp [linkFn, he]
        · rw [wdeg_linkFn f v S hvS]
          exact hn _ (by rw [card_insert_of_notMem hvS]; omega)
      · simp only [linkFn] at hT
        split_ifs at hT with hvT
        · exact absurd rfl hT
        · intro x hx
          have hxv : x ≠ v := fun h => hvT (h ▸ hx)
          exact mem_erase.2 ⟨hxv, hU _ hT (mem_insert_of_mem hx)⟩
    obtain ⟨F, hF, hFe⟩ := exists_lift hcard hvU (null_mem_tradeSpan r _ _ hg)
    obtain ⟨hFs, hFn, hFU⟩ := tradeSpan_le_nullSub _ _ hF
    have hf' : f - F ∈ nullSub (r + 1) (U.erase v) := by
      refine ⟨fun e he => ?_, fun S hS => by rw [wdeg_sub, hn S hS, hFn S hS, sub_zero],
        fun e he => ?_⟩
      · by_cases h : f e = 0
        · exact hFs e (by simpa [h] using he)
        · exact hs e h
      · have hvE : v ∉ e := by
          intro hve
          apply he
          rw [Pi.sub_apply, hFe e hve]
          simp only [linkFn, notMem_erase, if_false, insert_erase hve, sub_self]
        have heU : e ⊆ U := by
          by_cases h : f e = 0
          · exact hFU e (by simpa [h] using he)
          · exact hU e h
        intro x hx
        exact mem_erase.2 ⟨fun h => hvE (h ▸ hx), heU hx⟩
    have hlt : (U.erase v).card < n := by rw [card_erase_of_mem hvU]; omega
    have := ih _ hlt (U.erase v) (f - F) hf' rfl
    have h2 : f = (f - F) + F := by abel
    rw [h2]
    exact Submodule.add_mem _ (tradeSpan_mono _ (erase_subset v U) this) hF

end RefinedAbsorption.GJW
