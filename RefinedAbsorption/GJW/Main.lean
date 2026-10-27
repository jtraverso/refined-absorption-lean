module
public import RefinedAbsorption.GJW.Trades
public import RefinedAbsorption.MultiAbsorber

/-!
# The theorem of Graver–Jurkat and Wilson (Theorem 3.2)

For `q > r ≥ 0` and a finite vertex type `V` with at least `q + r` elements, every
`K_q^r`-divisible integer-weighted `r`-graph is an integer combination of copies of `K_q^r`.
In particular, every `K_q^r`-divisible `r`-graph `L` with `v(L) ≥ q + r` has an integral
`K_q^r`-decomposition: `graverJurkatWilson : GraverJurkatWilson`.

Proof (by induction on `r`).  For `f` divisible of uniformity `r + 1`, the function
`F = ∂f / (q - r)` on `r`-sets (where `∂f(S) = ∑_{e ⊇ S} f e`) is `K_q^r`-divisible, so by
induction it is an integer combination `∑ c_Q K_Q^r`.  Then `h = ∑ c_Q K_Q^{r+1}` has the same
`r`-shadow as `f`, hence `f - h` is a null design.  Null designs are integer combinations of
trades (`null_mem_tradeSpan`), and every trade is an alternating sum of `2^{r+1}` copies of
`K_q^{r+1}` sharing a common `(q-r-1)`-set (this uses `|V| ≥ q + r + 1`).
-/

@[expose] public section

namespace RefinedAbsorption.GJW

open Finset

variable {V : Type*} [DecidableEq V]

/-- The (`r`-uniform) clique function of the vertex set `Q`. -/
def clq (r : ℕ) (Q : Finset V) : Finset V → ℤ := fun e => if e.card = r ∧ e ⊆ Q then 1 else 0

/-- Alternating sum of cliques `S ∪ {c₁,…,c_k}` over the transversals of a list of pairs. -/
def ksFn (r : ℕ) : List (V × V) → Finset V → Finset V → ℤ
  | [], S => clq r S
  | (a, b) :: ps, S => ksFn r ps (insert a S) - ksFn r ps (insert b S)

theorem ksFn_eq (r : ℕ) : ∀ {ps : List (V × V)} {S : Finset V}, TValid ps →
    Disjoint S (tverts ps) → ∀ e, ksFn r ps S e =
      if e.card = r ∧ e ⊆ S ∪ tverts ps then tradeFn ps (e \ S) else 0
  | [], S, _, _, e => by
    simp only [ksFn, clq, tverts, union_empty, tradeFn, sdiff_eq_empty_iff_subset]
    split_ifs <;> simp_all
  | (a, b) :: ps, S, hv, hd, e => by
    obtain ⟨hab, ha, hb, hps⟩ := hv
    have haS : a ∉ S := fun h => disjoint_left.1 hd h (by simp [tverts])
    have hbS : b ∉ S := fun h => disjoint_left.1 hd h (by simp [tverts])
    have hdP : Disjoint S (tverts ps) :=
      disjoint_of_subset_right (by intro x hx; simp [tverts, hx]) hd
    have hda : Disjoint (insert a S) (tverts ps) := disjoint_insert_left.2 ⟨ha, hdP⟩
    have hdb : Disjoint (insert b S) (tverts ps) := disjoint_insert_left.2 ⟨hb, hdP⟩
    simp only [ksFn, Pi.sub_apply]
    rw [ksFn_eq r hps hda, ksFn_eq r hps hdb]
    simp only [tradeFn, mem_sdiff, sdiff_insert]
    by_cases hae : a ∈ e <;> by_cases hbe : b ∈ e
    · have h1 : ¬ e ⊆ insert a S ∪ tverts ps := fun h => by
        have := h hbe
        simp only [mem_union, mem_insert] at this
        rcases this with (h' | h') | h'
        · exact hab h'.symm
        · exact hbS h'
        · exact hb h'
      have h2 : ¬ e ⊆ insert b S ∪ tverts ps := fun h => by
        have := h hae
        simp only [mem_union, mem_insert] at this
        rcases this with (h' | h') | h'
        · exact hab h'
        · exact haS h'
        · exact ha h'
      rw [insert_union] at h1 h2
      simp [h1, h2, hae, hbe, haS, hbS]
    · have h2 : ¬ e ⊆ insert b S ∪ tverts ps := fun h => by
        have := h hae
        simp only [mem_union, mem_insert] at this
        rcases this with (h' | h') | h'
        · exact hab h'
        · exact haS h'
        · exact ha h'
      have h3 : e ⊆ insert a S ∪ tverts ps ↔ e ⊆ S ∪ tverts ((a, b) :: ps) := by
        constructor
        · intro h x hx
          have := h hx
          simp only [mem_union, mem_insert, tverts] at this ⊢
          tauto
        · intro h x hx
          have := h hx
          simp only [mem_union, mem_insert, tverts] at this ⊢
          rcases this with h' | h' | h' | h'
          · tauto
          · tauto
          · exact absurd (h' ▸ hx) hbe
          · tauto
      simp only [h2, and_false, if_false, sub_zero, hae, haS, not_false_eq_true, and_true,
        hbe, false_and, if_true]
      by_cases hc : e.card = r
      · simp only [hc, true_and, h3]
      · simp [hc]
    · have h1 : ¬ e ⊆ insert a S ∪ tverts ps := fun h => by
        have := h hbe
        simp only [mem_union, mem_insert] at this
        rcases this with (h' | h') | h'
        · exact hab h'.symm
        · exact hbS h'
        · exact hb h'
      have h3 : e ⊆ insert b S ∪ tverts ps ↔ e ⊆ S ∪ tverts ((a, b) :: ps) := by
        constructor
        · intro h x hx
          have := h hx
          simp only [mem_union, mem_insert, tverts] at this ⊢
          tauto
        · intro h x hx
          have := h hx
          simp only [mem_union, mem_insert, tverts] at this ⊢
          rcases this with h' | h' | h' | h'
          · tauto
          · exact absurd (h' ▸ hx) hae
          · tauto
          · tauto
      simp only [h1, and_false, if_false, zero_sub, hae, hbS, not_false_eq_true, and_true,
        hbe, false_and, if_true]
      by_cases hc : e.card = r
      · simp only [hc, true_and, h3]
        split_ifs <;> simp
      · simp [hc]
    · have e1 : e \ insert a S = e \ S := sdiff_insert_of_notMem hae S
      have e2 : e \ insert b S = e \ S := sdiff_insert_of_notMem hbe S
      have h4 : (e ⊆ insert a S ∪ tverts ps) ↔ (e ⊆ insert b S ∪ tverts ps) := by
        constructor
        · intro h x hx
          have := h hx
          simp only [mem_union, mem_insert] at this ⊢
          rcases this with (h' | h') | h'
          · exact absurd (h' ▸ hx) hae
          · tauto
          · tauto
        · intro h x hx
          have := h hx
          simp only [mem_union, mem_insert] at this ⊢
          rcases this with (h' | h') | h'
          · exact absurd (h' ▸ hx) hbe
          · tauto
          · tauto
      rw [← sdiff_insert, ← sdiff_insert, e1, e2]
      simp only [hae, hbe, false_and, if_false, sub_zero, ite_self]
      by_cases hc : e.card = r
      · simp only [hc, true_and]
        simp only [h4, sub_self]
      · simp [hc]

variable [Fintype V]

/-- The integer span of the copies of `K_q^r` (the `r`-uniform clique functions of the
`q`-sets). -/
def Lam (q r : ℕ) : Submodule ℤ (Finset V → ℤ) :=
  Submodule.span ℤ (Set.range (fun Q : {Q : Finset V // Q.card = q} => clq r Q.1))

/-- `f` is `r`-supported and `K_q^r`-divisible. -/
def WDiv (q r : ℕ) (f : Finset V → ℤ) : Prop :=
  Supp r f ∧ ∀ S : Finset V, S.card < r → ((q - S.card).choose (r - S.card) : ℤ) ∣ wdeg f S

/-- The `r`-supported functions, as a submodule. -/
def suppSub (r : ℕ) : Submodule ℤ (Finset V → ℤ) where
  carrier := {f | Supp r f}
  add_mem' := by
    intro f g hf hg e he
    by_cases h : f e = 0
    · exact hg e (by simpa [h] using he)
    · exact hf e h
  zero_mem' := fun e he => absurd rfl he
  smul_mem' := by
    intro c f hf e he
    exact hf e (fun h => he (by simp [h]))

omit [Fintype V] in
theorem Lam_le_suppSub (q r : ℕ) : Lam (V := V) q r ≤ suppSub r := by
  refine Submodule.span_le.2 ?_
  rintro g ⟨Q, rfl⟩ e he
  simp only [clq, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at he
  exact he.1

omit [Fintype V] in
theorem ksFn_mem (q r : ℕ) : ∀ {ps : List (V × V)} {S : Finset V}, TValid ps →
    Disjoint S (tverts ps) → S.card + ps.length = q → ksFn r ps S ∈ Lam q r
  | [], S, _, _, hc => Submodule.subset_span ⟨⟨S, by simpa using hc⟩, rfl⟩
  | (a, b) :: ps, S, hv, hd, hc => by
    obtain ⟨hab, ha, hb, hps⟩ := hv
    have haS : a ∉ S := fun h => disjoint_left.1 hd h (by simp [tverts])
    have hbS : b ∉ S := fun h => disjoint_left.1 hd h (by simp [tverts])
    have hdP : Disjoint S (tverts ps) :=
      disjoint_of_subset_right (by intro x hx; simp [tverts, hx]) hd
    simp only [List.length_cons] at hc
    refine Submodule.sub_mem _ (ksFn_mem q r hps (disjoint_insert_left.2 ⟨ha, hdP⟩) ?_)
      (ksFn_mem q r hps (disjoint_insert_left.2 ⟨hb, hdP⟩) ?_)
    · rw [card_insert_of_notMem haS]; omega
    · rw [card_insert_of_notMem hbS]; omega

/-- Every trade of uniformity `r` is an integer combination of copies of `K_q^r`, provided
there are at least `q + r` vertices. -/
theorem tradeFn_mem_Lam {q r : ℕ} (hrq : r ≤ q) (hV : q + r ≤ Fintype.card V)
    {ps : List (V × V)} (hv : TValid ps) (hlen : ps.length = r) : tradeFn ps ∈ Lam q r := by
  have hc : q - r ≤ (univ \ tverts ps).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_tverts hv, hlen]; omega
  obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq hc
  have hd : Disjoint S (tverts ps) := by
    rw [disjoint_left]; intro x hx hx'
    exact (mem_sdiff.1 (hS hx)).2 hx'
  have heq : tradeFn ps = ksFn r ps S := by
    funext e
    rw [ksFn_eq r hv hd]
    by_cases ht : tradeFn ps e = 0
    · rw [ht]
      split_ifs with h
      · by_contra h'
        obtain ⟨-, hc'⟩ := tradeFn_support (Ne.symm h')
        have : e \ S = e := eq_of_subset_of_card_le sdiff_subset (by rw [hc', h.1, hlen])
        rw [this] at h'; exact h' ht.symm
      · rfl
    · obtain ⟨hs, hc'⟩ := tradeFn_support ht
      have hdes : e \ S = e := sdiff_eq_self_of_disjoint
        (disjoint_of_subset_left hs hd.symm)
      rw [if_pos ⟨hc'.trans hlen, hs.trans subset_union_right⟩, hdes]
  rw [heq]
  exact ksFn_mem q r hv hd (by omega)

theorem tradeSpan_le_Lam {q r : ℕ} (hrq : r ≤ q) (hV : q + r ≤ Fintype.card V) :
    tradeSpan r (univ : Finset V) ≤ Lam q r := by
  refine Submodule.span_le.2 ?_
  rintro g ⟨ps, hlen, hv, -, rfl⟩
  exact tradeFn_mem_Lam hrq hV hv hlen

/-- Double counting of degrees: for `f` supported on `(r+1)`-sets and `|S| ≤ r`, the sum of the
degrees of the `r`-sets containing `S` is `(r + 1 - |S|)` times the degree of `S`. -/
theorem sum_wdeg_supersets {r : ℕ} {f : Finset V → ℤ} (hf : Supp (r + 1) f) (S : Finset V)
    (hS : S.card ≤ r) :
    ∑ S' ∈ univ.filter (fun S' => S ⊆ S' ∧ S'.card = r), wdeg f S' =
      ((r + 1 - S.card : ℕ) : ℤ) * wdeg f S := by
  simp only [wdeg]
  rw [sum_comm' (t' := univ.filter (fun e => S ⊆ e))
    (s' := fun e => (e.powersetCard r).filter (fun S' => S ⊆ S'))]
  · rw [mul_sum]
    refine sum_congr rfl fun e he => ?_
    rw [sum_const, nsmul_eq_mul]
    by_cases hfe : f e = 0
    · rw [hfe, mul_zero, mul_zero]
    · have hec := hf e hfe
      rw [card_powersetCard_filter_superset (mem_filter.1 he).2 hS, hec]
      congr 2
      rw [show r + 1 - S.card = (r - S.card) + 1 by omega, Nat.choose_succ_self_right]
  · intro S' e
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h3, h2⟩, h1⟩, h1.trans h3⟩
    · rintro ⟨⟨⟨h3, h2⟩, h1⟩, _⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem wdeg_clq {r : ℕ} {Q S : Finset V} (hS : S.card ≤ r) :
    wdeg (clq r Q) S = if S ⊆ Q then (((Q.card - S.card).choose (r - S.card) : ℕ) : ℤ) else 0 := by
  have : wdeg (clq r Q) S = (((Q.powersetCard r).filter (fun e => S ⊆ e)).card : ℤ) := by
    simp only [wdeg, clq]
    rw [sum_boole]
    congr 2
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard]
    tauto
  rw [this]
  split_ifs with h
  · rw [card_powersetCard_filter_superset h hS]
  · rw [card_powersetCard_filter_superset_of_not h]; rfl

/-- Lifting cliques one uniformity up. -/
theorem exists_lift_Lam {q r : ℕ} {F : Finset V → ℤ} (hF : F ∈ Lam q r) :
    ∃ h ∈ Lam q (r + 1), ∀ S : Finset V, S.card = r → wdeg h S = ((q - r : ℕ) : ℤ) * F S := by
  induction hF using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨Q, hQ⟩, rfl⟩ := hg
    refine ⟨clq (r + 1) Q, Submodule.subset_span ⟨⟨Q, hQ⟩, rfl⟩, fun S hS => ?_⟩
    rw [wdeg_clq (by omega)]
    simp only [clq, hS, true_and, hQ]
    split_ifs
    · rw [show r + 1 - r = 1 by omega, Nat.choose_one_right]; ring
    · ring
  | zero => exact ⟨0, Submodule.zero_mem _, fun S _ => by simp [wdeg_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨h, hh, hh'⟩ := hx
    obtain ⟨k, hk, hk'⟩ := hy
    exact ⟨h + k, Submodule.add_mem _ hh hk, fun S hS => by
      rw [wdeg_add, hh' S hS, hk' S hS, Pi.add_apply]; ring⟩
  | smul c x _ hx =>
    obtain ⟨h, hh, hh'⟩ := hx
    exact ⟨c • h, Submodule.smul_mem _ c hh, fun S hS => by
      rw [wdeg_smul, hh' S hS, Pi.smul_apply, smul_eq_mul]; ring⟩

/-- **Graver–Jurkat, Wilson (weighted form).**  If `r < q` and `|V| ≥ q + r`, every
`r`-supported `K_q^r`-divisible integer function is an integer combination of copies of
`K_q^r`. -/
theorem wdiv_mem_Lam : ∀ (r : ℕ) {q : ℕ}, r < q → q + r ≤ Fintype.card V →
    ∀ f : Finset V → ℤ, WDiv q r f → f ∈ Lam q r
  | 0, q, _, hV, f, ⟨hs, _⟩ => by
    obtain ⟨Q, -, hQ⟩ := exists_subset_card_eq (s := (univ : Finset V)) (n := q)
      (by rw [card_univ]; omega)
    have hf : f = f ∅ • clq 0 Q := by
      funext e
      by_cases he : e = ∅
      · subst he; simp [clq]
      · have : f e = 0 := by
          by_contra h; exact he (card_eq_zero.1 (hs e h))
        simp [clq, card_eq_zero, he, this]
    rw [hf]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨Q, hQ⟩, rfl⟩)
  | r + 1, q, hrq, hV, f, ⟨hs, hd⟩ => by
    have hqr : (0 : ℤ) < ((q - r : ℕ) : ℤ) := by exact_mod_cast (by omega : 0 < q - r)
    set d : ℤ := ((q - r : ℕ) : ℤ) with hdd
    -- divisibility at level `r`
    have hdr : ∀ S : Finset V, S.card = r → d ∣ wdeg f S := by
      intro S hS
      have := hd S (by omega)
      rwa [hS, show r + 1 - r = 1 by omega, Nat.choose_one_right] at this
    set F : Finset V → ℤ := fun S => if S.card = r then wdeg f S / d else 0 with hFdef
    have hFmul : ∀ S, d * F S = if S.card = r then wdeg f S else 0 := by
      intro S
      simp only [hFdef]
      split_ifs with h
      · exact Int.mul_ediv_cancel' (hdr S h)
      · ring
    have hFdiv : WDiv q r F := by
      refine ⟨fun e he => ?_, fun S hS => ?_⟩
      · simp only [hFdef] at he; split_ifs at he with h
        · exact h
        · exact absurd rfl he
      · have hsum : d * wdeg F S = ((r + 1 - S.card : ℕ) : ℤ) * wdeg f S := by
          rw [← sum_wdeg_supersets hs S hS.le, wdeg, mul_sum]
          simp_rw [hFmul]
          rw [← sum_filter, filter_filter]
        obtain ⟨m, hm⟩ := hd S (by omega)
        have hid : (q - S.card).choose (r + 1 - S.card) * (r + 1 - S.card) =
            (q - S.card).choose (r - S.card) * (q - r) := by
          have := Nat.choose_succ_right_eq (q - S.card) (r - S.card)
          rw [show r - S.card + 1 = r + 1 - S.card by omega,
            show q - S.card - (r - S.card) = q - r by omega] at this
          exact this
        have hid' : ((r + 1 - S.card : ℕ) : ℤ) * ((q - S.card).choose (r + 1 - S.card) : ℤ) =
            d * ((q - S.card).choose (r - S.card) : ℤ) := by
          rw [hdd]; exact_mod_cast (by rw [mul_comm]; rw [hid]; ring)
        refine ⟨m, ?_⟩
        have : d * wdeg F S = d * (((q - S.card).choose (r - S.card) : ℤ) * m) := by
          rw [hsum, hm, ← mul_assoc, hid', mul_assoc]
        exact mul_left_cancel₀ hqr.ne' this
    have hFL := wdiv_mem_Lam r (by omega) (by omega) F hFdiv
    obtain ⟨h, hh, hh'⟩ := exists_lift_Lam hFL
    have hhs : Supp (r + 1) h := Lam_le_suppSub q (r + 1) hh
    have hgs : Supp (r + 1) (f - h) := Submodule.sub_mem (suppSub (r + 1))
      (show f ∈ suppSub (r + 1) from hs) hhs
    have hgr : ∀ S : Finset V, S.card = r → wdeg (f - h) S = 0 := by
      intro S hS
      rw [wdeg_sub, hh' S hS, hFmul S, if_pos hS, sub_self]
    have hg : f - h ∈ nullSub (r + 1) (univ : Finset V) := by
      refine ⟨hgs, fun S hS => ?_, fun e _ => subset_univ e⟩
      by_cases hSr : S.card = r
      · exact hgr S hSr
      · have := sum_wdeg_supersets hgs S (by omega)
        rw [sum_eq_zero (fun S' hS' => hgr S' (mem_filter.1 hS').2.2)] at this
        have hne : ((r + 1 - S.card : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega)
        exact (mul_eq_zero.1 this.symm).resolve_left hne
    have hgL := tradeSpan_le_Lam (q := q) (by omega) hV (null_mem_tradeSpan _ _ _ hg)
    have : f = (f - h) + h := by abel
    rw [this]
    exact Submodule.add_mem _ hgL hh

end RefinedAbsorption.GJW

namespace RefinedAbsorption

open Finset GJW

/-- **Theorem 3.2 (Graver–Jurkat, Wilson).**  For `q > r ≥ 1`, every `K_q^r`-divisible
`r`-graph `L` with `v(L) ≥ q + r` admits an integral `K_q^r`-decomposition. -/
theorem graverJurkatWilson : GraverJurkatWilson := by
  intro q r W _ _ L hr hrq hL hdiv hv
  have hV : q + r ≤ Fintype.card W := hv.trans (card_le_univ _)
  set f : Finset W → ℤ := fun e => if e ∈ L then 1 else 0 with hf
  have hwdeg : ∀ S, wdeg f S = (deg L S : ℤ) := by
    intro S
    rw [wdeg, hf]
    simp only
    rw [sum_boole, deg]
    congr 2
    ext e; simp [and_comm]
  have hfd : WDiv q r f := by
    refine ⟨fun e he => hL e ?_, fun S hS => ?_⟩
    · simp only [hf] at he; split_ifs at he with h
      · exact h
      · exact absurd rfl he
    · rw [hwdeg]; exact_mod_cast hdiv S hS
  have hmem := wdiv_mem_Lam r hrq hV f hfd
  rw [Lam, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨fun Q => if h : Q.card = q then c ⟨Q, h⟩ else 0, fun e he => ?_⟩
  have hce := congrFun hc e
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, clq, he, true_and, hf] at hce
  rw [← hce, sum_filter, sum_subtype (univ.powersetCard q) (p := fun Q => Q.card = q) (by simp)]
  refine sum_congr rfl fun Q _ => ?_
  obtain ⟨Q, hQ⟩ := Q
  simp only [hQ, dif_pos]
  split_ifs <;> simp

end RefinedAbsorption
