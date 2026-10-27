module
public import RefinedAbsorption.OddGrid.Stage

/-!
# Divisibility in a stage

With weights `pw` compatible with the stage labels (`StagePW`):

* the switch pieces `P1` and the chain pieces are divisible (their class vanishes exactly);
* `ldiv_P0_walk`, `ldiv_P0_count`: the piece `P0 ℓ` is divisible when the rerouting of `ℓ` is a
  signed walk between the ends of `ℓ` with an odd number of steps, or a single bundle of weight
  `≡ 0 (mod q - 1)`;
* `sig_eq_sum`: the residual value of the chain on `e` is the sum over the present inputs of the
  weight they send to `e`;
* `ldiv_of_partition`, `ldiv_sup`: divisibility passes to residues and to disjoint unions.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner

variable {n K : ℕ}

/-- Compatibility of the weights with the labels of stage `t`. -/
structure StagePW (t : ℕ) (restF : RestF n K) (pw : Lab n K → Finset (Fin n) × ZMod K) :
    Prop where
  anti : ∀ ℓ, pw (.anti t ℓ) = ((pw ℓ).1, -(pw ℓ).2)
  rest : ∀ ℓ k, pw (.rest t ℓ k) = (restF ℓ).getD k (∅, 0)
  cp : ∀ e k s, pw (.cp t e k s) = (e, s)
  cn : ∀ e k s, pw (.cn t e k s) = (e, -s)

/-! ### Divisibility through partitions -/

section Partition

variable {Λ V : Type} [DecidableEq Λ] [DecidableEq V] {q : ℕ} {pw : Λ → Finset V × ZMod K}

lemma ldiv_union {P Q : Finset Λ} (h : Disjoint P Q) (hP : LDiv q pw P) (hQ : LDiv q pw Q) :
    LDiv q pw (P ∪ Q) := by
  unfold LDiv; rw [liftS_union]
  exact MIsDivisible.union (disjoint_liftS h) hP hQ

lemma ldiv_empty : LDiv q pw (∅ : Finset Λ) := by
  unfold LDiv; rw [liftS_empty]; exact mIsDivisible_empty q 2 _

lemma pd_image_liftS {𝒰 : Finset (Finset Λ)} (h : (𝒰 : Set (Finset Λ)).PairwiseDisjoint id) :
    ((𝒰.image (liftS (Λ := Λ) (V := V) (wsg pw)) : Finset (Finset (Λ × ℕ × ℕ))) :
      Set (Finset (Λ × ℕ × ℕ))).PairwiseDisjoint id := by
  intro W hW W' hW' hne
  simp only [coe_image, Set.mem_image, mem_coe] at hW hW'
  obtain ⟨P, hP, rfl⟩ := hW
  obtain ⟨P', hP', rfl⟩ := hW'
  have hPP : P ≠ P' := fun h => hne (by rw [h])
  exact disjoint_liftS (h hP hP' hPP)

lemma ldiv_sup {𝒰 : Finset (Finset Λ)} (h : (𝒰 : Set (Finset Λ)).PairwiseDisjoint id)
    (hd : ∀ P ∈ 𝒰, LDiv q pw P) : LDiv q pw (𝒰.sup id) := by
  unfold LDiv
  rw [← liftS_sup]
  intro S hS
  rw [mdeg_sup_eq_sum _ _ (pd_image_liftS h)]
  exact Finset.dvd_sum fun W hW => by
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    exact hd P hP S hS

lemma ldiv_of_partition {A Res : Finset Λ} {𝒰 : Finset (Finset Λ)} (hA : LDiv q pw A)
    (h : (𝒰 : Set (Finset Λ)).PairwiseDisjoint id) (hd : ∀ P ∈ 𝒰, LDiv q pw P)
    (hdj : Disjoint (𝒰.sup id) Res) (heq : 𝒰.sup id ∪ Res = A) : LDiv q pw Res := by
  unfold LDiv at *
  refine divisible_of_partition hA (pd_image_liftS (pw := pw) h) ?_ ?_ ?_
  · intro W hW
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    exact hd P hP
  · rw [liftS_sup]; exact disjoint_liftS hdj
  · rw [liftS_sup, ← liftS_union, heq]

/-- Labels of weight `0` have no copies. -/
lemma liftS_eq_empty {Q : Finset Λ} (h : ∀ ℓ ∈ Q, (pw ℓ).2 = 0) : liftS (wsg pw) Q = ∅ := by
  ext c
  simp only [mem_liftS, notMem_empty, iff_false, not_and]
  intro hc hs
  simp only [wsg, List.length_singleton, Nat.lt_one_iff] at hs
  simp [segAt, wsg, hs, h _ hc]

lemma ldiv_of_wt_zero {Q : Finset Λ} (h : ∀ ℓ ∈ Q, (pw ℓ).2 = 0) : LDiv q pw Q := by
  unfold LDiv; rw [liftS_eq_empty h]; exact mIsDivisible_empty q 2 _

end Partition

/-! ### Exact classes -/

section Exact

variable {Λ V : Type} [DecidableEq Λ] [DecidableEq V] [NeZero K] {q : ℕ}
  {pw : Λ → Finset V × ZMod K}

/-- A set of labels with exactly vanishing class is divisible. -/
lemma ldiv_of_exact (hd : q - 1 ∣ K) (hN : q.choose 2 ∣ K) {Q : Finset Λ}
    (h1 : ∀ v, cls pw Q v = 0) (h0 : tot pw Q = 0) : LDiv q pw Q :=
  ldiv_of_cls hd hN (fun v => by rw [h1 v, map_zero]) (by rw [h0, map_zero])

/-- Labels on one pair: the class is the total weight on that pair. -/
lemma cls_of_pair {Q : Finset Λ} {e : Finset V} (h : ∀ ℓ ∈ Q, (pw ℓ).1 = e) (v : V) :
    cls pw Q v = if v ∈ e then tot pw Q else 0 := by
  unfold cls tot
  split_ifs with hv
  · exact sum_congr rfl fun ℓ hℓ => by rw [h ℓ hℓ, if_pos hv]
  · exact sum_eq_zero fun ℓ hℓ => by rw [h ℓ hℓ, if_neg hv]

/-- Labels on one pair with total weight `0` are divisible. -/
lemma ldiv_of_pair (hd : q - 1 ∣ K) (hN : q.choose 2 ∣ K) {Q : Finset Λ} {e : Finset V}
    (h : ∀ ℓ ∈ Q, (pw ℓ).1 = e) (h0 : tot pw Q = 0) : LDiv q pw Q :=
  ldiv_of_exact hd hN (fun v => by rw [cls_of_pair h, h0, ite_self]) h0

end Exact

/-! ### The pieces of a stage -/

variable [NeZero K] {q : ℕ} (hd : q - 1 ∣ K) (hN : q.choose 2 ∣ K)
  {t : ℕ} {I : Finset (Lab n K)} {restF : RestF n K} {pw : Lab n K → Finset (Fin n) × ZMod K}

include hd hN in
lemma ldiv_P1 (hpw : StagePW t restF pw) (ℓ : Lab n K) : LDiv q pw (P1 t ℓ) := by
  apply ldiv_of_pair hd hN (e := (pw ℓ).1)
  · intro x hx
    simp only [P1, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · rfl
    · rw [hpw.anti]
  · have hne : ℓ ≠ Lab.anti t ℓ := by
      intro h
      have := congrArg sizeOf h
      simp at this
    simp [P1, tot, sum_pair hne, hpw.anti]

lemma pw_item (hpw : StagePW t restF pw) {e : Finset (Fin n)} {k : ℕ}
    (hk : k ∈ Icc 1 (slen t I restF e)) :
    pw (item t I restF e k) = (e, iw t I restF e k) := by
  obtain ⟨ℓ, -, j, -, hj⟩ := item_isRest hk
  have hon := mem_onPair.1 (item_mem hk)
  rw [iw]
  rw [hj] at hon ⊢
  rw [hpw.rest, ← hon.2]
  rfl

include hd hN in
lemma ldiv_chW (hpw : StagePW t restF pw) {e : Finset (Fin n)} {P : Finset (Lab n K)}
    (hP : P ∈ chW (Lab.cp t e) (Lab.cn t e) (item t I restF e) (iw t I restF e)
      (slen t I restF e)) : LDiv q pw P := by
  simp only [chW, mem_union, mem_biUnion, mem_filter, mem_product, mem_univ, and_true,
    mem_insert, mem_singleton, mem_image] at hP
  rcases hP with ⟨⟨k, s⟩, ⟨hk, -⟩, rfl | rfl⟩ | ⟨⟨k, s⟩, hk, rfl⟩
  · -- transition with the item
    obtain ⟨ℓ, -, j, -, hj⟩ := item_isRest hk
    have hpi := pw_item (I := I) hpw hk
    apply ldiv_of_pair hd hN (e := e)
    · intro x hx
      simp only [chT, if_true, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · rw [hpw.cp]
      · rw [hpi]
      · rw [hpw.cn]
    · simp only [chT, if_true]
      rw [hj] at hpi ⊢
      rw [tot, sum_insert (by simp), sum_insert (by simp), sum_singleton, hpw.cp, hpw.cn, hpi]
      ring
  · apply ldiv_of_pair hd hN (e := e)
    · intro x hx
      simp only [chT, Bool.false_eq_true, if_false, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [hpw.cp]
      · rw [hpw.cn]
    · simp only [chT, Bool.false_eq_true, if_false]
      rw [tot, sum_pair (by simp), hpw.cp, hpw.cn]
      ring
  · apply ldiv_of_pair hd hN (e := e)
    · intro x hx
      simp only [chQ, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [hpw.cn]
      · rw [hpw.cp]
    · rw [chQ, tot, sum_pair (by simp), hpw.cp, hpw.cn]
      ring

/-- The class of the rests of `ℓ`. -/
lemma cls_rests (hpw : StagePW t restF pw) (ℓ : Lab n K) (v : Fin n) :
    cls pw (rests t restF ℓ) v = lcls (restF ℓ) v := by
  rw [cls, rests, sum_image (fun a _ b _ h => by simpa using h)]
  simp only [hpw.rest]
  rw [lcls, ← sum_range_getD (restF ℓ) (∅, 0) (fun s => if v ∈ s.1 then s.2 else 0)]

lemma tot_rests (hpw : StagePW t restF pw) (ℓ : Lab n K) :
    tot pw (rests t restF ℓ) = ltot (restF ℓ) := by
  rw [tot, rests, sum_image (fun a _ b _ h => by simpa using h)]
  simp only [hpw.rest]
  rw [ltot, ← sum_range_getD (restF ℓ) (∅, 0) Prod.snd]

lemma anti_notMem_rests (ℓ : Lab n K) : Lab.anti t ℓ ∉ rests t restF ℓ := by
  simp [rests]

include hd hN in
/-- `P0` for a walk rerouting. -/
lemma ldiv_P0_walk (hpw : StagePW t restF pw) {ℓ : Lab n K} {p : Fin n} {tl : List (Fin n)}
    (hw : restF ℓ = walkL (p :: tl) (pw ℓ).2)
    (hch : (p :: tl).IsChain (· ≠ ·)) (hodd : ¬ Even tl.length)
    (hpr : (pw ℓ).1 = {p, (p :: tl).getLast (List.cons_ne_nil _ _)})
    (hne : p ≠ (p :: tl).getLast (List.cons_ne_nil _ _)) : LDiv q pw (P0 t restF ℓ) := by
  apply ldiv_of_exact hd hN
  · intro v
    rw [P0, ← Finset.singleton_union, cls_union pw (disjoint_singleton_left.2 (anti_notMem_rests ℓ)),
      cls_rests hpw, hw, lcls_walkL_odd p tl hch hodd]
    simp only [cls, sum_singleton, hpw.anti, hpr, mem_insert, mem_singleton]
    by_cases h1 : v = p
    · subst h1; simp [hne]
    · by_cases h2 : v = (p :: tl).getLast (List.cons_ne_nil _ _)
      · rw [h2] at h1 ⊢; simp [h1]
      · simp [h1, h2]
  · rw [P0, ← Finset.singleton_union, tot_union pw (disjoint_singleton_left.2 (anti_notMem_rests ℓ)),
      tot_rests hpw, hw, ltot_walkL, if_neg hodd]
    simp [tot, hpw.anti]

include hN in
/-- `P0` for a single count-only bundle. -/
lemma ldiv_P0_count (hpw : StagePW t restF pw) {ℓ : Lab n K} {f : Finset (Fin n)}
    (hw : restF ℓ = [(f, (pw ℓ).2)])
    (hs : ZMod.castHom hd (ZMod (q - 1)) (pw ℓ).2 = 0) : LDiv q pw (P0 t restF ℓ) := by
  apply ldiv_of_cls hd hN
  · intro v
    rw [P0, ← Finset.singleton_union, cls_union pw (disjoint_singleton_left.2 (anti_notMem_rests ℓ)),
      cls_rests hpw, hw]
    simp only [cls, sum_singleton, hpw.anti, lcls, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    have hs' : ((pw ℓ).2.cast : ZMod (q - 1)) = 0 := by rwa [ZMod.castHom_apply] at hs
    split_ifs <;> simp [hs, hs', ZMod.cast_neg hd]
  · rw [P0, ← Finset.singleton_union, tot_union pw (disjoint_singleton_left.2 (anti_notMem_rests ℓ)),
      tot_rests hpw, hw]
    simp [tot, hpw.anti, ltot]

/-! ### The residual values -/

/-- The weight sent by the input `ℓ` to the pair `e`. -/
def restMass (restF : RestF n K) (ℓ : Lab n K) (e : Finset (Fin n)) : ZMod K :=
  ∑ k ∈ (range (restF ℓ).length).filter (fun k => ((restF ℓ).getD k (∅, 0)).1 = e),
    ((restF ℓ).getD k (∅, 0)).2

lemma sig_eq_sum (e : Finset (Fin n)) (Ls : Finset (Lab n K)) (hLs : Ls ⊆ I) :
    sig t I restF e Ls = ∑ ℓ ∈ Ls, restMass restF ℓ e := by
  -- reindex the chain by its items
  have h1 : sig t I restF e Ls = ∑ i ∈ (onPair t I restF e).filter (fun i => src i ∈ Ls),
      restWt restF i := by
    rw [sig, psum, ← present_items, Finset.sum_image]
    swap
    · intro a ha b hb h
      exact item_inj (mem_filter.1 ha).1 (mem_filter.1 hb).1 h
    rw [sum_filter]
    have : Icc 1 (slen t I restF e) = (range (slen t I restF e)).image (· + 1) := by
      ext k; simp only [mem_Icc, mem_image, mem_range]
      constructor
      · intro h; exact ⟨k - 1, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩; omega
    rw [this, sum_image (fun a _ b _ h => by simpa using h)]
    rfl
  rw [h1]
  -- the present rests on `e`, grouped by their input
  have h2 : (onPair t I restF e).filter (fun i => src i ∈ Ls) =
      Ls.biUnion (fun ℓ => ((range (restF ℓ).length).filter
        (fun k => ((restF ℓ).getD k (∅, 0)).1 = e)).image (Lab.rest t ℓ)) := by
    ext x
    simp only [mem_filter, mem_onPair, mem_restSet, mem_biUnion, mem_image, mem_range]
    constructor
    · rintro ⟨⟨⟨ℓ, -, k, hk, rfl⟩, hp⟩, hs⟩
      exact ⟨ℓ, hs, k, ⟨hk, hp⟩, rfl⟩
    · rintro ⟨ℓ, hℓ, k, ⟨hk, hp⟩, rfl⟩
      exact ⟨⟨⟨ℓ, hLs hℓ, k, hk, rfl⟩, hp⟩, hℓ⟩
  rw [h2, sum_biUnion]
  · refine sum_congr rfl fun ℓ _ => ?_
    rw [restMass, sum_image (fun a _ b _ h => by simpa using h)]
    rfl
  · intro ℓ _ ℓ' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_image] at hx hx'
    obtain ⟨k, -, rfl⟩ := hx
    obtain ⟨k', -, h⟩ := hx'
    simp only [Lab.rest.injEq] at h
    exact hne h.2.1.symm

end RefinedAbsorption.OddGrid
