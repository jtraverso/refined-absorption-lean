module
public import RequestProject.FlatDown.Basic
public import RequestProject.RefinerOne.Chain
public import RequestProject.MultiRefiner.FakeEdge

/-!
# Refiners for multigraphs with few distinct edges

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Multiplicity Reduction Lemma).  Lean
formalization: Juan Pablo Traverso Gianini, Apache-2.0.

* `multReduction`: the 1-uniform chain construction applied to every class of parallel copies.
  For an `r`-multigraph `X`, new parallel copies `R` and pieces of `M = fakeModulus q r` copies of
  one edge form a residual refiner of `X` whose residue has at most `M` copies of every edge of
  `X`.  No new edge is created: every new copy is parallel to a copy of `X`.
* `finiteStep`: a multigraph with at most `K` copies is refined by the empty refiner, using all of
  its divisible sub-multigraphs as pieces.
* `smallRefiner`: the composition.  Every `r`-multigraph with at most `k` distinct edges has a
  `C`-refined multi-refiner (empty residue) made of parallel copies of its own edges, where `C`
  depends only on `q`, `r` and `k`.
-/

@[expose] public section

namespace RefinedAbsorption.FlatDown

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.ChainRefiner

/-! ### The finite step -/

section Finite

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

open Classical in
/-- **Finite step**: the empty refiner with all divisible sub-multigraphs as pieces. -/
theorem finiteStep {q r K : ℕ} {ends : E → Finset V} {X : Finset E} (hX : MIsRGraph r ends X)
    (hK : X.card ≤ K) :
    IsMultiRefiner q r (K + 2 ^ K) ends X ∅ (X.powerset.filter (MIsDivisible q r ends)) := by
  refine ⟨by simpa using hX, disjoint_empty_right _, fun W hW => (mem_filter.1 hW).2,
    fun W hW => by simpa using mem_powerset.1 (mem_filter.1 hW).1,
    fun W hW => ((card_le_card (mem_powerset.1 (mem_filter.1 hW).1)).trans hK).trans
      (Nat.le_add_right _ _), fun i _ => ?_, fun L hL hdiv => ?_⟩
  · calc _ ≤ (X.powerset.filter (MIsDivisible q r ends)).card := card_filter_le _ _
      _ ≤ X.powerset.card := card_filter_le _ _
      _ = 2 ^ X.card := card_powerset X
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
      _ ≤ K + 2 ^ K := Nat.le_add_left _ _
  · refine ⟨{L}, by simp [hL, hdiv], ∅, subset_rfl, mIsDivisible_empty q r ends, by simp,
      by simp, by simp⟩

end Finite

/-! ### Multiplicity reduction -/

section Mult

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- Labels of the new parallel copies: the edge and a chain label. -/
abbrev MLab (V : Type) := Finset V × ChainRefiner.Lab

variable (ends : E → Finset V) (X : Finset E)

/-- The copies of `X` parallel to `e`. -/
def cls (e : Finset V) : Finset E := X.filter fun x => ends x = e

/-- Combined ends. -/
def mEnds : E ⊕ MLab V → Finset V := Sum.elim ends Prod.fst

/-- The chain labels of the class `e`, realised as copies: the first `|cls e|` inputs are the
copies of `X` parallel to `e`, every other label is a new copy of `e`. -/
noncomputable def phi (e : Finset V) : ChainRefiner.Lab → E ⊕ MLab V
  | Sum.inl i => if h : i < (cls ends X e).card then
      Sum.inl ((cls ends X e).equivFin.symm ⟨i, h⟩).1 else Sum.inr (e, Sum.inl i)
  | Sum.inr p => Sum.inr (e, Sum.inr p)

variable {ends X}

omit [DecidableEq E] in
theorem mEnds_phi (e : Finset V) (a : ChainRefiner.Lab) : mEnds ends (phi ends X e a) = e := by
  rcases a with i | p
  · simp only [phi]
    split_ifs with h
    · simp only [mEnds, Sum.elim_inl]
      exact (mem_filter.1 ((cls ends X e).equivFin.symm ⟨i, h⟩).2).2
    · rfl
  · rfl

theorem phi_inj {e e' : Finset V} {a a' : ChainRefiner.Lab}
    (h : phi ends X e a = phi ends X e' a') : e = e' ∧ a = a' := by
  have hee : e = e' := by
    have := congrArg (mEnds ends) h
    rwa [mEnds_phi, mEnds_phi] at this
  subst hee
  refine ⟨rfl, ?_⟩
  rcases a with i | p <;> rcases a' with i' | p'
  · simp only [phi] at h
    split_ifs at h with h1 h2 h2 <;> simp_all
  · simp only [phi] at h
    split_ifs at h <;> simp_all
  · simp only [phi] at h
    split_ifs at h <;> simp_all
  · simp only [phi, Sum.inr.injEq, Prod.mk.injEq, true_and] at h
    rw [h]

omit [DecidableEq E] in
theorem phi_inl_lt {e : Finset V} {i : ℕ} (hi : i < (cls ends X e).card) :
    ∃ x ∈ cls ends X e, phi ends X e (Sum.inl i) = Sum.inl x := by
  refine ⟨((cls ends X e).equivFin.symm ⟨i, hi⟩).1, ((cls ends X e).equivFin.symm ⟨i, hi⟩).2, ?_⟩
  simp [phi, hi]

omit [DecidableEq E] in
theorem phi_inl_ge {e : Finset V} {i : ℕ} (hi : (cls ends X e).card ≤ i) :
    phi ends X e (Sum.inl i) = Sum.inr (e, Sum.inl i) := by
  simp [phi, not_lt.2 hi]

omit [DecidableEq E] in
theorem exists_phi_of_mem {x : E} (hx : x ∈ X) :
    ∃ i < (cls ends X (ends x)).card, phi ends X (ends x) (Sum.inl i) = Sum.inl x := by
  have hxc : x ∈ cls ends X (ends x) := mem_filter.2 ⟨hx, rfl⟩
  refine ⟨((cls ends X (ends x)).equivFin ⟨x, hxc⟩).1,
    ((cls ends X (ends x)).equivFin ⟨x, hxc⟩).2, ?_⟩
  simp [phi]

end Mult


section MultBuild

variable {V E : Type} [DecidableEq V] [DecidableEq E] (ends : E → Finset V) (X : Finset E)
  (M : ℕ)

/-- The chain length of the class `e`: its copies and `M` reserve inputs. -/
def clen (e : Finset V) : ℕ := (cls ends X e).card + M

/-- The reserve inputs of the class `e`. -/
def resIdx (e : Finset V) : Finset ℕ := Ico (cls ends X e).card (clen ends X M e)

/-- The new parallel copies. -/
def mR : Finset (MLab V) := (X.image ends).biUnion fun e =>
  (Rlab M (clen ends X M e) ∪ (resIdx ends X M e).image xl).image fun a => (e, a)

/-- The residue set: the reserve copies. -/
noncomputable def mY : Finset (E ⊕ MLab V) := (X.image ends).biUnion fun e =>
  (resIdx ends X M e).image fun i => phi ends X e (xl i)

/-- The pieces: the images of the chain pieces of every class. -/
noncomputable def mW : Finset (Finset (E ⊕ MLab V)) := (X.image ends).biUnion fun e =>
  insert ((finPiece M (clen ends X M e)).image (phi ends X e))
    ((Idx M (clen ends X M e)).image fun p => (piece M p.1 p.2.1 p.2.2).image (phi ends X e))

variable {ends X M}

omit [DecidableEq E] in
theorem phi_zl (e : Finset V) (k j : ℕ) : phi ends X e (zl k j) = Sum.inr (e, zl k j) := rfl

omit [DecidableEq E] in
theorem phi_of_mem_Rres {e : Finset V} {a : ChainRefiner.Lab}
    (ha : a ∈ Rlab M (clen ends X M e) ∪ (resIdx ends X M e).image xl) :
    phi ends X e a = Sum.inr (e, a) := by
  rcases mem_union.1 ha with ha | ha
  · rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
    · exact absurd ha not_mem_Rlab_xl
    · rfl
  · obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
    exact phi_inl_ge (mem_Ico.1 hi).1

theorem mem_mR_image {c : E ⊕ MLab V} : c ∈ (mR ends X M).image Sum.inr ↔
    ∃ e ∈ X.image ends, ∃ a ∈ Rlab M (clen ends X M e) ∪ (resIdx ends X M e).image xl,
      c = phi ends X e a := by
  constructor
  · intro hc
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
    obtain ⟨e, he, hy⟩ := mem_biUnion.1 hy
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hy
    exact ⟨e, he, a, ha, (phi_of_mem_Rres ha).symm⟩
  · rintro ⟨e, he, a, ha, rfl⟩
    rw [phi_of_mem_Rres ha]
    exact mem_image_of_mem _ (mem_biUnion.2 ⟨e, he, mem_image_of_mem _ ha⟩)

theorem mem_X_image {c : E ⊕ MLab V} : c ∈ X.image Sum.inl ↔
    ∃ e ∈ X.image ends, ∃ i < (cls ends X e).card, c = phi ends X e (xl i) := by
  constructor
  · intro hc
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
    obtain ⟨i, hi, h⟩ := exists_phi_of_mem (ends := ends) hx
    exact ⟨ends x, mem_image_of_mem _ hx, i, hi, h.symm⟩
  · rintro ⟨e, -, i, hi, rfl⟩
    obtain ⟨x, hx, h⟩ := phi_inl_lt (ends := ends) (X := X) hi
    rw [xl, h]
    exact mem_image_of_mem _ (mem_filter.1 hx).1

/-- Every copy of `X ∪ R` is the image of a label of the universe of its class. -/
theorem mem_XR {c : E ⊕ MLab V} : c ∈ X.image Sum.inl ∪ (mR ends X M).image Sum.inr ↔
    ∃ e ∈ X.image ends, ∃ a ∈ Rlab M (clen ends X M e) ∪ Xlab (clen ends X M e),
      c = phi ends X e a := by
  rw [mem_union, mem_X_image (ends := ends), mem_mR_image]
  constructor
  · rintro (⟨e, he, i, hi, rfl⟩ | ⟨e, he, a, ha, rfl⟩)
    · exact ⟨e, he, xl i, mem_union_right _ (mem_Xlab_xl.2 (by unfold clen; omega)), rfl⟩
    · refine ⟨e, he, a, ?_, rfl⟩
      rcases mem_union.1 ha with ha | ha
      · exact mem_union_left _ ha
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
        exact mem_union_right _ (mem_Xlab_xl.2 (mem_Ico.1 hi).2)
  · rintro ⟨e, he, a, ha, rfl⟩
    rcases mem_union.1 ha with ha | ha
    · exact Or.inr ⟨e, he, a, mem_union_left _ ha, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
      have hi' := mem_range.1 hi
      by_cases h : i < (cls ends X e).card
      · exact Or.inl ⟨e, he, i, h, rfl⟩
      · exact Or.inr ⟨e, he, xl i, mem_union_right _ (mem_image_of_mem _
          (mem_Ico.2 ⟨by omega, hi'⟩)), rfl⟩

theorem card_image_phi (e : Finset V) (P : Finset ChainRefiner.Lab) :
    (P.image (phi ends X e)).card = P.card :=
  card_image_of_injective _ fun _ _ h => (phi_inj h).2

theorem mdeg_image_phi (e : Finset V) (P : Finset ChainRefiner.Lab) (S : Finset V) :
    mdeg (mEnds ends) (P.image (phi ends X e)) S = if S ⊆ e then P.card else 0 := by
  unfold mdeg
  split_ifs with h
  · rw [filter_true_of_mem fun c hc => by
      obtain ⟨a, -, rfl⟩ := mem_image.1 hc
      rw [mEnds_phi]; exact h]
    exact card_image_phi e P
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro c hc
    obtain ⟨a, -, rfl⟩ := mem_image.1 hc
    rw [mEnds_phi]; exact h

/-- Degrees as sums over the classes. -/
theorem mdeg_eq_sum_cls (G : Finset (E ⊕ MLab V)) (hG : ∀ c ∈ G, mEnds ends c ∈ X.image ends)
    (S : Finset V) : mdeg (mEnds ends) G S =
      ∑ e ∈ X.image ends, if S ⊆ e then (G.filter fun c => mEnds ends c = e).card else 0 := by
  unfold mdeg
  rw [card_eq_sum_card_fiberwise (f := mEnds ends) (t := X.image ends)
    (fun c hc => hG c (mem_filter.1 hc).1)]
  refine sum_congr rfl fun e _ => ?_
  rw [filter_filter]
  split_ifs with h
  · congr 1
    exact filter_congr fun c _ => ⟨fun h' => h'.2, fun h' => ⟨h' ▸ h, h'⟩⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro c - ⟨h1, h2⟩
    exact h (h2 ▸ h1)

end MultBuild

section MultMain

variable {V E : Type} [DecidableEq V] [DecidableEq E] {ends : E → Finset V} {X : Finset E}
  {M : ℕ}

/-- The input bits of the chain of the class `e` selected by `L`: the copies of `X` in `L`, then
as many reserve inputs as needed to reach a multiple of `M`. -/
noncomputable def selBit (ends : E → Finset V) (X : Finset E) (M : ℕ) (L : Finset (E ⊕ MLab V))
    (e : Finset V) (i : ℕ) : Bool :=
  if i < (cls ends X e).card then decide (phi ends X e (xl i) ∈ L)
  else decide (i - (cls ends X e).card <
    (M - (L.filter fun c => mEnds ends c = e).card % M) % M)

theorem card_filter_sel_lt {L : Finset (E ⊕ MLab V)} (hL : L ⊆ X.image Sum.inl) (e : Finset V) :
    ((range (cls ends X e).card).filter fun i => selBit ends X M L e i = true).card =
      (L.filter fun c => mEnds ends c = e).card := by
  refine card_bij (fun i _ => phi ends X e (xl i)) ?_ ?_ ?_
  · intro i hi
    obtain ⟨hi, hb⟩ := mem_filter.1 hi
    have hi' := mem_range.1 hi
    simp only [selBit, hi', if_true, decide_eq_true_eq] at hb
    exact mem_filter.2 ⟨hb, mEnds_phi e _⟩
  · intro i _ j _ h
    have := (phi_inj h).2
    simpa [xl] using this
  · intro c hc
    obtain ⟨hcL, hce⟩ := mem_filter.1 hc
    obtain ⟨x, hx, rfl⟩ := mem_image.1 (hL hcL)
    have hxe : ends x = e := hce
    subst hxe
    obtain ⟨i, hi, h⟩ := exists_phi_of_mem (ends := ends) hx
    refine ⟨i, mem_filter.2 ⟨mem_range.2 hi, ?_⟩, h⟩
    simp only [selBit, hi, if_true, decide_eq_true_eq]
    rw [xl, h]; exact hcL

theorem filter_sel_Ico_true (L : Finset (E ⊕ MLab V)) (e : Finset V) {k : ℕ}
    (hk : k = (M - (L.filter fun c => mEnds ends c = e).card % M) % M) :
    ((resIdx ends X M e).filter fun i => selBit ends X M L e i = true) =
      Ico (cls ends X e).card ((cls ends X e).card + k) := by
  ext i
  simp only [resIdx, clen, mem_filter, mem_Ico, selBit]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    simp only [show ¬ i < (cls ends X e).card by omega, if_false, decide_eq_true_eq] at h3
    omega
  · rintro ⟨h1, h2⟩
    have : k ≤ M := by
      rcases Nat.eq_zero_or_pos M with h0 | h0
      · subst h0; simp at hk; omega
      · rw [hk]; exact (Nat.mod_lt _ h0).le
    refine ⟨⟨h1, by omega⟩, ?_⟩
    simp only [show ¬ i < (cls ends X e).card by omega, if_false, decide_eq_true_eq]
    omega

theorem filter_sel_Ico_false (L : Finset (E ⊕ MLab V)) (e : Finset V) {k : ℕ}
    (hk : k = (M - (L.filter fun c => mEnds ends c = e).card % M) % M) :
    ((resIdx ends X M e).filter fun i => selBit ends X M L e i = false) =
      Ico ((cls ends X e).card + k) ((cls ends X e).card + M) := by
  ext i
  simp only [resIdx, clen, mem_filter, mem_Ico, selBit]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    simp only [show ¬ i < (cls ends X e).card by omega, if_false, decide_eq_false_iff_not,
      not_lt] at h3
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨by omega, h2⟩, ?_⟩
    simp only [show ¬ i < (cls ends X e).card by omega, if_false, decide_eq_false_iff_not,
      not_lt]
    omega

theorem mod_add_pad (hM : 1 ≤ M) (c : ℕ) : M ∣ c + (M - c % M) % M := by
  by_cases h0 : c % M = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self, add_zero]; exact Nat.dvd_of_mod_eq_zero h0
  · have hlt : c % M < M := Nat.mod_lt _ (by omega)
    rw [Nat.mod_eq_of_lt (show M - c % M < M by omega)]
    have := Nat.div_add_mod c M
    exact ⟨c / M + 1, by rw [Nat.mul_add, mul_one]; omega⟩

theorem sub_pad_modEq (hM : 1 ≤ M) (c : ℕ) : M - (M - c % M) % M ≡ c [MOD M] := by
  by_cases h0 : c % M = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.sub_zero]
    unfold Nat.ModEq; rw [Nat.mod_self, h0]
  · have hlt : c % M < M := Nat.mod_lt _ (by omega)
    rw [Nat.mod_eq_of_lt (show M - c % M < M by omega), show M - (M - c % M) = c % M by omega]
    exact Nat.mod_modEq c M

theorem cnt_selBit (hM : 1 ≤ M) {L : Finset (E ⊕ MLab V)} (hL : L ⊆ X.image Sum.inl)
    (e : Finset V) : M ∣ cnt (selBit ends X M L e) (clen ends X M e) := by
  set c := (L.filter fun c => mEnds ends c = e).card
  rw [cnt_eq_card, Llab, card_image_of_injective _ (fun a b h => xl_inj.1 h)]
  have hsplit : (range (clen ends X M e)).filter (fun i => selBit ends X M L e i) =
      (range (cls ends X e).card).filter (fun i => selBit ends X M L e i = true) ∪
        (resIdx ends X M e).filter (fun i => selBit ends X M L e i = true) := by
    ext i
    simp only [mem_filter, mem_range, mem_union, resIdx, clen, mem_Ico]
    by_cases h : selBit ends X M L e i = true
    · simp only [h, and_true]; omega
    · simp [h]
  rw [hsplit, card_union_of_disjoint (disjoint_filter_filter (by
      rw [disjoint_left]; intro i hi hi'
      simp only [mem_range, resIdx, mem_Ico] at hi hi'; omega)),
    card_filter_sel_lt hL, filter_sel_Ico_true L e rfl, Nat.card_Ico, Nat.add_sub_cancel_left]
  exact mod_add_pad hM c

/-- **Multiplicity reduction.**  For `1 ≤ M` divisible by every `binom(q-s, r-s)` (`s < r`),
the new parallel copies `mR` refine `X` with residue in the reserve copies `mY` (at most `M`
copies of each edge of `X`); every copy lies in at most `4M + 1` pieces, each with at most `M`
copies of one edge. -/
theorem multReduction {q r : ℕ} (hM : 1 ≤ M) (hdvd : ∀ s < r, (q - s).choose (r - s) ∣ M)
    (hX : MIsRGraph r ends X) :
    IsResidualMultiRefiner q r (5 * M + 1) (mEnds ends) (X.image Sum.inl)
      ((mR ends X M).image Sum.inr) (mY ends X M) (mW ends X M) := by
  -- pieces of the family
  have hW : ∀ W ∈ mW ends X M, ∃ e ∈ X.image ends, ∃ P : Finset ChainRefiner.Lab,
      W = P.image (phi ends X e) ∧ P ⊆ Rlab M (clen ends X M e) ∪ Xlab (clen ends X M e) ∧
      (P.card = 0 ∨ P.card = M) := by
    intro W hW
    obtain ⟨e, he, hW⟩ := mem_biUnion.1 hW
    rcases mem_insert.1 hW with rfl | hW
    · refine ⟨e, he, _, rfl, finPiece_subset hM, ?_⟩
      rw [card_finPiece hM]; split_ifs <;> simp
    · obtain ⟨⟨i, t, b⟩, hp, rfl⟩ := mem_image.1 hW
      simp only [Idx, mem_product, mem_range, mem_univ, and_true] at hp
      refine ⟨e, he, _, rfl, piece_subset hM hp.1 hp.2, ?_⟩
      rw [card_piece hM hp.2]; split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨e, he, a, -, rfl⟩ := mem_XR.1 hc
    rw [mEnds_phi]
    obtain ⟨x, hx, rfl⟩ := mem_image.1 he
    exact hX x hx
  · rw [disjoint_left]
    intro c hc hc'
    obtain ⟨x, -, rfl⟩ := mem_image.1 hc
    obtain ⟨y, -, h⟩ := mem_image.1 hc'
    cases h
  · intro W hW' S hS
    obtain ⟨e, -, P, rfl, -, hP⟩ := hW W hW'
    rw [mdeg_image_phi]
    split_ifs
    · rcases hP with h | h <;> rw [h]
      · exact dvd_zero _
      · exact hdvd _ hS
    · exact dvd_zero _
  · intro W hW' c hc
    obtain ⟨e, he, P, rfl, hPs, -⟩ := hW W hW'
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
    exact mem_XR.2 ⟨e, he, a, hPs ha, rfl⟩
  · intro W hW'
    obtain ⟨e, -, P, rfl, -, hP⟩ := hW W hW'
    rw [card_image_phi]
    rcases hP with h | h <;> rw [h] <;> omega
  · intro c hc
    obtain ⟨e, he, a, -, rfl⟩ := mem_XR.1 hc
    have hsub : (mW ends X M).filter (fun W => phi ends X e a ∈ W) ⊆
        insert ((finPiece M (clen ends X M e)).image (phi ends X e))
          (((Idx M (clen ends X M e)).filter fun p => a ∈ piece M p.1 p.2.1 p.2.2).image
            fun p => (piece M p.1 p.2.1 p.2.2).image (phi ends X e)) := by
      intro W hW'
      obtain ⟨hW', hcW⟩ := mem_filter.1 hW'
      obtain ⟨e', -, hW'⟩ := mem_biUnion.1 hW'
      rcases mem_insert.1 hW' with rfl | hW'
      · obtain ⟨a', -, h⟩ := mem_image.1 hcW
        obtain ⟨rfl, -⟩ := phi_inj h
        exact mem_insert_self _ _
      · obtain ⟨p, hp, rfl⟩ := mem_image.1 hW'
        obtain ⟨a', ha', h⟩ := mem_image.1 hcW
        obtain ⟨rfl, rfl⟩ := phi_inj h
        exact mem_insert_of_mem (mem_image_of_mem _ (mem_filter.2 ⟨hp, ha'⟩))
    refine (card_le_card hsub).trans ((card_insert_le _ _).trans ?_)
    have := card_filter_piece_le M (clen ends X M e) a
    have := card_image_le (s := (Idx M (clen ends X M e)).filter fun p =>
      a ∈ piece M p.1 p.2.1 p.2.2) (f := fun p => (piece M p.1 p.2.1 p.2.2).image (phi ends X e))
    omega
  · intro L hL hLdiv
    set b := selBit ends X M L with hb
    have hcnt : ∀ e, M ∣ cnt (b e) (clen ends X M e) := fun e => cnt_selBit hM hL e
    set 𝒰 : Finset (Finset (E ⊕ MLab V)) := (X.image ends).biUnion fun e =>
      insert ((finPiece M (clen ends X M e)).image (phi ends X e))
        ((range (clen ends X M e)).image fun i => (chosen M (b e) i).image (phi ends X e))
      with h𝒰
    set Res : Finset (E ⊕ MLab V) := (X.image ends).biUnion fun e =>
      ((resIdx ends X M e).filter fun i => b e i = false).image fun i => phi ends X e (xl i)
      with hRes
    have hW𝒰 : ∀ W ∈ 𝒰, ∃ e ∈ X.image ends, (W = (finPiece M (clen ends X M e)).image
        (phi ends X e)) ∨ ∃ i < clen ends X M e, W = (chosen M (b e) i).image (phi ends X e) := by
      intro W hW'
      obtain ⟨e, he, hW'⟩ := mem_biUnion.1 hW'
      rcases mem_insert.1 hW' with rfl | hW'
      · exact ⟨e, he, Or.inl rfl⟩
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 hW'
        exact ⟨e, he, Or.inr ⟨i, mem_range.1 hi, rfl⟩⟩
    have hsup : ∀ c, c ∈ 𝒰.sup id ↔ ∃ e ∈ X.image ends,
        ∃ a ∈ Rlab M (clen ends X M e) ∪ Llab (b e) (clen ends X M e), c = phi ends X e a := by
      intro c
      rw [mem_sup]
      constructor
      · rintro ⟨W, hW', hcW⟩
        obtain ⟨e, he, rfl | ⟨i, hi, rfl⟩⟩ := hW𝒰 W hW'
        · obtain ⟨a, ha, rfl⟩ := mem_image.1 hcW
          exact ⟨e, he, a, (cover hM (b e) _ (hcnt e) a).1 (Or.inr ha), rfl⟩
        · obtain ⟨a, ha, rfl⟩ := mem_image.1 hcW
          exact ⟨e, he, a, (cover hM (b e) _ (hcnt e) a).1 (Or.inl ⟨i, hi, ha⟩), rfl⟩
      · rintro ⟨e, he, a, ha, rfl⟩
        rcases (cover hM (b e) _ (hcnt e) a).2 ha with ⟨i, hi, ha⟩ | ha
        · exact ⟨_, mem_biUnion.2 ⟨e, he, mem_insert_of_mem (mem_image_of_mem _
            (mem_range.2 hi))⟩, mem_image_of_mem _ ha⟩
        · exact ⟨_, mem_biUnion.2 ⟨e, he, mem_insert_self _ _⟩, mem_image_of_mem _ ha⟩
    have hres : ∀ c, c ∈ Res ↔ ∃ e ∈ X.image ends, ∃ i ∈ resIdx ends X M e,
        b e i = false ∧ c = phi ends X e (xl i) := by
      intro c
      simp only [hRes, mem_biUnion, mem_image, mem_filter]
      constructor
      · rintro ⟨e, he, i, ⟨hi, hbi⟩, rfl⟩; exact ⟨e, he, i, hi, hbi, rfl⟩
      · rintro ⟨e, he, i, hi, hbi, rfl⟩; exact ⟨e, he, i, ⟨hi, hbi⟩, rfl⟩
    have hdisj : Disjoint (𝒰.sup id) Res := by
      rw [disjoint_left]
      intro c hc hc'
      obtain ⟨e, -, a, ha, rfl⟩ := (hsup c).1 hc
      obtain ⟨e', -, i, -, hbi, h⟩ := (hres _).1 hc'
      obtain ⟨rfl, rfl⟩ := phi_inj h
      rcases mem_union.1 ha with ha | ha
      · exact not_mem_Rlab_xl ha
      · rw [mem_Llab_xl] at ha
        rw [ha.2] at hbi; cases hbi
    refine ⟨𝒰, ?_, Res, ?_, ?_, ?_, hdisj, ?_⟩
    · intro W hW'
      obtain ⟨e, he, hW'⟩ := mem_biUnion.1 hW'
      refine mem_biUnion.2 ⟨e, he, ?_⟩
      rcases mem_insert.1 hW' with rfl | hW'
      · exact mem_insert_self _ _
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 hW'
        refine mem_insert_of_mem (mem_image.2 ⟨(i, tSeq M (b e) i, b e i), ?_, rfl⟩)
        simp only [Idx, mem_product, mem_range, mem_univ, and_true]
        exact ⟨mem_range.1 hi, tSeq_lt hM _ _⟩
    · intro c hc
      obtain ⟨e, he, i, hi, -, rfl⟩ := (hres c).1 hc
      exact mem_biUnion.2 ⟨e, he, mem_image_of_mem _ hi⟩
    · -- the residue is divisible
      intro S hS
      have hcl_res : ∀ c ∈ Res, mEnds ends c ∈ X.image ends := by
        intro c hc
        obtain ⟨e, he, i, -, -, rfl⟩ := (hres c).1 hc
        rwa [mEnds_phi]
      have hcl_L : ∀ c ∈ L, mEnds ends c ∈ X.image ends := by
        intro c hc
        obtain ⟨x, hx, rfl⟩ := mem_image.1 (hL hc)
        exact mem_image_of_mem _ hx
      have hfib : ∀ e ∈ X.image ends, (Res.filter fun c => mEnds ends c = e).card =
          M - (M - (L.filter fun c => mEnds ends c = e).card % M) % M := by
        intro e he
        have : Res.filter (fun c => mEnds ends c = e) =
            ((resIdx ends X M e).filter fun i => b e i = false).image
              fun i => phi ends X e (xl i) := by
          ext c
          rw [mem_filter, hres]
          constructor
          · rintro ⟨⟨e', -, i, hi, hbi, rfl⟩, hce⟩
            rw [mEnds_phi] at hce; subst hce
            exact mem_image_of_mem _ (mem_filter.2 ⟨hi, hbi⟩)
          · intro hc
            obtain ⟨i, hi, rfl⟩ := mem_image.1 hc
            obtain ⟨hi, hbi⟩ := mem_filter.1 hi
            exact ⟨⟨e, he, i, hi, hbi, rfl⟩, mEnds_phi _ _⟩
        rw [this, card_image_of_injective _ (fun i j h => by simpa [xl] using (phi_inj h).2),
          hb, filter_sel_Ico_false L e rfl, Nat.card_Ico]
        omega
      have hmod : mdeg (mEnds ends) Res S ≡ mdeg (mEnds ends) L S [MOD M] := by
        rw [mdeg_eq_sum_cls Res hcl_res, mdeg_eq_sum_cls L hcl_L]
        refine Nat.ModEq.sum fun e he => ?_
        split_ifs
        · rw [hfib e he]; exact sub_pad_modEq hM _
        · rfl
      exact (hmod.dvd_iff (hdvd _ hS)).2 (hLdiv S hS)
    · -- pairwise disjointness
      intro W hW' W' hW'' hne
      show Disjoint W W'
      rw [disjoint_left]
      intro c hc hc'
      apply hne
      obtain ⟨e, -, hWe⟩ := hW𝒰 W hW'
      obtain ⟨e', -, hWe'⟩ := hW𝒰 W' hW''
      rcases hWe with rfl | ⟨i, hi, rfl⟩ <;> rcases hWe' with rfl | ⟨i', hi', rfl⟩
      · obtain ⟨a, -, h⟩ := mem_image.1 hc
        obtain ⟨a', -, h'⟩ := mem_image.1 hc'
        obtain ⟨rfl, -⟩ := phi_inj (h.trans h'.symm)
        rfl
      · obtain ⟨a, ha, h⟩ := mem_image.1 hc
        obtain ⟨a', ha', h'⟩ := mem_image.1 hc'
        obtain ⟨rfl, rfl⟩ := phi_inj (h.trans h'.symm)
        exact absurd ha (chosen_not_fin hM (hcnt e) hi' ha')
      · obtain ⟨a, ha, h⟩ := mem_image.1 hc
        obtain ⟨a', ha', h'⟩ := mem_image.1 hc'
        obtain ⟨rfl, rfl⟩ := phi_inj (h.trans h'.symm)
        exact absurd ha' (chosen_not_fin hM (hcnt e) hi ha)
      · obtain ⟨a, ha, h⟩ := mem_image.1 hc
        obtain ⟨a', ha', h'⟩ := mem_image.1 hc'
        obtain ⟨rfl, rfl⟩ := phi_inj (h.trans h'.symm)
        rw [chosen_unique ha ha']
    · -- the union
      ext c
      rw [mem_union, mem_union, hsup, hres, mem_mR_image]
      constructor
      · rintro (⟨e, he, a, ha, rfl⟩ | ⟨e, he, i, hi, -, rfl⟩)
        · rcases mem_union.1 ha with ha | ha
          · exact Or.inl ⟨e, he, a, mem_union_left _ ha, rfl⟩
          · obtain ⟨k, rfl⟩ : ∃ k, a = xl k := by
              rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
              · exact ⟨k, rfl⟩
              · exact absurd ha not_mem_Llab_zl
            obtain ⟨hk, hbk⟩ := mem_Llab_xl.1 ha
            by_cases hkc : k < (cls ends X e).card
            · right
              simp only [hb, selBit, hkc, if_true, decide_eq_true_eq] at hbk
              exact hbk
            · exact Or.inl ⟨e, he, xl k, mem_union_right _ (mem_image_of_mem _
                (mem_Ico.2 ⟨by omega, hk⟩)), rfl⟩
        · exact Or.inl ⟨e, he, xl i, mem_union_right _ (mem_image_of_mem _ hi), rfl⟩
      · rintro (⟨e, he, a, ha, rfl⟩ | hcL)
        · rcases mem_union.1 ha with ha | ha
          · exact Or.inl ⟨e, he, a, mem_union_left _ ha, rfl⟩
          · obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
            cases hbi : b e i
            · exact Or.inr ⟨e, he, i, hi, hbi, rfl⟩
            · exact Or.inl ⟨e, he, xl i, mem_union_right _ (mem_Llab_xl.2
                ⟨(mem_Ico.1 hi).2, hbi⟩), rfl⟩
        · obtain ⟨x, hx, rfl⟩ := mem_image.1 (hL hcL)
          obtain ⟨i, hi, h⟩ := exists_phi_of_mem (ends := ends) hx
          refine Or.inl ⟨ends x, mem_image_of_mem _ hx, xl i, mem_union_right _
            (mem_Llab_xl.2 ⟨by unfold clen; omega, ?_⟩), h.symm⟩
          simp only [hb, selBit, hi, if_true, decide_eq_true_eq]
          rw [xl, h]; exact hcL

end MultMain

section SmallRef

variable {V E : Type} [DecidableEq V] [DecidableEq E] {ends : E → Finset V} {X : Finset E}
  {M : ℕ}

theorem mY_subset_mR : mY ends X M ⊆ (mR ends X M).image Sum.inr := by
  intro c hc
  obtain ⟨e, he, hc⟩ := mem_biUnion.1 hc
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hc
  exact mem_mR_image.2 ⟨e, he, xl i, mem_union_right _ (mem_image_of_mem _ hi), rfl⟩

theorem card_mY_le : (mY ends X M).card ≤ (X.image ends).card * M := by
  refine card_biUnion_le.trans ?_
  calc ∑ e ∈ X.image ends, ((resIdx ends X M e).image fun i => phi ends X e (xl i)).card
      ≤ ∑ _e ∈ X.image ends, M := sum_le_sum fun e _ => card_image_le.trans (by
        simp [resIdx, clen])
    _ = (X.image ends).card * M := by simp

theorem mR_ends {y : MLab V} (hy : y ∈ mR ends X M) : y.1 ∈ X.image ends := by
  obtain ⟨e, he, hy⟩ := mem_biUnion.1 hy
  obtain ⟨a, -, rfl⟩ := mem_image.1 hy
  exact he

end SmallRef

/-- **Refiners for multigraphs with few distinct edges.**  Every `r`-multigraph with at most `k`
distinct edges has a `C`-refined multi-refiner, with empty residue, made of new parallel copies
of its own edges; `C` depends only on `q`, `r` and `k`. -/
theorem smallRefiner (q r k : ℕ) (hrq : r ≤ q) : ∃ C : ℕ, ∀ {V E : Type} [DecidableEq V]
    [DecidableEq E] (ends : E → Finset V) (X : Finset E), MIsRGraph r ends X →
    (X.image ends).card ≤ k →
    ∃ (N : Type) (_ : DecidableEq N) (endsN : N → Finset V) (R : Finset N)
      (𝒲 : Finset (Finset (E ⊕ N))), (∀ y ∈ R, endsN y ∈ X.image ends) ∧
      IsMultiRefiner q r C (Sum.elim ends endsN) (X.image Sum.inl) (R.image Sum.inr) 𝒲 := by
  set M := RefinedAbsorption.MultiRefiner.fakeModulus q r with hMdef
  have hM : 1 ≤ M := fakeModulus_pos hrq
  have hdvd : ∀ s < r, (q - s).choose (r - s) ∣ M := fun s hs => dvd_fakeModulus hs
  refine ⟨5 * M + 1 + (k * M + 2 ^ (k * M)), ?_⟩
  intro V E _ _ ends X hX hk
  classical
  have h₁ := multReduction (q := q) (ends := ends) (X := X) hM hdvd hX
  have hYsub := mY_subset_mR (ends := ends) (X := X) (M := M)
  have hYr : MIsRGraph r (mEnds ends) (mY ends X M) :=
    fun c hc => h₁.rgraph c (mem_union_right _ (hYsub hc))
  have hYcard : (mY ends X M).card ≤ k * M :=
    card_mY_le.trans (Nat.mul_le_mul_right _ hk)
  have h₂ := finiteStep (q := q) hYr hYcard
  have h := h₁.trans h₂ (hYsub.trans subset_union_right) (disjoint_empty_left _)
  rw [union_empty] at h
  exact ⟨MLab V, inferInstance, Prod.fst, mR ends X M, _, fun y hy => mR_ends hy, h⟩

end RefinedAbsorption.FlatDown
