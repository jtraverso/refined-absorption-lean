module
public import RefinedAbsorption.MultiRefiner.Basic

/-!
# Fake edges

To remove a duplicate copy `i` of an `r`-set `e = ends i`, we replace it by a *fake edge*: a
simple `r`-graph on `e` plus new vertices tagged by `i`, which behaves like the single edge `e`
with respect to `K_q^r`-divisibility.  We use `m = N - 1` anti-edges on `e`, where
`N = ∏_{s<r} binom(q-s, r-s)`: the `j`-th anti-edge is the clique on `e ∪ T_{i,j}` minus `e`,
with `T_{i,j}` a set of `q - r` new vertices.  For every `S` with `|S| < r`,
`deg(fake edge, S) ≡ m·(−[S ⊆ e]) ≡ [S ⊆ e]` modulo `binom(q-|S|, r-|S|)`, since this binomial
divides `N = m + 1` (`fakeEdge_deg_cast`).  Every edge of the fake edge contains a new vertex
tagged by `i` (`fakeEdge_exists_fresh`, `fakeEdge_fresh_tag`).
-/

@[expose] public section

namespace RefinedAbsorption.MultiRefiner

open Finset

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- `N(q, r) = ∏_{s < r} binom(q-s, r-s)`; every `binom(q-|S|, r-|S|)` with `|S| < r` divides it. -/
def fakeModulus (q r : ℕ) : ℕ := ∏ s ∈ range r, (q - s).choose (r - s)

/-- The number `m = N - 1` of anti-edges in a fake edge. -/
def fakeCount (q r : ℕ) : ℕ := fakeModulus q r - 1

/-- The extended vertex type: old vertices, and new vertices `(i, j, t)` (label `i`, anti-edge
`j`, position `t`). -/
abbrev XV (V E : Type*) (q r : ℕ) := V ⊕ (E × Fin (fakeCount q r) × Fin (q - r))

/-- The copy `i` as a simple edge on the old vertices. -/
def lift (q r : ℕ) (ends : E → Finset V) (i : E) : Finset (XV V E q r) :=
  (ends i).map Function.Embedding.inl

/-- The new vertices of the `j`-th anti-edge of the fake edge of `i`. -/
def freshT (q r : ℕ) (i : E) (j : Fin (fakeCount q r)) : Finset (XV V E q r) :=
  univ.image fun t => Sum.inr (i, j, t)

/-- The `j`-th clique `e ∪ T_{i,j}`. -/
def fakeClique (q r : ℕ) (ends : E → Finset V) (i : E) (j : Fin (fakeCount q r)) :
    Finset (XV V E q r) :=
  lift q r ends i ∪ freshT q r i j

/-- The `j`-th anti-edge: the clique on `e ∪ T_{i,j}` minus `e`. -/
def antiPiece (q r : ℕ) (ends : E → Finset V) (i : E) (j : Fin (fakeCount q r)) :
    Finset (Finset (XV V E q r)) :=
  cliqueEdges r (fakeClique q r ends i j) \ {lift q r ends i}

/-- The fake edge of the copy `i`. -/
def fakeEdge (q r : ℕ) (ends : E → Finset V) (i : E) : Finset (Finset (XV V E q r)) :=
  univ.biUnion (antiPiece q r ends i)

theorem fakeModulus_pos {q r : ℕ} (hrq : r ≤ q) : 0 < fakeModulus q r :=
  prod_pos fun s _ => Nat.choose_pos (by omega)

theorem dvd_fakeModulus {q r s : ℕ} (hs : s < r) : (q - s).choose (r - s) ∣ fakeModulus q r :=
  dvd_prod_of_mem _ (mem_range.2 hs)

theorem card_freshT (q r : ℕ) (i : E) (j : Fin (fakeCount q r)) :
    (freshT (V := V) q r i j).card = q - r := by
  rw [freshT, card_image_of_injective _ (fun a b h => by simpa using h), card_univ,
    Fintype.card_fin]

omit [DecidableEq V] [DecidableEq E] in
theorem card_lift (q r : ℕ) (ends : E → Finset V) (i : E) :
    (lift q r ends i).card = (ends i).card := card_map _

theorem disjoint_lift_freshT (q r : ℕ) (ends : E → Finset V) (i i' : E)
    (j : Fin (fakeCount q r)) : Disjoint (lift q r ends i) (freshT q r i' j) := by
  rw [disjoint_left]
  intro x hx hx'
  obtain ⟨v, -, rfl⟩ := mem_map.1 hx
  obtain ⟨t, -, ht⟩ := mem_image.1 hx'
  simp at ht

theorem card_fakeClique {q r : ℕ} (hrq : r ≤ q) {ends : E → Finset V} {i : E}
    (hi : (ends i).card = r) (j : Fin (fakeCount q r)) : (fakeClique q r ends i j).card = q := by
  rw [fakeClique, card_union_of_disjoint (disjoint_lift_freshT q r ends i i j), card_lift,
    card_freshT, hi]
  omega

theorem lift_mem_cliqueEdges {q r : ℕ} {ends : E → Finset V} {i : E}
    (hi : (ends i).card = r) (j : Fin (fakeCount q r)) :
    lift q r ends i ∈ cliqueEdges r (fakeClique q r ends i j) :=
  mem_powersetCard.2 ⟨subset_union_left, by rw [card_lift, hi]⟩

/-- Every edge of the `j`-th anti-edge contains a new vertex `(i, j, t)`. -/
theorem antiPiece_exists_fresh {q r : ℕ} {ends : E → Finset V} {i : E}
    (hi : (ends i).card = r) {j : Fin (fakeCount q r)} {f : Finset (XV V E q r)}
    (hf : f ∈ antiPiece q r ends i j) : ∃ t, (Sum.inr (i, j, t) : XV V E q r) ∈ f := by
  rw [antiPiece, mem_sdiff, mem_singleton, cliqueEdges, mem_powersetCard] at hf
  obtain ⟨⟨hsub, hcard⟩, hne⟩ := hf
  by_contra hno
  push_neg at hno
  apply hne
  have : f ⊆ lift q r ends i := by
    intro x hx
    rcases mem_union.1 (hsub hx) with h | h
    · exact h
    · obtain ⟨t, -, rfl⟩ := mem_image.1 h
      exact absurd hx (hno t)
  exact eq_of_subset_of_card_le this (by rw [card_lift, hi, hcard])

/-- The new vertices of an edge of the `j`-th anti-edge are tagged `(i, j)`. -/
theorem antiPiece_fresh_tag {q r : ℕ} {ends : E → Finset V} {i : E} {j : Fin (fakeCount q r)}
    {f : Finset (XV V E q r)} (hf : f ∈ antiPiece q r ends i j) {i' : E}
    {j' : Fin (fakeCount q r)} {t : Fin (q - r)} (hx : (Sum.inr (i', j', t) : XV V E q r) ∈ f) :
    i' = i ∧ j' = j := by
  rw [antiPiece, mem_sdiff, cliqueEdges, mem_powersetCard] at hf
  rcases mem_union.1 (hf.1.1 hx) with h | h
  · obtain ⟨v, -, hv⟩ := mem_map.1 h
    simp at hv
  · obtain ⟨t', -, ht'⟩ := mem_image.1 h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at ht'
    exact ⟨ht'.1.symm, ht'.2.1.symm⟩

theorem antiPiece_pairwiseDisjoint {q r : ℕ} {ends : E → Finset V} {i : E}
    (hi : (ends i).card = r) :
    ((univ : Finset (Fin (fakeCount q r))) : Set (Fin (fakeCount q r))).PairwiseDisjoint
      (antiPiece q r ends i) := by
  intro j _ j' _ hne
  rw [Function.onFun, disjoint_left]
  intro f hf hf'
  obtain ⟨t, ht⟩ := antiPiece_exists_fresh hi hf
  exact hne (antiPiece_fresh_tag hf' ht).2

theorem fakeEdge_exists_fresh {q r : ℕ} {ends : E → Finset V} {i : E}
    (hi : (ends i).card = r) {f : Finset (XV V E q r)} (hf : f ∈ fakeEdge q r ends i) :
    ∃ j t, (Sum.inr (i, j, t) : XV V E q r) ∈ f := by
  obtain ⟨j, -, hj⟩ := mem_biUnion.1 hf
  exact ⟨j, antiPiece_exists_fresh hi hj⟩

theorem fakeEdge_fresh_tag {q r : ℕ} {ends : E → Finset V} {i : E}
    {f : Finset (XV V E q r)} (hf : f ∈ fakeEdge q r ends i) {i' : E}
    {j' : Fin (fakeCount q r)} {t : Fin (q - r)} (hx : (Sum.inr (i', j', t) : XV V E q r) ∈ f) :
    i' = i := by
  obtain ⟨j, -, hj⟩ := mem_biUnion.1 hf
  exact (antiPiece_fresh_tag hj hx).1

/-- The old vertices of an edge of the fake edge of `i` lie in `ends i`. -/
theorem fakeEdge_inl {q r : ℕ} {ends : E → Finset V} {i : E}
    {f : Finset (XV V E q r)} (hf : f ∈ fakeEdge q r ends i) {v : V}
    (hv : (Sum.inl v : XV V E q r) ∈ f) : v ∈ ends i := by
  obtain ⟨j, -, hj⟩ := mem_biUnion.1 hf
  rw [antiPiece, mem_sdiff, cliqueEdges, mem_powersetCard] at hj
  rcases mem_union.1 (hj.1.1 hv) with h | h
  · obtain ⟨w, hw, hwv⟩ := mem_map.1 h
    simp only [Function.Embedding.inl_apply, Sum.inl.injEq] at hwv
    exact hwv ▸ hw
  · obtain ⟨t, -, ht⟩ := mem_image.1 h
    simp at ht

theorem fakeEdge_card_edge {q r : ℕ} {ends : E → Finset V} {i : E}
    {f : Finset (XV V E q r)} (hf : f ∈ fakeEdge q r ends i) : f.card = r := by
  obtain ⟨j, -, hj⟩ := mem_biUnion.1 hf
  exact (mem_powersetCard.1 (mem_sdiff.1 hj).1).2

theorem card_fakeEdge_le {q r : ℕ} (hrq : r ≤ q) {ends : E → Finset V} {i : E}
    (hi : (ends i).card = r) : (fakeEdge q r ends i).card ≤ fakeCount q r * q.choose r := by
  refine card_biUnion_le.trans ?_
  calc ∑ j : Fin (fakeCount q r), (antiPiece q r ends i j).card
      ≤ ∑ _j : Fin (fakeCount q r), q.choose r := by
        refine sum_le_sum fun j _ => ?_
        refine (card_le_card sdiff_subset).trans ?_
        rw [cliqueEdges, card_powersetCard, card_fakeClique hrq hi]
    _ = fakeCount q r * q.choose r := by simp

/-- Degree of `S` in the `j`-th anti-edge plus `[S ⊆ e]` is the degree of `S` in the clique. -/
theorem deg_antiPiece_add {q r : ℕ} {ends : E → Finset V} {i : E}
    (hi : (ends i).card = r) (j : Fin (fakeCount q r)) (S : Finset (XV V E q r)) :
    deg (antiPiece q r ends i j) S + (if S ⊆ lift q r ends i then 1 else 0) =
      deg (cliqueEdges r (fakeClique q r ends i j)) S := by
  have hmem := lift_mem_cliqueEdges (q := q) hi j
  have hf : (antiPiece q r ends i j).filter (fun e => S ⊆ e) =
      (cliqueEdges r (fakeClique q r ends i j)).filter (fun e => S ⊆ e) \ {lift q r ends i} := by
    ext f; simp only [antiPiece, mem_filter, mem_sdiff, mem_singleton]; tauto
  rw [deg, deg, hf]
  split_ifs with h
  · rw [card_sdiff_of_subset (singleton_subset_iff.2 (mem_filter.2 ⟨hmem, h⟩)), card_singleton]
    have : 0 < (filter (fun e => S ⊆ e) (cliqueEdges r (fakeClique q r ends i j))).card :=
      card_pos.2 ⟨_, mem_filter.2 ⟨hmem, h⟩⟩
    exact Nat.sub_add_cancel this
  · rw [add_zero, sdiff_singleton_eq_erase, erase_eq_of_notMem (fun h' => h (mem_filter.1 h').2)]

/-- The degree of `S` in a `q`-clique is divisible by `binom(q - |S|, r - |S|)`. -/
theorem choose_dvd_deg_cliqueEdges {q r : ℕ} {Q S : Finset (XV V E q r)} (hQ : Q.card = q)
    (hS : S.card ≤ r) : (q - S.card).choose (r - S.card) ∣ deg (cliqueEdges r Q) S := by
  by_cases h : S ⊆ Q
  · rw [deg, cliqueEdges, card_powersetCard_filter_superset h hS, hQ]
  · rw [deg, cliqueEdges, card_powersetCard_filter_superset_of_not h]
    exact dvd_zero _

/-- **The fake edge behaves like the edge `e` modulo divisibility.**  For `|S| < r`, in
`ZMod (binom(q-|S|, r-|S|))` the degree of `S` in the fake edge of `i` equals `[S ⊆ e]`. -/
theorem fakeEdge_deg_cast {q r : ℕ} (hrq : r ≤ q) {ends : E → Finset V} {i : E}
    (hi : (ends i).card = r) {S : Finset (XV V E q r)} (hS : S.card < r) :
    ((deg (fakeEdge q r ends i) S : ℕ) : ZMod ((q - S.card).choose (r - S.card))) =
      if S ⊆ lift q r ends i then 1 else 0 := by
  set b := (q - S.card).choose (r - S.card)
  have hdeg : deg (fakeEdge q r ends i) S = ∑ j, deg (antiPiece q r ends i j) S := by
    rw [deg, fakeEdge, filter_biUnion, card_biUnion]
    · rfl
    · intro j _ j' _ hne
      exact disjoint_filter_filter (antiPiece_pairwiseDisjoint hi (mem_coe.2 (mem_univ j))
        (mem_coe.2 (mem_univ j')) hne)
  have hpiece : ∀ j, ((deg (antiPiece q r ends i j) S : ℕ) : ZMod b) =
      -(if S ⊆ lift q r ends i then 1 else 0) := by
    intro j
    have h1 := congrArg (fun n : ℕ => (n : ZMod b)) (deg_antiPiece_add (q := q) hi j S)
    have h2 : ((deg (cliqueEdges r (fakeClique q r ends i j)) S : ℕ) : ZMod b) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2
        (choose_dvd_deg_cliqueEdges (card_fakeClique hrq hi j) hS.le)
    simp only [Nat.cast_add, h2] at h1
    split_ifs at h1 ⊢ <;> push_cast at h1 ⊢ <;> linear_combination h1
  have hN : ((fakeCount q r : ℕ) : ZMod b) + 1 = 0 := by
    have : fakeCount q r + 1 = fakeModulus q r := by
      have := fakeModulus_pos hrq; unfold fakeCount; omega
    rw [← Nat.cast_one, ← Nat.cast_add, this]
    exact (ZMod.natCast_eq_zero_iff _ _).2 (dvd_fakeModulus hS)
  rw [hdeg, Nat.cast_sum, sum_congr rfl (fun j _ => hpiece j), sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  split_ifs
  · linear_combination (-1 : ZMod b) * hN
  · simp

end RefinedAbsorption.MultiRefiner
