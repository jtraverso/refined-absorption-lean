module
public import RequestProject.OddGrid.Basic

/-!
# Accumulator chains

An accumulator chain absorbs an arbitrary subset of its items and leaves a single carry whose
value is the total weight of the present items.  Items `item 1, …, item t` have weights
`w 1, …, w t ∈ ZMod K`; the carries are `cp k s` (weight `s`) and `cn k s` (weight `-s`).

The pieces are
* `chT k s true = {cp (k-1) s, item k, cn k (s + w k)}` and `chT k s false = {cp (k-1) s, cn k s}`
  (the transitions, with `s = 0` when `k = 1`);
* `chQ k s = {cn k s, cp k s}`.

For a set of present items, with prefix sums `psum w pres k`, the pieces `chT k (σ (k-1)) (k present)` and
`chQ k s` (`s ≠ psum w pres k`) partition the carries and the present items, except the residue
`cp t (psum w pres t)` (`chain_decomp`).
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset

section Chain

variable {Λ : Type} [DecidableEq Λ] {K : ℕ} [NeZero K]

/-- Prefix sums of the present weights. -/
def psum (w : ℕ → ZMod K) (pres : ℕ → Prop) [DecidablePred pres] (k : ℕ) : ZMod K :=
  ∑ j ∈ range k, if pres (j + 1) then w (j + 1) else 0

lemma psum_zero (w : ℕ → ZMod K) (pres : ℕ → Prop) [DecidablePred pres] : psum w pres 0 = 0 := by
  simp [psum]

lemma psum_succ (w : ℕ → ZMod K) (pres : ℕ → Prop) [DecidablePred pres] (k : ℕ) :
    psum w pres (k + 1) = psum w pres k + if pres (k + 1) then w (k + 1) else 0 := by
  simp [psum, sum_range_succ]

variable (cp cn : ℕ → ZMod K → Λ) (item : ℕ → Λ) (w : ℕ → ZMod K)

/-- Transition pieces. -/
def chT (k : ℕ) (s : ZMod K) (b : Bool) : Finset Λ :=
  if b then {cp (k - 1) s, item k, cn k (s + w k)} else {cp (k - 1) s, cn k s}

/-- Pairing pieces. -/
def chQ (k : ℕ) (s : ZMod K) : Finset Λ := {cn k s, cp k s}

/-- The labels of a chain of length `t`. -/
def chR (t : ℕ) : Finset Λ :=
  {cp 0 0} ∪ ((Icc 1 t) ×ˢ (univ : Finset (ZMod K))).image (fun p => cp p.1 p.2) ∪
    ((Icc 1 t) ×ˢ (univ : Finset (ZMod K))).image (fun p => cn p.1 p.2)

/-- The pieces of a chain of length `t`. -/
def chW (t : ℕ) : Finset (Finset Λ) :=
  (((Icc 1 t) ×ˢ (univ : Finset (ZMod K))).filter (fun p => p.1 = 1 → p.2 = 0)).biUnion
      (fun p => {chT cp cn item w p.1 p.2 true, chT cp cn item w p.1 p.2 false}) ∪
    ((Icc 1 t) ×ˢ (univ : Finset (ZMod K))).image (fun p => chQ cp cn p.1 p.2)

/-- The pieces used for a set of present items. -/
def chU (t : ℕ) (pres : ℕ → Prop) [DecidablePred pres] : Finset (Finset Λ) :=
  (Icc 1 t).image (fun k => chT cp cn item w k (psum w pres (k - 1)) (decide (pres k))) ∪
    (((Icc 1 t) ×ˢ (univ : Finset (ZMod K))).filter (fun p => p.2 ≠ psum w pres p.1)).image
      (fun p => chQ cp cn p.1 p.2)

variable {cp cn item w}

/-- The transition piece used at step `k`. -/
lemma chT_used (pres : ℕ → Prop) [DecidablePred pres] {k : ℕ} (hk : 1 ≤ k) :
    chT cp cn item w k (psum w pres (k - 1)) (decide (pres k)) =
      if pres k then {cp (k - 1) (psum w pres (k - 1)), item k, cn k (psum w pres k)}
      else {cp (k - 1) (psum w pres (k - 1)), cn k (psum w pres k)} := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [chT, Nat.add_sub_cancel, psum_succ]
  by_cases h : pres (j + 1) <;> simp [h]

lemma mem_chT_used (pres : ℕ → Prop) [DecidablePred pres] {k : ℕ} (hk : 1 ≤ k) (x : Λ) :
    x ∈ chT cp cn item w k (psum w pres (k - 1)) (decide (pres k)) ↔
      x = cp (k - 1) (psum w pres (k - 1)) ∨ (pres k ∧ x = item k) ∨
        x = cn k (psum w pres k) := by
  rw [chT_used pres hk]
  split_ifs with h <;> simp [h]

/-- **Accumulator chain decomposition.** -/
theorem chain_decomp (t : ℕ) (pres : ℕ → Prop) [DecidablePred pres]
    (hcp : ∀ k s k' s', cp k s = cp k' s' ↔ k = k' ∧ s = s')
    (hcn : ∀ k s k' s', cn k s = cn k' s' ↔ k = k' ∧ s = s')
    (hpn : ∀ k s k' s', cp k s ≠ cn k' s')
    (hit : ∀ k ∈ Icc 1 t, ∀ k' ∈ Icc 1 t, item k = item k' → k = k')
    (hic : ∀ k ∈ Icc 1 t, ∀ k' s, item k ≠ cp k' s)
    (hin : ∀ k ∈ Icc 1 t, ∀ k' s, item k ≠ cn k' s) :
    chU cp cn item w t pres ⊆ chW cp cn item w t ∧
      ((chU cp cn item w t pres : Set (Finset Λ))).PairwiseDisjoint id ∧
      Disjoint ((chU cp cn item w t pres).sup id) {cp t (psum w pres t)} ∧
      (chU cp cn item w t pres).sup id ∪ {cp t (psum w pres t)} =
        chR cp cn t ∪ ((Icc 1 t).filter pres).image item := by
  have hσ0 : psum w pres 0 = 0 := psum_zero w pres
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the used pieces belong to the family
    intro P hP
    rcases mem_union.1 hP with hP | hP
    · obtain ⟨k, hk, rfl⟩ := mem_image.1 hP
      have hk' := mem_Icc.1 hk
      refine mem_union_left _ (mem_biUnion.2 ⟨(k, psum w pres (k - 1)), mem_filter.2 ⟨?_, ?_⟩, ?_⟩)
      · simp [hk'.1, hk'.2]
      · intro h1; simp only at h1; rw [h1]; exact hσ0
      · cases decide (pres k) <;> simp
    · obtain ⟨p, hp, rfl⟩ := mem_image.1 hP
      exact mem_union_right _ (mem_image.2 ⟨p, (mem_filter.1 hp).1, rfl⟩)
  · -- pairwise disjointness
    intro P hP P' hP' hne
    rw [chU] at hP hP'
    simp only [coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe, mem_filter,
      mem_product, mem_univ, and_true] at hP hP'
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro x hx hx'
    rcases hP with ⟨k, hk, rfl⟩ | ⟨⟨k, s⟩, ⟨hk, hs⟩, rfl⟩ <;>
      rcases hP' with ⟨k', hk', rfl⟩ | ⟨⟨k', s'⟩, ⟨hk', hs'⟩, rfl⟩
    · have h1 := (mem_Icc.1 hk).1
      have h1' := (mem_Icc.1 hk').1
      rw [mem_chT_used pres h1] at hx
      rw [mem_chT_used pres h1'] at hx'
      apply hne
      have : k = k' := by
        rcases hx with rfl | ⟨-, rfl⟩ | rfl <;> rcases hx' with h | ⟨-, h⟩ | h <;>
          first
          | (simp only [hcp, hcn] at h; omega)
          | exact absurd h (hpn _ _ _ _)
          | exact absurd h.symm (hpn _ _ _ _)
          | exact hit _ hk _ hk' h
          | exact absurd h (hic _ hk _ _)
          | exact absurd h.symm (hic _ hk' _ _)
          | exact absurd h (hin _ hk _ _)
          | exact absurd h.symm (hin _ hk' _ _)
      rw [this]
    · have h1 := (mem_Icc.1 hk).1
      rw [mem_chT_used pres h1] at hx
      simp only [chQ, mem_insert, mem_singleton] at hx' hs'
      rcases hx with rfl | ⟨-, rfl⟩ | rfl <;> rcases hx' with h | h
      · exact hpn _ _ _ _ h
      · rw [hcp] at h; obtain ⟨rfl, rfl⟩ := h; exact hs' rfl
      · exact hin _ hk _ _ h
      · exact hic _ hk _ _ h
      · rw [hcn] at h; obtain ⟨rfl, rfl⟩ := h; exact hs' rfl
      · exact hpn _ _ _ _ h.symm
    · have h1' := (mem_Icc.1 hk').1
      rw [mem_chT_used pres h1'] at hx'
      simp only [chQ, mem_insert, mem_singleton] at hx hs
      rcases hx' with rfl | ⟨-, rfl⟩ | rfl <;> rcases hx with h | h
      · exact hpn _ _ _ _ h
      · rw [hcp] at h; obtain ⟨rfl, rfl⟩ := h; exact hs rfl
      · exact hin _ hk' _ _ h
      · exact hic _ hk' _ _ h
      · rw [hcn] at h; obtain ⟨rfl, rfl⟩ := h; exact hs rfl
      · exact hpn _ _ _ _ h.symm
    · simp only [chQ, mem_insert, mem_singleton] at hx hx'
      apply hne
      rcases hx with rfl | rfl <;> rcases hx' with h | h
      · rw [hcn] at h; rw [h.1, h.2]
      · exact absurd h.symm (hpn _ _ _ _)
      · exact absurd h (hpn _ _ _ _)
      · rw [hcp] at h; rw [h.1, h.2]
  · -- the residue is not in a used piece
    rw [Finset.disjoint_sup_left]
    intro P hP
    rw [Finset.disjoint_singleton_right, id]
    intro hx
    rcases mem_union.1 hP with hP | hP
    · obtain ⟨k, hk, rfl⟩ := mem_image.1 hP
      have hk' := mem_Icc.1 hk
      rw [mem_chT_used pres hk'.1] at hx
      rcases hx with h | ⟨-, h⟩ | h
      · rw [hcp] at h; omega
      · exact hic _ hk _ _ h.symm
      · exact hpn _ _ _ _ h
    · obtain ⟨⟨k, s⟩, hp, rfl⟩ := mem_image.1 hP
      simp only [mem_filter, mem_product, mem_univ, and_true] at hp
      simp only [chQ, mem_insert, mem_singleton] at hx
      rcases hx with h | h
      · exact hpn _ _ _ _ h
      · rw [hcp] at h; obtain ⟨rfl, rfl⟩ := h; exact hp.2 rfl
  · -- the union
    ext x
    simp only [mem_union, mem_sup, id, mem_singleton, chR, mem_image, mem_product, mem_univ,
      and_true, mem_filter]
    constructor
    · rintro (⟨P, hP, hx⟩ | rfl)
      · rcases mem_union.1 hP with hP | hP
        · obtain ⟨k, hk, rfl⟩ := mem_image.1 hP
          have hk' := mem_Icc.1 hk
          rw [mem_chT_used pres hk'.1] at hx
          rcases hx with rfl | ⟨hp, rfl⟩ | rfl
          · by_cases h1 : k = 1
            · subst h1; left; left; left; simp [hσ0]
            · left; left; right
              exact ⟨(k - 1, psum w pres (k - 1)), mem_Icc.2 ⟨by omega, by omega⟩, rfl⟩
          · right; exact ⟨k, ⟨hk, hp⟩, rfl⟩
          · left; right; exact ⟨(k, psum w pres k), hk, rfl⟩
        · obtain ⟨⟨k, s⟩, hp, rfl⟩ := mem_image.1 hP
          simp only [mem_filter, mem_product, mem_univ, and_true] at hp
          simp only [chQ, mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · left; right; exact ⟨(k, s), hp.1, rfl⟩
          · left; left; right; exact ⟨(k, s), hp.1, rfl⟩
      · rcases Nat.eq_zero_or_pos t with h0 | h0
        · subst h0; left; left; left; simp [hσ0]
        · left; left; right; exact ⟨(t, psum w pres t), mem_Icc.2 ⟨h0, le_rfl⟩, rfl⟩
    · rintro (((rfl | ⟨⟨k, s⟩, hk, rfl⟩) | ⟨⟨k, s⟩, hk, rfl⟩) | ⟨k, ⟨hk, hp⟩, rfl⟩)
      · rcases Nat.eq_zero_or_pos t with h0 | h0
        · subst h0; right; rw [hσ0]
        · left
          refine ⟨_, mem_union_left _ (mem_image_of_mem _ (mem_Icc.2 ⟨le_rfl, h0⟩)), ?_⟩
          rw [mem_chT_used pres le_rfl]; left; simp [hσ0]
      · have hk' := mem_Icc.1 hk
        by_cases hs : s = psum w pres k
        · subst hs
          rcases lt_or_eq_of_le hk'.2 with hlt | heq
          · left
            refine ⟨_, mem_union_left _ (mem_image_of_mem _
              (mem_Icc.2 ⟨by omega, hlt⟩ : k + 1 ∈ Icc 1 t)), ?_⟩
            rw [mem_chT_used pres (by omega)]; left; simp
          · right; simp only at heq ⊢; rw [heq]
        · left
          refine ⟨_, mem_union_right _ (mem_image.2 ⟨(k, s), mem_filter.2
            ⟨mem_product.2 ⟨hk, mem_univ _⟩, hs⟩, rfl⟩), ?_⟩
          simp [chQ]
      · have hk' := mem_Icc.1 hk
        by_cases hs : s = psum w pres k
        · subst hs; left
          refine ⟨_, mem_union_left _ (mem_image_of_mem _ hk), ?_⟩
          rw [mem_chT_used pres hk'.1]; right; right; rfl
        · left
          refine ⟨_, mem_union_right _ (mem_image.2 ⟨(k, s), mem_filter.2
            ⟨mem_product.2 ⟨hk, mem_univ _⟩, hs⟩, rfl⟩), ?_⟩
          simp [chQ]
      · left
        refine ⟨_, mem_union_left _ (mem_image_of_mem _ hk), ?_⟩
        rw [mem_chT_used pres (mem_Icc.1 hk).1]; right; left; exact ⟨hp, rfl⟩

end Chain

end RefinedAbsorption.OddGrid
