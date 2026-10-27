module
public import Mathlib

/-!
# Boxes: the basic class-preserving moves for `r`-sets

Let `e` be a finite set, `F ⊆ e` a set of *fixed* vertices and `ρ` a *replacement* map that is
injective on `e \ F` and sends `e \ F` outside `e`.  For `F ⊆ J ⊆ e` the *transversal*
`bt e ρ J = J ∪ ρ (e \ J)` keeps the vertices of `J` and replaces the others; it carries the sign
`(-1)^{|e \ J|}`.  The signed sum of all transversals is the (lower) *box* `Σ_J ± [bt e ρ J]`.

* `box_sum_eq_zero_of_free`: the box has class `0` at every set `S` that misses some coordinate,
  i.e. some `x ∈ e \ F` with `x ∉ S` and `ρ x ∉ S`.
* `box_free_of_card_lt`: for the full box (`F = ∅`) every `S` with `|S| < |e|` misses a coordinate,
  so the full box has class `0` at every face.
* `box_cover_card`: for the lower box, a set `S` at which the class is not `0` has the size of a
  set `S'` with `e \ F ⊆ S' ⊆ e`.

These are the `r`-uniform versions of the odd walks of the grid refiner (for `r = 2` the full box
on `{u, w}` is the walk `u, ρ w, ρ u, w`).
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset

variable {V : Type*} [DecidableEq V]

/-- The transversal of the box on `e` keeping exactly the vertices of `J`. -/
def bt (e : Finset V) (ρ : V → V) (J : Finset V) : Finset V := J ∪ (e \ J).image ρ

/-- The transversals of the box (with fixed set `F`), indexed by the kept sets. -/
def bJs (e F : Finset V) : Finset (Finset V) := e.powerset.filter (F ⊆ ·)

/-- Hypotheses on a box: `F ⊆ e`, `ρ` injective on `e \ F` and `ρ (e \ F)` disjoint from `e`. -/
structure BoxOK (e F : Finset V) (ρ : V → V) : Prop where
  sub : F ⊆ e
  inj : Set.InjOn ρ ↑(e \ F)
  out : ∀ x ∈ e \ F, ρ x ∉ e

variable {e F : Finset V} {ρ : V → V}

lemma mem_bt_of_free (h : BoxOK e F ρ) {J : Finset V} (hJ : J ∈ bJs e F) {x : V}
    (hx : x ∈ e \ F) : (x ∈ bt e ρ J ↔ x ∈ J) ∧ (ρ x ∈ bt e ρ J ↔ x ∉ J) := by
  have hJe : J ⊆ e := mem_powerset.1 (mem_filter.1 hJ).1
  have hFJ : F ⊆ J := (mem_filter.1 hJ).2
  have hxe : x ∈ e := (mem_sdiff.1 hx).1
  constructor
  · simp only [bt, mem_union, mem_image, mem_sdiff]
    constructor
    · rintro (h1 | ⟨y, ⟨hy, hyJ⟩, hyx⟩)
      · exact h1
      · exfalso
        have hyF : y ∈ e \ F := mem_sdiff.2 ⟨hy, fun hyF => hyJ (hFJ hyF)⟩
        exact h.out y hyF (hyx ▸ hxe)
    · exact Or.inl
  · simp only [bt, mem_union, mem_image, mem_sdiff]
    constructor
    · rintro (h1 | ⟨y, ⟨hy, hyJ⟩, hyx⟩) hxJ
      · exact h.out x hx (hJe h1)
      · have hyF : y ∈ e \ F := mem_sdiff.2 ⟨hy, fun hyF => hyJ (hFJ hyF)⟩
        have : y = x := h.inj (by simpa using hyF) (by simpa using hx) hyx
        subst this; exact hyJ hxJ
    · intro hxJ; exact Or.inr ⟨x, ⟨hxe, hxJ⟩, rfl⟩

/-- Away from the coordinate `x`, flipping `x` does not change the transversal. -/
lemma mem_bt_flip (h : BoxOK e F ρ) {J : Finset V} (hJ : J ∈ bJs e F) {x : V} (hx : x ∈ e \ F)
    {y : V} (hyx : y ≠ x) (hyρ : y ≠ ρ x) :
    y ∈ bt e ρ J ↔ y ∈ bt e ρ (symmDiff J {x}) := by
  have hFJ : F ⊆ J := (mem_filter.1 hJ).2
  simp only [bt, mem_union, mem_image, mem_sdiff, mem_symmDiff, mem_singleton]
  constructor
  · rintro (h1 | ⟨z, ⟨hz, hzJ⟩, rfl⟩)
    · exact Or.inl (Or.inl ⟨h1, hyx⟩)
    · have hzx : z ≠ x := fun hzx => hyρ (by rw [hzx])
      exact Or.inr ⟨z, ⟨hz, fun h' => by
        rcases h' with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hzJ h1
        · exact hzx h1⟩, rfl⟩
  · rintro ((⟨h1, -⟩ | ⟨h1, h2⟩) | ⟨z, ⟨hz, hzJ⟩, rfl⟩)
    · exact Or.inl h1
    · exact absurd h1 hyx
    · have hzx : z ≠ x := fun hzx => hyρ (by rw [hzx])
      refine Or.inr ⟨z, ⟨hz, fun hzJ' => hzJ (Or.inl ⟨hzJ', hzx⟩)⟩, rfl⟩

/-- **A box has class `0` at a set missing one of its free coordinates.** -/
theorem box_sum_eq_zero_of_free {R : Type*} [CommRing R] (h : BoxOK e F ρ) (S : Finset V)
    {x : V} (hx : x ∈ e \ F) (hxS : x ∉ S) (hρS : ρ x ∉ S) :
    ∑ J ∈ bJs e F, (if S ⊆ bt e ρ J then (-1 : R) ^ (e \ J).card else 0) = 0 := by
  have hxe : x ∈ e := (mem_sdiff.1 hx).1
  have hxF : x ∉ F := (mem_sdiff.1 hx).2
  refine sum_involution (fun J _ => symmDiff J {x}) ?_ ?_ ?_ ?_
  · intro J hJ
    have hJ' : symmDiff J {x} ∈ bJs e F := by
      have hJe : J ⊆ e := mem_powerset.1 (mem_filter.1 hJ).1
      have hFJ : F ⊆ J := (mem_filter.1 hJ).2
      refine mem_filter.2 ⟨mem_powerset.2 ?_, ?_⟩
      · intro y hy
        rcases mem_symmDiff.1 hy with ⟨hy1, -⟩ | ⟨hy1, -⟩
        · exact hJe hy1
        · rw [mem_singleton.1 hy1]; exact hxe
      · intro y hy
        refine mem_symmDiff.2 (Or.inl ⟨hFJ hy, ?_⟩)
        rw [mem_singleton]; rintro rfl; exact hxF hy
    have hiff : S ⊆ bt e ρ J ↔ S ⊆ bt e ρ (symmDiff J {x}) := by
      constructor
      · intro hS y hy
        exact (mem_bt_flip h hJ hx (fun h' => hxS (h' ▸ hy)) (fun h' => hρS (h' ▸ hy))).1 (hS hy)
      · intro hS y hy
        exact (mem_bt_flip h hJ hx (fun h' => hxS (h' ▸ hy)) (fun h' => hρS (h' ▸ hy))).2 (hS hy)
    dsimp only
    by_cases hS : S ⊆ bt e ρ J
    · rw [if_pos hS, if_pos (hiff.1 hS)]
      have hcard : (e \ symmDiff J {x}).card + 1 = (e \ J).card ∨
          (e \ J).card + 1 = (e \ symmDiff J {x}).card := by
        by_cases hxJ : x ∈ J
        · right
          have : e \ symmDiff J {x} = insert x (e \ J) := by
            ext y
            simp only [mem_sdiff, mem_symmDiff, mem_singleton, mem_insert]
            constructor
            · rintro ⟨hy, hn⟩
              by_cases hyx : y = x
              · exact Or.inl hyx
              · exact Or.inr ⟨hy, fun hyJ => hn (Or.inl ⟨hyJ, hyx⟩)⟩
            · rintro (rfl | ⟨hy, hyJ⟩)
              · exact ⟨hxe, by rintro (⟨-, h'⟩ | ⟨-, h'⟩) <;> simp_all⟩
              · refine ⟨hy, ?_⟩
                rintro (⟨h1, -⟩ | ⟨rfl, h2⟩)
                · exact hyJ h1
                · exact h2 hxJ
          rw [this, card_insert_of_notMem (by simp [hxJ])]
        · left
          have : e \ J = insert x (e \ symmDiff J {x}) := by
            ext y
            simp only [mem_sdiff, mem_symmDiff, mem_singleton, mem_insert]
            constructor
            · rintro ⟨hy, hyJ⟩
              by_cases hyx : y = x
              · exact Or.inl hyx
              · exact Or.inr ⟨hy, by rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> simp_all⟩
            · rintro (rfl | ⟨hy, hn⟩)
              · exact ⟨hxe, hxJ⟩
              · refine ⟨hy, fun hyJ => hn (Or.inl ⟨hyJ, ?_⟩)⟩
                rintro rfl; exact hxJ hyJ
          rw [this, card_insert_of_notMem (by simp [mem_symmDiff, hxJ])]
      rcases hcard with h1 | h1
      · rw [← h1, pow_succ]; ring
      · rw [← h1, pow_succ]; ring
    · rw [if_neg hS, if_neg (fun h' => hS (hiff.2 h'))]; simp
  · intro J hJ hne
    intro heq
    dsimp only at heq
    have : x ∈ J ↔ x ∈ symmDiff J {x} := by rw [heq]
    simp [mem_symmDiff] at this
  · intro J hJ
    have hJe : J ⊆ e := mem_powerset.1 (mem_filter.1 hJ).1
    have hFJ : F ⊆ J := (mem_filter.1 hJ).2
    refine mem_filter.2 ⟨mem_powerset.2 ?_, ?_⟩
    · intro y hy
      rcases mem_symmDiff.1 hy with ⟨hy1, -⟩ | ⟨hy1, -⟩
      · exact hJe hy1
      · rw [mem_singleton.1 hy1]; exact hxe
    · intro y hy
      refine mem_symmDiff.2 (Or.inl ⟨hFJ hy, ?_⟩)
      rw [mem_singleton]; rintro rfl; exact hxF hy
  · intro J _
    exact symmDiff_symmDiff_cancel_right {x} J

/-- If `S` meets every coordinate pair `{x, ρ x}` (`x ∈ e \ F`), then `|e \ F| ≤ |S|`. -/
lemma card_le_of_cover (h : BoxOK e F ρ) {S : Finset V}
    (hc : ∀ x ∈ e \ F, x ∈ S ∨ ρ x ∈ S) : (e \ F).card ≤ S.card := by
  classical
  let g : V → V := fun x => if x ∈ S then x else ρ x
  refine card_le_card_of_injOn g (fun x hx => ?_) ?_
  · simp only [g]; split_ifs with h1
    · exact h1
    · exact (hc x hx).resolve_left h1
  · intro x hx y hy hxy
    simp only [g] at hxy
    have hxe := (mem_sdiff.1 (mem_coe.1 hx)).1
    have hye := (mem_sdiff.1 (mem_coe.1 hy)).1
    split_ifs at hxy with h1 h2 h2
    · exact hxy
    · exact absurd (hxy ▸ hxe) (h.out y (mem_coe.1 hy))
    · exact absurd (hxy.symm ▸ hye) (h.out x (mem_coe.1 hx))
    · exact h.inj hx hy hxy

/-- **The full box has class `0` at every face.** -/
theorem box_free_of_card_lt (h : BoxOK e ∅ ρ) {S : Finset V} (hS : S.card < e.card) :
    ∃ x ∈ e \ ∅, x ∉ S ∧ ρ x ∉ S := by
  by_contra hcon
  push_neg at hcon
  have hc : ∀ x ∈ e \ ∅, x ∈ S ∨ ρ x ∈ S := by
    intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inl hxS
    · exact Or.inr (hcon x hx hxS)
  have := card_le_of_cover h hc
  rw [sdiff_empty] at this
  omega

/-- The full box sum vanishes at every face. -/
theorem box_sum_eq_zero {R : Type*} [CommRing R] (h : BoxOK e ∅ ρ) {S : Finset V}
    (hS : S.card < e.card) :
    ∑ J ∈ bJs e ∅, (if S ⊆ bt e ρ J then (-1 : R) ^ (e \ J).card else 0) = 0 := by
  obtain ⟨x, hx, hxS, hρS⟩ := box_free_of_card_lt h hS
  exact box_sum_eq_zero_of_free h S hx hxS hρS

/-- **Lower boxes.**  A set at which the lower box has nonzero class has the size of a set `S'`
with `e \ F ⊆ S' ⊆ e`; moreover `S` is not contained in `e` only if it contains a replaced
vertex. -/
theorem box_cover_card {R : Type*} [CommRing R] (h : BoxOK e F ρ) {S : Finset V}
    (hne : ∑ J ∈ bJs e F, (if S ⊆ bt e ρ J then (-1 : R) ^ (e \ J).card else 0) ≠ 0) :
    ∃ S', e \ F ⊆ S' ∧ S' ⊆ e ∧ S'.card = S.card := by
  have hc : ∀ x ∈ e \ F, x ∈ S ∨ ρ x ∈ S := by
    intro x hx
    by_contra hcon
    push_neg at hcon
    exact hne (box_sum_eq_zero_of_free h S hx hcon.1 hcon.2)
  -- some transversal contains `S`
  obtain ⟨J, hJ, hSJ⟩ : ∃ J ∈ bJs e F, S ⊆ bt e ρ J := by
    by_contra hcon
    push_neg at hcon
    exact hne (sum_eq_zero fun J hJ => by rw [if_neg (hcon J hJ)])
  have hJe : J ⊆ e := mem_powerset.1 (mem_filter.1 hJ).1
  have hFJ : F ⊆ J := (mem_filter.1 hJ).2
  -- `S ⊆ J ∪ ρ (e \ J)`; set `S' = (e \ F) ∪ (S ∩ F)`
  refine ⟨(e \ F) ∪ (S ∩ F), subset_union_left, union_subset sdiff_subset
    (inter_subset_right.trans h.sub), ?_⟩
  -- the map `y ↦ y` on `S ∩ (J ∪ …)` identifies the pieces
  have hdisj : Disjoint (e \ F) (S ∩ F) := by
    rw [disjoint_left]; intro y hy hy'; exact (mem_sdiff.1 hy).2 (mem_inter.1 hy').2
  rw [card_union_of_disjoint hdisj]
  -- `S = (S ∩ F) ∪ (S \ F)` and `|S \ F| = |e \ F|`
  have hsplit : S.card = (S ∩ F).card + (S \ F).card := by
    rw [card_inter_add_card_sdiff]
  -- every element of `S \ F` is `x` or `ρ x` for a unique `x ∈ e \ F`
  have hmem : ∀ y ∈ S \ F, ∃ x ∈ e \ F, y = x ∨ y = ρ x := by
    intro y hy
    have hy' := hSJ (mem_sdiff.1 hy).1
    simp only [bt, mem_union, mem_image, mem_sdiff] at hy'
    rcases hy' with hyJ | ⟨x, ⟨hx, hxJ⟩, rfl⟩
    · exact ⟨y, mem_sdiff.2 ⟨hJe hyJ, (mem_sdiff.1 hy).2⟩, Or.inl rfl⟩
    · exact ⟨x, mem_sdiff.2 ⟨hx, fun hxF => hxJ (hFJ hxF)⟩, Or.inr rfl⟩
  -- not both `x` and `ρ x` lie in `S` (no transversal contains both)
  have hnb : ∀ x ∈ e \ F, ¬ (x ∈ S ∧ ρ x ∈ S) := by
    rintro x hx ⟨h1, h2⟩
    have := mem_bt_of_free h hJ hx
    exact (this.2.1 (hSJ h2)) (this.1.1 (hSJ h1))
  classical
  let g : V → V := fun x => if x ∈ S then x else ρ x
  have hg : (e \ F).image g = S \ F := by
    ext y
    simp only [mem_image, g]
    constructor
    · rintro ⟨x, hx, rfl⟩
      split_ifs with h1
      · exact mem_sdiff.2 ⟨h1, (mem_sdiff.1 hx).2⟩
      · refine mem_sdiff.2 ⟨(hc x hx).resolve_left h1, fun hF => ?_⟩
        exact h.out x hx (h.sub hF)
    · intro hy
      obtain ⟨x, hx, hyx | hyx⟩ := hmem y hy
      · subst hyx; exact ⟨y, hx, by rw [if_pos (mem_sdiff.1 hy).1]⟩
      · subst hyx
        refine ⟨x, hx, ?_⟩
        rw [if_neg]
        intro hxS; exact hnb x hx ⟨hxS, (mem_sdiff.1 hy).1⟩
  have hinj : Set.InjOn g ↑(e \ F) := by
    intro x hx y hy hxy
    simp only [g] at hxy
    have hxe := (mem_sdiff.1 (mem_coe.1 hx)).1
    have hye := (mem_sdiff.1 (mem_coe.1 hy)).1
    split_ifs at hxy with h1 h2 h2
    · exact hxy
    · exact absurd (hxy ▸ hxe) (h.out y (mem_coe.1 hy))
    · exact absurd (hxy.symm ▸ hye) (h.out x (mem_coe.1 hx))
    · exact h.inj hx hy hxy
  rw [hsplit, ← hg, card_image_of_injOn hinj]
  ring

/-- Transversals have the size of `e`. -/
lemma card_bt (h : BoxOK e F ρ) {J : Finset V} (hJ : J ∈ bJs e F) : (bt e ρ J).card = e.card := by
  have hJe : J ⊆ e := mem_powerset.1 (mem_filter.1 hJ).1
  have hFJ : F ⊆ J := (mem_filter.1 hJ).2
  have hsub : e \ J ⊆ e \ F := sdiff_subset_sdiff subset_rfl hFJ
  rw [bt, card_union_of_disjoint, card_image_of_injOn (h.inj.mono (by exact_mod_cast hsub)),
    ← card_union_of_disjoint disjoint_sdiff, union_sdiff_of_subset hJe]
  rw [disjoint_left]
  intro y hyJ hy
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
  exact h.out x (hsub hx) (hJe hyJ)

/-- The transversal keeping everything is `e`. -/
lemma bt_self (ρ : V → V) : bt e ρ e = e := by simp [bt]

lemma self_mem_bJs (h : BoxOK e F ρ) : e ∈ bJs e F :=
  mem_filter.2 ⟨mem_powerset_self _, h.sub⟩

/-- Vertices of transversals. -/
lemma bt_subset (h : BoxOK e F ρ) {J : Finset V} (hJ : J ∈ bJs e F) :
    bt e ρ J ⊆ e ∪ (e \ F).image ρ := by
  have hJe : J ⊆ e := mem_powerset.1 (mem_filter.1 hJ).1
  have hFJ : F ⊆ J := (mem_filter.1 hJ).2
  exact union_subset_union hJe (image_subset_image (sdiff_subset_sdiff subset_rfl hFJ))

end RefinedAbsorption.HyperPlan
