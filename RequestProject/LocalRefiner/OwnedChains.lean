module
public import RequestProject.RefinerOne.Transfer

/-!
# Families of chain refiners with owners

Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

We run one copy of the label-level chain refiner of the case `r = 1` (`ChainRefiner`) for every
*owner* `o : O`, with `m o` inputs, and relabel the labels of owner `o` by `φ o : Lab → G`.  When
the relabellings are jointly injective on the used labels (`ChInj`), the chains do not interact:

* `chCover`: if every owner selects a number of inputs divisible by `q`, the chosen pieces
  cover exactly the relabelled reservoirs and the selected inputs;
* `chUnique`: every label lies in at most one chosen piece;
* `chFam_struct`: every piece has size `0` or `q` and lies in the labels of one owner;
* `chMult`: every label lies in at most `4q + 1` pieces.

This is used twice in `LocalRefiner`: once with one owner per vertex (degree conditions) and once
with a single owner (the global edge-count condition).
-/

@[expose] public section

namespace RefinedAbsorption.LocalRefiner

open Finset RefinedAbsorption.ChainRefiner

variable {O G : Type} [DecidableEq O] [Fintype O] [DecidableEq G]

section Defs

variable (q : ℕ) (m : O → ℕ) (φ : O → Lab → G)

/-- The relabellings are jointly injective on the used labels. -/
def ChInj : Prop :=
  ∀ o o' a a', a ∈ Ulab q (m o) → a' ∈ Ulab q (m o') → φ o a = φ o' a' → o = o' ∧ a = a'

/-- The pieces of owner `o`. -/
def chFamO (o : O) : Finset (Finset G) :=
  (Idx q (m o)).image (fun i => (piece q i.1 i.2.1 i.2.2).image (φ o)) ∪
    {(finPiece q (m o)).image (φ o)}

/-- All pieces. -/
def chFam : Finset (Finset G) := univ.biUnion (chFamO q m φ)

/-- The relabelled reservoirs. -/
def chR : Finset G := univ.biUnion fun o => (Rlab q (m o)).image (φ o)

/-- The relabelled inputs. -/
def chX : Finset G := univ.biUnion fun o => (Xlab (m o)).image (φ o)

/-- The relabelled selected inputs. -/
def chL (b : O → ℕ → Bool) : Finset G :=
  univ.biUnion fun o => (Llab (b o) (m o)).image (φ o)

/-- The chosen piece with index `α = (o, i)`: the `i`-th chosen piece of owner `o` for `i < m o`,
and the final piece of `o` for `i = m o`. -/
def chPc (b : O → ℕ → Bool) (α : O × ℕ) : Finset G :=
  if α.2 < m α.1 then (chosen q (b α.1) α.2).image (φ α.1)
  else (finPiece q (m α.1)).image (φ α.1)

/-- The indices of the chosen pieces. -/
def chInd : Finset (O × ℕ) := univ.biUnion fun o => (range (m o + 1)).image (o, ·)

end Defs

variable {q : ℕ} {m : O → ℕ} {φ : O → Lab → G}

lemma mem_chInd {α : O × ℕ} : α ∈ chInd m ↔ α.2 ≤ m α.1 := by
  obtain ⟨o, i⟩ := α
  simp only [chInd, mem_biUnion, mem_univ, true_and, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨o', j, hj, rfl, rfl⟩; exact Nat.lt_succ_iff.1 hj
  · intro h; exact ⟨o, i, Nat.lt_succ_of_le h, rfl, rfl⟩

lemma chosen_subset_U (hq : 1 ≤ q) {b : ℕ → Bool} {M i : ℕ} (hi : i < M) :
    chosen q b i ⊆ Ulab q M :=
  (piece_subset hq hi (tSeq_lt hq b i)).trans (Rlab_union_Xlab_subset hq)

omit [DecidableEq O] [Fintype O] in
lemma chPc_subset_U (hq : 1 ≤ q) (b : O → ℕ → Bool) (α : O × ℕ) :
    ∀ g ∈ chPc q m φ b α, ∃ a ∈ Ulab q (m α.1), φ α.1 a = g := by
  intro g hg
  unfold chPc at hg
  split_ifs at hg with h
  · obtain ⟨a, ha, rfl⟩ := mem_image.1 hg
    exact ⟨a, chosen_subset_U hq h ha, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := mem_image.1 hg
    exact ⟨a, finPiece_subset_U hq ha, rfl⟩

omit [DecidableEq O] [Fintype O] in
/-- The input labels in a chosen piece are selected. -/
lemma chPc_sel (hq : 1 ≤ q) (b : O → ℕ → Bool) (α : O × ℕ) :
    ∀ g ∈ chPc q m φ b α, ∃ a ∈ Ulab q (m α.1), φ α.1 a = g ∧
      ∀ i, a = xl i → b α.1 i = true := by
  intro g hg
  unfold chPc at hg
  split_ifs at hg with h
  · obtain ⟨a, ha, rfl⟩ := mem_image.1 hg
    refine ⟨a, chosen_subset_U hq h ha, rfl, fun i hi => ?_⟩
    subst hi
    obtain ⟨hb, rfl⟩ := (chosen_xl).1 ha
    exact hb
  · obtain ⟨a, ha, rfl⟩ := mem_image.1 hg
    refine ⟨a, finPiece_subset_U hq ha, rfl, fun i hi => ?_⟩
    subst hi
    exact absurd ha not_mem_finPiece_xl

lemma chPc_mem (hq : 1 ≤ q) (b : O → ℕ → Bool) {α : O × ℕ} (hα : α ∈ chInd m) :
    chPc q m φ b α ∈ chFam q m φ := by
  obtain ⟨o, i⟩ := α
  simp only [chFam, mem_biUnion, mem_univ, true_and]
  refine ⟨o, ?_⟩
  simp only [chPc, chFamO, mem_union, mem_image, mem_singleton]
  split_ifs with h
  · left
    exact ⟨(i, tSeq q (b o) i, b o i), by
      simp only [Idx, mem_product, mem_range, mem_univ, and_true]
      exact ⟨h, tSeq_lt hq _ _⟩, rfl⟩
  · right; rfl

/-- **Covering.** -/
theorem chCover (hq : 1 ≤ q) (b : O → ℕ → Bool) (hdiv : ∀ o, q ∣ cnt (b o) (m o)) (g : G) :
    (∃ α ∈ chInd m, g ∈ chPc q m φ b α) ↔ g ∈ chR q m φ ∪ chL m φ b := by
  simp only [mem_union, chR, chL, mem_biUnion, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨⟨o, i⟩, hα, hg⟩
    rw [mem_chInd] at hα
    simp only [chPc] at hg
    split_ifs at hg with h
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 hg
      have := (cover hq (b o) (m o) (hdiv o) a).1 (Or.inl ⟨i, h, ha⟩)
      rcases mem_union.1 this with h' | h'
      · exact Or.inl ⟨o, a, h', rfl⟩
      · exact Or.inr ⟨o, a, h', rfl⟩
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 hg
      have := (cover hq (b o) (m o) (hdiv o) a).1 (Or.inr ha)
      rcases mem_union.1 this with h' | h'
      · exact Or.inl ⟨o, a, h', rfl⟩
      · exact Or.inr ⟨o, a, h', rfl⟩
  · intro h
    obtain ⟨o, a, ha, rfl⟩ : ∃ o, ∃ a ∈ Rlab q (m o) ∪ Llab (b o) (m o), φ o a = g := by
      rcases h with ⟨o, a, ha, rfl⟩ | ⟨o, a, ha, rfl⟩
      · exact ⟨o, a, mem_union_left _ ha, rfl⟩
      · exact ⟨o, a, mem_union_right _ ha, rfl⟩
    rcases (cover hq (b o) (m o) (hdiv o) a).2 ha with ⟨i, hi, hai⟩ | hfin
    · refine ⟨(o, i), mem_chInd.2 (by simp; omega), ?_⟩
      simp only [chPc, if_pos hi]
      exact mem_image_of_mem _ hai
    · refine ⟨(o, m o), mem_chInd.2 le_rfl, ?_⟩
      simp only [chPc, lt_irrefl, if_false]
      exact mem_image_of_mem _ hfin

/-- **Uniqueness**: a label lies in at most one chosen piece. -/
theorem chUnique (hq : 1 ≤ q) (hinj : ChInj q m φ) (b : O → ℕ → Bool)
    (hdiv : ∀ o, q ∣ cnt (b o) (m o)) {α β : O × ℕ} (hα : α ∈ chInd m) (hβ : β ∈ chInd m)
    {g : G} (h1 : g ∈ chPc q m φ b α) (h2 : g ∈ chPc q m φ b β) : α = β := by
  obtain ⟨o, i⟩ := α
  obtain ⟨o', j⟩ := β
  rw [mem_chInd] at hα hβ
  simp only at hα hβ
  have hmem : ∀ (o : O) (i : ℕ), i ≤ m o → ∀ g ∈ chPc q m φ b (o, i),
      ∃ a, φ o a = g ∧ a ∈ Ulab q (m o) ∧
        ((i < m o ∧ a ∈ chosen q (b o) i) ∨ (i = m o ∧ a ∈ finPiece q (m o))) := by
    intro o i hi g hg
    simp only [chPc] at hg
    split_ifs at hg with h
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 hg
      exact ⟨a, rfl, chosen_subset_U hq h ha, Or.inl ⟨h, ha⟩⟩
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 hg
      exact ⟨a, rfl, finPiece_subset_U hq ha, Or.inr ⟨by omega, ha⟩⟩
  obtain ⟨a, rfl, haU, ha⟩ := hmem o i hα g h1
  obtain ⟨a', ha'e, ha'U, ha'⟩ := hmem o' j hβ _ h2
  obtain ⟨rfl, rfl⟩ := hinj o' o a' a ha'U haU ha'e
  rcases ha with ⟨hi, hai⟩ | ⟨rfl, haf⟩ <;> rcases ha' with ⟨hj, haj⟩ | ⟨hj, haf'⟩
  · rw [chosen_unique hai haj]
  · exact absurd haf' (chosen_not_fin hq (hdiv o') hi hai)
  · exact absurd haf (chosen_not_fin hq (hdiv o') hj haj)
  · rw [hj]

omit [DecidableEq O] in
/-- Every piece lies in the relabelled reservoir and inputs. -/
theorem chFam_subset (hq : 1 ≤ q) {W : Finset G} (hW : W ∈ chFam q m φ) :
    W ⊆ chR q m φ ∪ chX m φ := by
  simp only [chFam, chFamO, mem_biUnion, mem_univ, true_and, mem_union, mem_image,
    mem_singleton] at hW
  have key : ∀ (o : O) (P : Finset Lab), P ⊆ Rlab q (m o) ∪ Xlab (m o) →
      P.image (φ o) ⊆ chR q m φ ∪ chX m φ := by
    intro o P hP g hg
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hg
    simp only [mem_union, chR, chX, mem_biUnion, mem_univ, true_and, mem_image]
    rcases mem_union.1 (hP ha) with h | h
    · exact Or.inl ⟨o, a, h, rfl⟩
    · exact Or.inr ⟨o, a, h, rfl⟩
  obtain ⟨o, ⟨x, hx, rfl⟩ | rfl⟩ := hW
  · simp only [Idx, mem_product, mem_range, mem_univ, and_true] at hx
    exact key o _ (piece_subset hq hx.1 hx.2)
  · exact key o _ (finPiece_subset hq)

omit [DecidableEq O] in
/-- Every piece has size `0` or `q` and consists of labels of a single owner. -/
theorem chFam_struct (hq : 1 ≤ q) (hinj : ChInj q m φ) {W : Finset G}
    (hW : W ∈ chFam q m φ) :
    ∃ o, (W.card = 0 ∨ W.card = q) ∧ ∀ g ∈ W, ∃ a ∈ Ulab q (m o), φ o a = g := by
  simp only [chFam, chFamO, mem_biUnion, mem_univ, true_and, mem_union, mem_image,
    mem_singleton] at hW
  have hio : ∀ o, Set.InjOn (φ o) (Ulab q (m o)) := fun o a ha a' ha' h =>
    (hinj o o a a' ha ha' h).2
  have key : ∀ (o : O) (P : Finset Lab), P ⊆ Ulab q (m o) → (P.card = 0 ∨ P.card = q) →
      ((P.image (φ o)).card = 0 ∨ (P.image (φ o)).card = q) ∧
        ∀ g ∈ P.image (φ o), ∃ a ∈ Ulab q (m o), φ o a = g := by
    intro o P hP hc
    refine ⟨card_image_cases (hio o) hP hc, fun g hg => ?_⟩
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hg
    exact ⟨a, hP ha, rfl⟩
  obtain ⟨o, ⟨x, hx, rfl⟩ | rfl⟩ := hW
  · exact ⟨o, key o _ (piece_subset_U hq hx) (card_piece_cases hq hx)⟩
  · exact ⟨o, key o _ (finPiece_subset_U hq) (card_finPiece_cases hq)⟩

omit [DecidableEq O] in
/-- **Multiplicity**: every label lies in at most `4q + 1` pieces. -/
theorem chMult (hq : 1 ≤ q) (hinj : ChInj q m φ) (g : G) :
    ((chFam q m φ).filter (g ∈ ·)).card ≤ 4 * q + 1 := by
  by_cases hex : ∃ o, ∃ a ∈ Ulab q (m o), φ o a = g
  · obtain ⟨o, a, haU, rfl⟩ := hex
    have hsub : (chFam q m φ).filter (φ o a ∈ ·) ⊆
        ((Idx q (m o)).filter (fun x => a ∈ piece q x.1 x.2.1 x.2.2)).image
          (fun i => (piece q i.1 i.2.1 i.2.2).image (φ o)) ∪
          {(finPiece q (m o)).image (φ o)} := by
      intro W hW
      rw [mem_filter] at hW
      obtain ⟨hW, hgW⟩ := hW
      simp only [chFam, chFamO, mem_biUnion, mem_univ, true_and, mem_union, mem_image,
        mem_singleton] at hW
      obtain ⟨o', ⟨x, hx, rfl⟩ | rfl⟩ := hW
      · obtain ⟨a', ha', he⟩ := mem_image.1 hgW
        have hU := piece_subset_U hq hx ha'
        obtain ⟨rfl, rfl⟩ := hinj o' o a' a hU haU he
        exact mem_union_left _ (mem_image.2 ⟨x, mem_filter.2 ⟨hx, ha'⟩, rfl⟩)
      · obtain ⟨a', ha', he⟩ := mem_image.1 hgW
        have hU := finPiece_subset_U hq ha'
        obtain ⟨rfl, rfl⟩ := hinj o' o a' a hU haU he
        exact mem_union_right _ (mem_singleton_self _)
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ + _ := card_union_le _ _
      _ ≤ 4 * q + 1 := by
        rw [card_singleton]
        exact Nat.add_le_add_right (card_image_le.trans (card_filter_piece_le q (m o) a)) 1
  · push_neg at hex
    have : (chFam q m φ).filter (g ∈ ·) = ∅ := by
      rw [filter_eq_empty_iff]
      intro W hW hgW
      obtain ⟨o, -, hall⟩ := chFam_struct hq hinj hW
      obtain ⟨a, ha, he⟩ := hall g hgW
      exact hex o a ha he
    rw [this]; simp

omit [DecidableEq O] in
lemma chL_subset (b : O → ℕ → Bool) : chL m φ b ⊆ chX m φ := by
  intro g hg
  simp only [chL, chX, mem_biUnion, mem_univ, true_and, mem_image] at hg ⊢
  obtain ⟨o, a, ha, rfl⟩ := hg
  refine ⟨o, a, ?_, rfl⟩
  rcases lab_cases a with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
  · exact mem_Xlab_xl.2 (mem_Llab_xl.1 ha).1
  · exact absurd ha not_mem_Llab_zl

end RefinedAbsorption.LocalRefiner
