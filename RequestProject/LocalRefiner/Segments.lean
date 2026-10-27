module
public import RequestProject.MultiRefiner.Basic

/-!
# Labels made of bundles of parallel copies

Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

Each label `ℓ : Λ` stands for a small multigraph given by a list of *segments* `(p, k)`: `k`
parallel copies of the set `p`.  The copies of `ℓ` are the triples `(ℓ, s, c)` with `s` a segment
index and `c < k_s`; their ends are the set of the segment.  A finite set of labels `P` lifts to
the multigraph `liftS P`, and degrees of lifts are sums of the degrees of the labels
(`mdeg_liftS`).
-/

@[expose] public section

namespace RefinedAbsorption.LocalRefiner

open Finset RefinedAbsorption.MultiRefiner

variable {Λ V : Type} [DecidableEq Λ] [DecidableEq V]

section Defs

variable (sg : Λ → List (Finset V × ℕ))

/-- The `s`-th segment of the label `ℓ`. -/
def segAt (ℓ : Λ) (s : ℕ) : Finset V × ℕ := (sg ℓ).getD s (∅, 0)

/-- The ends of a copy. -/
def cpEnds (c : Λ × ℕ × ℕ) : Finset V := (segAt sg c.1 c.2.1).1

/-- The copies of a label. -/
def lift (ℓ : Λ) : Finset (Λ × ℕ × ℕ) :=
  (range (sg ℓ).length).biUnion fun s => (range (segAt sg ℓ s).2).image fun c => (ℓ, s, c)

/-- The copies of a set of labels. -/
def liftS (P : Finset Λ) : Finset (Λ × ℕ × ℕ) := P.biUnion (lift sg)

/-- The degree of a set `S` in the multigraph of a label. -/
def wdeg (ℓ : Λ) (S : Finset V) : ℕ :=
  ∑ s ∈ range (sg ℓ).length, if S ⊆ (segAt sg ℓ s).1 then (segAt sg ℓ s).2 else 0

end Defs

variable {sg : Λ → List (Finset V × ℕ)}

omit [DecidableEq V] in
lemma mem_lift {ℓ : Λ} {c : Λ × ℕ × ℕ} :
    c ∈ lift sg ℓ ↔ c.1 = ℓ ∧ c.2.1 < (sg ℓ).length ∧ c.2.2 < (segAt sg ℓ c.2.1).2 := by
  obtain ⟨a, s, t⟩ := c
  simp only [lift, mem_biUnion, mem_range, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨s', hs', t', ht', rfl, rfl, rfl⟩; exact ⟨rfl, hs', ht'⟩
  · rintro ⟨rfl, hs, ht⟩; exact ⟨s, hs, t, ht, rfl, rfl, rfl⟩

omit [DecidableEq V] in
lemma mem_liftS {P : Finset Λ} {c : Λ × ℕ × ℕ} :
    c ∈ liftS sg P ↔ c.1 ∈ P ∧ c.2.1 < (sg c.1).length ∧ c.2.2 < (segAt sg c.1 c.2.1).2 := by
  simp only [liftS, mem_biUnion, mem_lift]
  constructor
  · rintro ⟨ℓ, hℓ, rfl, h1, h2⟩; exact ⟨hℓ, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩; exact ⟨c.1, h0, rfl, h1, h2⟩

omit [DecidableEq V] in
lemma liftS_union (P Q : Finset Λ) : liftS sg (P ∪ Q) = liftS sg P ∪ liftS sg Q :=
  union_biUnion

omit [DecidableEq V] in
lemma liftS_mono {P Q : Finset Λ} (h : P ⊆ Q) : liftS sg P ⊆ liftS sg Q :=
  biUnion_subset_biUnion_of_subset_left _ h

omit [DecidableEq V] in
lemma liftS_empty : liftS sg (∅ : Finset Λ) = ∅ := biUnion_empty

omit [DecidableEq V] in
lemma disjoint_liftS {P Q : Finset Λ} (h : Disjoint P Q) : Disjoint (liftS sg P) (liftS sg Q) := by
  rw [Finset.disjoint_left]
  intro c hP hQ
  exact Finset.disjoint_left.1 h (mem_liftS.1 hP).1 (mem_liftS.1 hQ).1

omit [DecidableEq V] in
lemma liftS_sup (𝒰 : Finset (Finset Λ)) :
    (𝒰.image (liftS sg)).sup id = liftS sg (𝒰.sup id) := by
  ext c
  simp only [mem_sup, mem_image, id, mem_liftS]
  constructor
  · rintro ⟨W, ⟨P, hP, rfl⟩, hc⟩
    rw [mem_liftS] at hc
    exact ⟨⟨P, hP, hc.1⟩, hc.2⟩
  · rintro ⟨⟨P, hP, h0⟩, h1, h2⟩
    exact ⟨liftS sg P, ⟨P, hP, rfl⟩, mem_liftS.2 ⟨h0, h1, h2⟩⟩

lemma mdeg_lift (ℓ : Λ) (S : Finset V) : mdeg (cpEnds sg) (lift sg ℓ) S = wdeg sg ℓ S := by
  unfold mdeg lift wdeg
  rw [filter_biUnion, card_biUnion]
  · apply sum_congr rfl
    intro s _
    rw [filter_image]
    split_ifs with h
    · rw [filter_true_of_mem (fun c _ => by simpa [cpEnds] using h)]
      rw [card_image_of_injective _ (fun a b hab => by simpa using hab), card_range]
    · rw [filter_false_of_mem (fun c _ => by simpa [cpEnds] using h)]
      simp
  · intro s _ s' _ hss'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c h1 h2
    simp only [mem_filter, mem_image] at h1 h2
    obtain ⟨⟨t, -, rfl⟩, -⟩ := h1
    obtain ⟨⟨t', -, he⟩, -⟩ := h2
    simp only [Prod.mk.injEq] at he
    exact hss' he.2.1.symm

lemma mdeg_liftS (P : Finset Λ) (S : Finset V) :
    mdeg (cpEnds sg) (liftS sg P) S = ∑ ℓ ∈ P, wdeg sg ℓ S := by
  unfold liftS
  rw [mdeg, filter_biUnion, card_biUnion]
  · exact sum_congr rfl fun ℓ _ => mdeg_lift ℓ S
  · intro ℓ _ ℓ' _ h
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c h1 h2
    rw [mem_filter, mem_lift] at h1 h2
    exact h (h1.1.1.symm.trans h2.1.1)

lemma card_liftS (P : Finset Λ) : (liftS sg P).card = ∑ ℓ ∈ P, wdeg sg ℓ ∅ := by
  rw [← mdeg_liftS]; simp [mdeg]

omit [DecidableEq V] in
lemma cpEnds_mem_of_mem_liftS {P : Finset Λ} {c : Λ × ℕ × ℕ} (hc : c ∈ liftS sg P) :
    (segAt sg c.1 c.2.1) ∈ sg c.1 := by
  rw [mem_liftS] at hc
  simp only [segAt]
  rw [List.getD_eq_getElem _ _ hc.2.1]
  exact List.getElem_mem _

/-! ### Labels touching a vertex -/

section Touch

variable (sg) in
/-- The label `ℓ` has a copy containing `x`. -/
def touch (x : V) (ℓ : Λ) : Bool := (sg ℓ).any fun p => decide (x ∈ p.1)

omit [DecidableEq Λ] in
lemma touch_iff {x : V} {ℓ : Λ} : touch sg x ℓ = true ↔ ∃ p ∈ sg ℓ, x ∈ p.1 := by
  simp [touch]

omit [DecidableEq Λ] [DecidableEq V] in
lemma segAt_mem {ℓ : Λ} {s : ℕ} (hs : s < (sg ℓ).length) : segAt sg ℓ s ∈ sg ℓ := by
  simp only [segAt]
  rw [List.getD_eq_getElem _ _ hs]
  exact List.getElem_mem _

omit [DecidableEq Λ] in
lemma wdeg_eq_zero_of_not_touch {x : V} {ℓ : Λ} (h : touch sg x ℓ = false) :
    wdeg sg ℓ {x} = 0 := by
  unfold wdeg
  apply sum_eq_zero
  intro s hs
  rw [if_neg]
  rw [singleton_subset_iff]
  intro hx
  have : touch sg x ℓ = true := touch_iff.2 ⟨_, segAt_mem (mem_range.1 hs), hx⟩
  rw [h] at this; exact Bool.false_ne_true this

omit [DecidableEq Λ] in
lemma wdeg_le_empty (ℓ : Λ) (S : Finset V) : wdeg sg ℓ S ≤ wdeg sg ℓ ∅ := by
  unfold wdeg
  apply sum_le_sum
  intro s _
  simp only [empty_subset, if_true]
  split_ifs <;> omega

lemma touch_of_mem_liftS {P : Finset Λ} {c : Λ × ℕ × ℕ} (hc : c ∈ liftS sg P) {x : V}
    (hx : x ∈ cpEnds sg c) : touch sg x c.1 = true :=
  touch_iff.2 ⟨_, cpEnds_mem_of_mem_liftS hc, hx⟩

/-- The degree of a vertex in a lift is at most the maximal size times the number of labels
touching it. -/
lemma mdeg_liftS_le (P : Finset Λ) (x : V) (smax : ℕ) (hs : ∀ ℓ ∈ P, wdeg sg ℓ ∅ ≤ smax) :
    mdeg (cpEnds sg) (liftS sg P) {x} ≤ smax * (P.filter (touch sg x ·)).card := by
  rw [mdeg_liftS, ← sum_filter_add_sum_filter_not P (touch sg x · = true)]
  have h0 : ∑ ℓ ∈ P.filter (fun ℓ => ¬ touch sg x ℓ = true), wdeg sg ℓ {x} = 0 := by
    apply sum_eq_zero
    intro ℓ hℓ
    rw [mem_filter, Bool.not_eq_true] at hℓ
    exact wdeg_eq_zero_of_not_touch hℓ.2
  rw [h0, add_zero, mul_comm, ← smul_eq_mul]
  apply sum_le_card_nsmul
  intro ℓ hℓ
  exact (wdeg_le_empty ℓ _).trans (hs ℓ (mem_filter.1 hℓ).1)

end Touch

end RefinedAbsorption.LocalRefiner
