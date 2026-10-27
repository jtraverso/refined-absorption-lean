module
public import RequestProject.GeneralEmbedding.Counting

/-!
# The state of the greedy embedding

After the supergraphs `W_H`, `H ∈ 𝒮`, have been embedded by `φ`, we record the *new pairs*
`(H, e)` with `H ∈ 𝒮` and `e ∈ W_H` an edge containing a new vertex, and for a vertex set `A`:

* `totDeg`: the number of new pairs whose image contains `A`;
* `strDeg`: the number of new pairs whose old part contains `A` (*structural* contributions,
  controlled by the edge-intersecting and refinedness hypotheses);
* `accDeg`: the number of new pairs whose image contains `A` although their old part does not
  (*accidental* contributions, controlled by the greedy choices).
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {n : ℕ} {ι : Type*} [DecidableEq ι] {m : Finset ι → ℕ}

/-- The new pairs `(H, e)`, `H ∈ 𝒮`, `e ∈ W_H` containing a new vertex. -/
def newPairs (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))
    (𝒮 : Finset (Finset ι)) : Finset (Σ H : Finset ι, Finset (Fin n ⊕ Fin (m H))) :=
  (𝒮.sigma W).filter (fun p => p.2.toRight.Nonempty)

/-- The image of a pair under `φ`. -/
def pimg (φ : (H : Finset ι) → Fin (m H) → Fin n)
    (p : Σ H : Finset ι, Finset (Fin n ⊕ Fin (m H))) : Finset (Fin n) :=
  embedEdge (φ p.1) p.2

section

variable (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))

def totDeg (𝒮 : Finset (Finset ι)) (φ : (H : Finset ι) → Fin (m H) → Fin n)
    (A : Finset (Fin n)) : ℕ :=
  ((newPairs W 𝒮).filter (fun p => A ⊆ pimg φ p)).card

def strDeg (𝒮 : Finset (Finset ι)) (A : Finset (Fin n)) : ℕ :=
  ((newPairs W 𝒮).filter (fun p => A ⊆ p.2.toLeft)).card

def accDeg (𝒮 : Finset (Finset ι)) (φ : (H : Finset ι) → Fin (m H) → Fin n)
    (A : Finset (Fin n)) : ℕ :=
  ((newPairs W 𝒮).filter (fun p => A ⊆ pimg φ p ∧ ¬ A ⊆ p.2.toLeft)).card

theorem totDeg_le (𝒮 : Finset (Finset ι)) (φ : (H : Finset ι) → Fin (m H) → Fin n)
    (A : Finset (Fin n)) : totDeg W 𝒮 φ A ≤ strDeg W 𝒮 A + accDeg W 𝒮 φ A := by
  unfold totDeg strDeg accDeg
  refine le_trans (card_le_card ?_) (card_union_le _ _)
  intro p hp
  obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
  by_cases h : A ⊆ p.2.toLeft
  · exact mem_union_left _ (mem_filter.2 ⟨hp1, h⟩)
  · exact mem_union_right _ (mem_filter.2 ⟨hp1, hp2, h⟩)

omit [DecidableEq ι] in
theorem accDeg_empty (𝒮 : Finset (Finset ι)) (φ : (H : Finset ι) → Fin (m H) → Fin n) :
    accDeg W 𝒮 φ ∅ = 0 := by
  unfold accDeg
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p _ h
  exact h.2 (empty_subset _)

/-- Structural contributions are bounded by the refinedness of `ℋ`. -/
theorem strDeg_le [Fintype ι] {C : ℕ} {ends : ι → Finset (Fin n)} {ℋ 𝒮 : Finset (Finset ι)}
    (h𝒮 : 𝒮 ⊆ ℋ) (href : IsCRefinedFamily C ℋ) (hint : IsEdgeIntersecting ends ℋ m W)
    (hbd : ∀ H ∈ ℋ, (W H).card ≤ C) (A : Finset (Fin n)) :
    strDeg W 𝒮 A ≤ C * C * (univ.filter (fun x => A ⊆ ends x)).card := by
  classical
  unfold strDeg
  have hsub : (newPairs W 𝒮).filter (fun p => A ⊆ p.2.toLeft) ⊆
      (univ.filter (fun x => A ⊆ ends x)).biUnion
        (fun x => (ℋ.filter (fun H => x ∈ H)).sigma W) := by
    intro p hp
    obtain ⟨hp1, hA⟩ := mem_filter.1 hp
    obtain ⟨hp1', _⟩ := mem_filter.1 hp1
    obtain ⟨hH, he⟩ := mem_sigma.1 hp1'
    obtain ⟨x, hx, hex⟩ := hint p.1 (h𝒮 hH) p.2 he
    refine mem_biUnion.2 ⟨x, mem_filter.2 ⟨mem_univ _, hA.trans hex⟩, ?_⟩
    exact mem_sigma.2 ⟨mem_filter.2 ⟨h𝒮 hH, hx⟩, he⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ x ∈ univ.filter (fun x => A ⊆ ends x), ((ℋ.filter (fun H => x ∈ H)).sigma W).card
      ≤ ∑ x ∈ univ.filter (fun x => A ⊆ ends x), C * C := by
        refine sum_le_sum fun x _ => ?_
        rw [card_sigma]
        calc ∑ H ∈ ℋ.filter (fun H => x ∈ H), (W H).card
            ≤ ∑ H ∈ ℋ.filter (fun H => x ∈ H), C :=
              sum_le_sum fun H hH => hbd H (mem_filter.1 hH).1
          _ = (ℋ.filter (fun H => x ∈ H)).card * C := by rw [sum_const, smul_eq_mul]
          _ ≤ C * C := Nat.mul_le_mul_right _ (href x)
    _ = C * C * (univ.filter (fun x => A ⊆ ends x)).card := by
        rw [sum_const, smul_eq_mul, mul_comm]

theorem card_embedEdge_le {m' : ℕ} (f : Fin m' → Fin n) (e : Finset (Fin n ⊕ Fin m')) :
    (embedEdge f e).card ≤ e.card := card_image_le

theorem mem_embedEdge {m' : ℕ} {f : Fin m' → Fin n} {e : Finset (Fin n ⊕ Fin m')} {x : Fin n} :
    x ∈ embedEdge f e ↔ x ∈ e.toLeft ∨ ∃ i ∈ e.toRight, f i = x := by
  unfold embedEdge
  simp only [mem_image, mem_toLeft, mem_toRight]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases y with y | i
    · exact Or.inl hy
    · exact Or.inr ⟨i, hy, rfl⟩
  · rintro (h | ⟨i, hi, rfl⟩)
    · exact ⟨Sum.inl x, h, rfl⟩
    · exact ⟨Sum.inr i, hi, rfl⟩

theorem toLeft_subset_embedEdge {m' : ℕ} (f : Fin m' → Fin n) (e : Finset (Fin n ⊕ Fin m')) :
    e.toLeft ⊆ embedEdge f e := fun _ hx => mem_embedEdge.2 (Or.inl hx)

/-- Quantities of `𝒮` do not change when `φ` is modified outside `𝒮`. -/
theorem pimg_update {𝒮 : Finset (Finset ι)} {H : Finset ι} (hH : H ∉ 𝒮)
    (φ : (H : Finset ι) → Fin (m H) → Fin n) (f : Fin (m H) → Fin n)
    {p : Σ H : Finset ι, Finset (Fin n ⊕ Fin (m H))} (hp : p ∈ newPairs W 𝒮) :
    pimg (Function.update φ H f) p = pimg φ p := by
  have hp1 : p.1 ∈ 𝒮 := (mem_sigma.1 (mem_filter.1 hp).1).1
  have hne : p.1 ≠ H := fun h => hH (h ▸ hp1)
  unfold pimg
  rw [Function.update_of_ne hne]

theorem accDeg_update {𝒮 : Finset (Finset ι)} {H : Finset ι} (hH : H ∉ 𝒮)
    (φ : (H : Finset ι) → Fin (m H) → Fin n) (f : Fin (m H) → Fin n) (A : Finset (Fin n)) :
    accDeg W 𝒮 (Function.update φ H f) A = accDeg W 𝒮 φ A := by
  unfold accDeg
  congr 1
  refine filter_congr fun p hp => ?_
  rw [pimg_update W hH φ f hp]

/-- The new pairs of `insert H 𝒮`. -/
theorem newPairs_insert_subset (𝒮 : Finset (Finset ι)) (H : Finset ι) :
    newPairs W (insert H 𝒮) ⊆ newPairs W 𝒮 ∪
      ((W H).filter (fun e => e.toRight.Nonempty)).map
        ⟨fun e => (⟨H, e⟩ : Σ H : Finset ι, Finset (Fin n ⊕ Fin (m H))),
          fun e₁ e₂ h => by simpa using h⟩ := by
  intro p hp
  obtain ⟨hp1, hnew⟩ := mem_filter.1 hp
  obtain ⟨hH, he⟩ := mem_sigma.1 hp1
  rcases mem_insert.1 hH with h | h
  · refine mem_union_right _ (mem_map.2 ⟨h ▸ p.2, ?_, ?_⟩)
    · obtain ⟨H', e⟩ := p
      simp only at h
      subst h
      exact mem_filter.2 ⟨he, hnew⟩
    · obtain ⟨H', e⟩ := p
      simp only at h
      subst h
      rfl
  · exact mem_union_left _ (mem_filter.2 ⟨mem_sigma.2 ⟨h, he⟩, hnew⟩)

/-- One step of the greedy embedding raises accidental degrees by the number of new edges of
`W_H` contributing to them. -/
theorem accDeg_insert_le {𝒮 : Finset (Finset ι)} {H : Finset ι} (hH : H ∉ 𝒮)
    (φ : (H : Finset ι) → Fin (m H) → Fin n) (f : Fin (m H) → Fin n) (A : Finset (Fin n)) :
    accDeg W (insert H 𝒮) (Function.update φ H f) A ≤ accDeg W 𝒮 φ A +
      ((W H).filter (fun e => e.toRight.Nonempty ∧ A ⊆ embedEdge f e ∧ ¬ A ⊆ e.toLeft)).card := by
  rw [← accDeg_update W hH φ f A]
  unfold accDeg
  set Y := ((W H).filter (fun e => e.toRight.Nonempty ∧ A ⊆ embedEdge f e ∧
      ¬ A ⊆ e.toLeft)).map ⟨fun e => (⟨H, e⟩ : Σ H : Finset ι, Finset (Fin n ⊕ Fin (m H))),
        fun e₁ e₂ h => by simpa using h⟩ with hY
  have hsub : (newPairs W (insert H 𝒮)).filter
      (fun p => A ⊆ pimg (Function.update φ H f) p ∧ ¬ A ⊆ p.2.toLeft) ⊆
      (newPairs W 𝒮).filter
        (fun p => A ⊆ pimg (Function.update φ H f) p ∧ ¬ A ⊆ p.2.toLeft) ∪ Y := by
    intro p hp
    obtain ⟨hp1, hA1, hA2⟩ := mem_filter.1 hp
    rcases mem_union.1 (newPairs_insert_subset W 𝒮 H hp1) with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨h, hA1, hA2⟩)
    · obtain ⟨e, he, rfl⟩ := mem_map.1 h
      obtain ⟨he1, he2⟩ := mem_filter.1 he
      refine mem_union_right _ (mem_map.2 ⟨e, mem_filter.2 ⟨he1, he2, ?_, hA2⟩, rfl⟩)
      unfold pimg at hA1
      change A ⊆ embedEdge (Function.update φ H f H) e at hA1
      simpa [Function.update_self] using hA1
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ = _ := by rw [hY, card_map]

end

end RefinedAbsorption
