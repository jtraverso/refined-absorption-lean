module
public import RefinedAbsorption.LinkSpread.Chain

/-!
# Composition of tagged outputs

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

The residues of a `TaggedOutE` (one residue `Y T` per tag `T`) form again a tagged multigraph
`pairSet Ts Y`, whose copies are the pairs `(T, c)` with `c ∈ Y T`, with tag `T` and body
`ends' T c`.  A second construction applied to it composes with the first one, fibre by fibre.

* `fibre_pairSet`, `mdeg_lift_pairSet`: fibres and lifted degrees of `pairSet`.
* **`TaggedOutE.comp`**: composition of tagged outputs (compare `PlacedOutE.comp`).
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown

section Pair

variable {n : ℕ} {E' : Type} [DecidableEq E']

/-- Tag of a pair `(T, c)` (truncated to `∅` when `T` meets the reserve `Zo`). -/
def pairTg (Zo : Finset (Fin n)) : Finset (Fin n) × E' → Finset (Fin n) :=
  fun p => if Disjoint p.1 Zo then p.1 else ∅

/-- Body of a pair `(T, c)` (truncated to `∅` when it leaves the reserve `Zo`). -/
def pairBd (Zo : Finset (Fin n)) (ends' : Finset (Fin n) → E' → Finset (Fin n)) :
    Finset (Fin n) × E' → Finset (Fin n) :=
  fun p => if ends' p.1 p.2 ⊆ Zo then ends' p.1 p.2 else ∅

/-- The tagged multigraph of the pairs `(T, c)`, `T ∈ Ts`, `c ∈ Y T`. -/
def pairSet (Ts : Finset (Finset (Fin n))) (Y : Finset (Fin n) → Finset E') :
    Finset (Finset (Fin n) × E') :=
  Ts.biUnion fun T => (Y T).image (Prod.mk T)

theorem mem_pairSet {Ts : Finset (Finset (Fin n))} {Y : Finset (Fin n) → Finset E'}
    {p : Finset (Fin n) × E'} : p ∈ pairSet Ts Y ↔ p.1 ∈ Ts ∧ p.2 ∈ Y p.1 := by
  obtain ⟨T, c⟩ := p
  simp [pairSet]

omit [DecidableEq E'] in
theorem pairTg_disjoint (Zo : Finset (Fin n)) (p : Finset (Fin n) × E') :
    Disjoint (pairTg Zo p) Zo := by
  unfold pairTg; split_ifs with h
  · exact h
  · exact disjoint_empty_left _

omit [DecidableEq E'] in
theorem pairBd_subset (Zo : Finset (Fin n)) (ends' : Finset (Fin n) → E' → Finset (Fin n))
    (p : Finset (Fin n) × E') : pairBd Zo ends' p ⊆ Zo := by
  unfold pairBd; split_ifs with h
  · exact h
  · exact empty_subset _

omit [DecidableEq E'] in
theorem pairTg_eq {Zo : Finset (Fin n)} {p : Finset (Fin n) × E'} (h : Disjoint p.1 Zo) :
    pairTg Zo p = p.1 := if_pos h

omit [DecidableEq E'] in
theorem pairBd_eq {Zo : Finset (Fin n)} {ends' : Finset (Fin n) → E' → Finset (Fin n)}
    {p : Finset (Fin n) × E'} (h : ends' p.1 p.2 ⊆ Zo) : pairBd Zo ends' p = ends' p.1 p.2 :=
  if_pos h

theorem fibre_pairSet {Zo : Finset (Fin n)} {Ts : Finset (Finset (Fin n))}
    {Y : Finset (Fin n) → Finset E'} (hTs : ∀ T ∈ Ts, Disjoint T Zo) {T : Finset (Fin n)}
    (hT : T ∈ Ts) : fibre (pairTg Zo) (pairSet Ts Y) T = (Y T).image (Prod.mk T) := by
  ext ⟨T', c⟩
  simp only [fibre, mem_filter, mem_pairSet, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [pairTg_eq (hTs _ h1)] at h3
    subst h3
    exact ⟨c, h2, rfl, rfl⟩
  · rintro ⟨c', hc', rfl, rfl⟩
    exact ⟨⟨hT, hc'⟩, pairTg_eq (hTs _ hT)⟩

theorem image_pairSet_subset {Zo : Finset (Fin n)} {Ts : Finset (Finset (Fin n))}
    {Y : Finset (Fin n) → Finset E'} (hTs : ∀ T ∈ Ts, Disjoint T Zo) :
    (pairSet Ts Y).image (pairTg Zo) ⊆ Ts := by
  intro T hT
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hT
  have hp' := mem_pairSet.1 hp
  rw [pairTg_eq (hTs _ hp'.1)]
  exact hp'.1

theorem mem_image_pairSet {Zo : Finset (Fin n)} {Ts : Finset (Finset (Fin n))}
    {Y : Finset (Fin n) → Finset E'} (hTs : ∀ T ∈ Ts, Disjoint T Zo) {T : Finset (Fin n)}
    (hT : T ∈ Ts) {c : E'} (hc : c ∈ Y T) : T ∈ (pairSet Ts Y).image (pairTg Zo) :=
  mem_image.2 ⟨(T, c), mem_pairSet.2 ⟨hT, hc⟩, pairTg_eq (hTs _ hT)⟩

/-- Lifted degrees of `pairSet`. -/
theorem mdeg_lift_pairSet {Zo : Finset (Fin n)} {Ts : Finset (Finset (Fin n))}
    {Y : Finset (Fin n) → Finset E'} {ends' : Finset (Fin n) → E' → Finset (Fin n)}
    (hTs : ∀ T ∈ Ts, Disjoint T Zo) (hY : ∀ T ∈ Ts, ∀ c ∈ Y T, ends' T c ⊆ Zo)
    (S : Finset (Fin n)) :
    mdeg (liftEnds (pairTg Zo) (pairBd Zo ends')) (pairSet Ts Y) S =
      ∑ T ∈ Ts, mdeg (fun c => T ∪ ends' T c) (Y T) S := by
  unfold mdeg pairSet
  rw [filter_biUnion, card_biUnion]
  · refine sum_congr rfl fun T hT => ?_
    rw [filter_image, card_image_of_injective _ (Prod.mk_right_injective T)]
    congr 1
    refine filter_congr fun c hc => ?_
    simp only [liftEnds]
    rw [pairTg_eq (p := (T, c)) (hTs T hT), pairBd_eq (p := (T, c)) (hY T hT c hc)]
  · intro T _ T' _ hne
    simp only [Function.onFun, disjoint_left, mem_filter, mem_image]
    rintro p ⟨⟨c, -, rfl⟩, -⟩ ⟨⟨c', -, h⟩, -⟩
    exact hne (Prod.mk.inj h).1.symm

end Pair

/-- Relabelling the copies does not increase piece degrees (relabelling compatible with the ends
only on the copies of the pieces). -/
theorem pdeg_image_le_of_mem {V E₁ E₂ : Type*} [DecidableEq V] [DecidableEq E₂]
    {ends₁ : E₁ → Finset V} {ends₂ : E₂ → Finset V} (g : E₁ → E₂) (𝒲 : Finset (Finset E₁))
    (hends : ∀ W ∈ 𝒲, ∀ c ∈ W, ends₂ (g c) = ends₁ c) (S : Finset V) :
    pdeg ends₂ (𝒲.image (image g)) S ≤ pdeg ends₁ 𝒲 S := by
  unfold pdeg
  rw [filter_image]
  refine card_image_le.trans (card_le_card fun W hW => ?_)
  rw [mem_filter] at hW ⊢
  refine ⟨hW.1, ?_⟩
  have hspan : (W.image g).biUnion ends₂ = W.biUnion ends₁ := by
    rw [image_biUnion]
    exact biUnion_congr rfl fun c hc => hends W hW.1 c hc
  have := hW.2
  rw [hspan] at this
  exact this

/-- **Composition of tagged outputs.** -/
theorem TaggedOutE.comp {q r i j C₁ C₂ : ℕ} {n : ℕ} {E : Type} [DecidableEq E]
    {tg bd : E → Finset (Fin n)} {Zo Z U : Finset (Fin n)} {X : Finset E} {D Bd₁ : ℕ}
    (P : ℕ → Prop) (h : TaggedOutE q r i j C₁ tg bd Zo Z X Bd₁)
    (hnext : ∀ (E₁ : Type) [DecidableEq E₁] (tg₁ bd₁ : E₁ → Finset (Fin n)) (X₁ : Finset E₁),
      (∀ x, Disjoint (tg₁ x) Zo) → (∀ x, bd₁ x ⊆ Zo) → (∀ x ∈ X₁, (tg₁ x).card = i) →
      (∀ x ∈ X₁, (bd₁ x).card = r - i) → IsFlat j Z bd₁ X₁ →
      (∀ x ∈ X₁, liftEnds tg₁ bd₁ x ⊆ U) →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg₁ bd₁) X₁ S ≤ D + Bd₁) →
      ∃ Bd₂, P Bd₂ ∧ TaggedOutE q r i 0 C₂ tg₁ bd₁ Zo Z X₁ Bd₂)
    (htg : ∀ x, Disjoint (tg x) Zo) (hbd : ∀ x, bd x ⊆ Zo) (htgc : ∀ x ∈ X, (tg x).card = i)
    (hZoU : Zo ⊆ U) (hXU : ∀ x ∈ X, liftEnds tg bd x ⊆ U)
    (hdegX : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) :
    ∃ Bd₂, P Bd₂ ∧ TaggedOutE q r i 0 (C₁ + C₂) tg bd Zo Z X (Bd₁ + Bd₂) := by
  obtain ⟨E₁, _, g, ends₁, R₁, Y₁, 𝒲₁, hg, hends, hT₁, hdeg₁, hpd₁⟩ := h
  set Ts := X.image tg with hTsdef
  have hTs : ∀ T ∈ Ts, Disjoint T Zo := by
    intro T hT; obtain ⟨x, -, rfl⟩ := mem_image.1 hT; exact htg x
  have hXRZo : ∀ T ∈ Ts, ∀ c ∈ (fibre tg X T).image g ∪ R₁ T, ends₁ T c ⊆ Zo := by
    intro T hT c hc
    rcases mem_union.1 hc with hc | hc
    · obtain ⟨x, -, rfl⟩ := mem_image.1 hc; rw [hends]; exact hbd x
    · exact (hT₁ T hT).2.2.2.2 c hc
  have hYZo : ∀ T ∈ Ts, ∀ c ∈ Y₁ T, ends₁ T c ⊆ Zo :=
    fun T hT c hc => hXRZo T hT c ((hT₁ T hT).2.2.2.1 hc)
  set X₁ := pairSet Ts Y₁ with hX₁def
  -- the hypotheses of the next step
  have h1 : ∀ x ∈ X₁, (pairTg Zo x).card = i := by
    intro p hp
    have hp' := mem_pairSet.1 hp
    rw [pairTg_eq (hTs _ hp'.1)]
    obtain ⟨x, hx, hxT⟩ := mem_image.1 hp'.1
    rw [← hxT]; exact htgc x hx
  have h2 : ∀ x ∈ X₁, (pairBd Zo ends₁ x).card = r - i := by
    intro p hp
    have hp' := mem_pairSet.1 hp
    rw [pairBd_eq (hYZo _ hp'.1 _ hp'.2)]
    exact (hT₁ _ hp'.1).2.1.rgraph _ ((hT₁ _ hp'.1).2.2.2.1 hp'.2)
  have h3 : IsFlat j Z (pairBd Zo ends₁) X₁ := by
    intro p hp
    have hp' := mem_pairSet.1 hp
    rw [pairBd_eq (hYZo _ hp'.1 _ hp'.2)]
    exact (hT₁ _ hp'.1).2.2.1 _ hp'.2
  have h4 : ∀ x ∈ X₁, liftEnds (pairTg Zo) (pairBd Zo ends₁) x ⊆ U := by
    intro p hp
    have hp' := mem_pairSet.1 hp
    unfold liftEnds
    refine union_subset ?_ ((pairBd_subset _ _ _).trans hZoU)
    rw [pairTg_eq (hTs _ hp'.1)]
    obtain ⟨x, hx, hxT⟩ := mem_image.1 hp'.1
    rw [← hxT]; exact subset_union_left.trans (hXU x hx)
  have h5 : ∀ S : Finset (Fin n), S.card = r - 1 →
      mdeg (liftEnds (pairTg Zo) (pairBd Zo ends₁)) X₁ S ≤ D + Bd₁ := by
    intro S hS
    rw [mdeg_lift_pairSet hTs hYZo]
    calc ∑ T ∈ Ts, mdeg (fun c => T ∪ ends₁ T c) (Y₁ T) S
        ≤ ∑ T ∈ Ts, (mdeg (fun c => T ∪ bd c) (fibre tg X T) S +
            mdeg (fun c => T ∪ ends₁ T c) (R₁ T) S) := by
          refine sum_le_sum fun T hT => ?_
          calc mdeg (fun c => T ∪ ends₁ T c) (Y₁ T) S
              ≤ mdeg (fun c => T ∪ ends₁ T c) ((fibre tg X T).image g ∪ R₁ T) S :=
                mdeg_mono _ (hT₁ T hT).2.2.2.1 S
            _ ≤ mdeg (fun c => T ∪ ends₁ T c) ((fibre tg X T).image g) S +
                mdeg (fun c => T ∪ ends₁ T c) (R₁ T) S := by
                unfold mdeg; rw [filter_union]; exact card_union_le _ _
            _ = _ := by
                rw [mdeg_image_eq (A := fibre tg X T) (ends := fun c => T ∪ bd c)
                  (fun c _ => by simp only [hends]) hg.injOn subset_rfl]
      _ ≤ D + Bd₁ := by
          rw [sum_add_distrib, ← mdeg_liftEnds_eq_sum]
          exact Nat.add_le_add (hdegX S hS) (hdeg₁ S hS)
  obtain ⟨Bd₂, hP, E₂, _, g₂, ends₂, R₂, Y₂, 𝒲₂, hg₂, hends₂, hT₂, hdeg₂, hpd₂⟩ :=
    hnext (Finset (Fin n) × E₁) (pairTg Zo) (pairBd Zo ends₁) X₁ (pairTg_disjoint Zo)
      (pairBd_subset Zo ends₁) h1 h2 h3 h4 h5
  set Ts₁ := X₁.image (pairTg Zo) with hTs₁def
  have hTs₁ : Ts₁ ⊆ Ts := image_pairSet_subset hTs
  have hYempty : ∀ T ∈ Ts, T ∉ Ts₁ → Y₁ T = ∅ := by
    intro T hT hT'
    rw [eq_empty_iff_forall_notMem]
    intro c hc
    exact hT' (mem_image_pairSet hTs hT hc)
  -- relabelling of the copies of the first stage, tag by tag
  have hends₂' : ∀ T ∈ Ts, ∀ c ∈ (fibre tg X T).image g ∪ R₁ T, ends₂ T (g₂ (T, c)) = ends₁ T c :=
    fun T hT c hc => by rw [hends₂]; exact pairBd_eq (p := (T, c)) (hXRZo T hT c hc)
  have hinj : ∀ T : Finset (Fin n), Function.Injective fun c : E₁ => g₂ (T, c) :=
    fun T => hg₂.comp (Prod.mk_right_injective T)
  have hfibimg : ∀ T : Finset (Fin n),
      ((fibre tg X T).image g).image (fun c => g₂ (T, c)) =
        (fibre tg X T).image (fun x => g₂ (tg x, g x)) := by
    intro T
    rw [image_image]
    refine image_congr fun x hx => ?_
    simp only [Function.comp, (mem_fibre.1 hx).2]
  refine ⟨Bd₂, hP, E₂, inferInstance, fun x => g₂ (tg x, g x), ends₂,
    fun T => (R₁ T).image (fun c => g₂ (T, c)) ∪ (if T ∈ Ts₁ then R₂ T else ∅),
    fun T => if T ∈ Ts₁ then Y₂ T else ∅,
    fun T => (𝒲₁ T).image (image fun c => g₂ (T, c)) ∪ (if T ∈ Ts₁ then 𝒲₂ T else ∅),
    ?_, ?_, fun T hT => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · intro x y hxy
    exact hg (Prod.mk.inj (hg₂ hxy)).2
  · intro T c
    rw [hends₂]
    simp only [pairBd, hends, if_pos (hbd c)]
  · obtain ⟨hR₁g, hres₁, -, hY₁, hR₁Zo⟩ := hT₁ T hT
    have hrel := residual_relabel hres₁ (fun c => g₂ (T, c)) (ends₂ T) (hends₂' T hT)
      (hinj T).injOn hY₁
    have hdisj : ∀ R : Finset E₂, (∀ c ∈ R, ∀ y, g₂ y ≠ c) →
        Disjoint R (((fibre tg X T).image g).image (fun c => g₂ (T, c)) ∪
          (R₁ T).image (fun c => g₂ (T, c))) := by
      intro R hR
      rw [disjoint_left]
      intro c hc hc'
      rw [← image_union] at hc'
      obtain ⟨x, -, rfl⟩ := mem_image.1 hc'
      exact hR _ hc _ rfl
    have hYsub : (Y₁ T).image (fun c => g₂ (T, c)) ⊆
        ((fibre tg X T).image g).image (fun c => g₂ (T, c)) ∪
          (R₁ T).image (fun c => g₂ (T, c)) := by
      rw [← image_union]; exact image_subset_image hY₁
    by_cases hT' : T ∈ Ts₁
    · simp only [if_pos hT']
      obtain ⟨hR₂g, hres₂, hflat₂, hY₂, hR₂Zo⟩ := hT₂ T hT'
      have hfib₁ : (fibre (pairTg Zo) X₁ T).image g₂ = (Y₁ T).image (fun c => g₂ (T, c)) := by
        rw [fibre_pairSet hTs hT, image_image]; rfl
      rw [hfib₁] at hres₂ hY₂
      have hcomp := hrel.trans hres₂ hYsub (hdisj _ hR₂g)
      rw [hfibimg] at hcomp
      refine ⟨?_, hcomp, hflat₂, ?_, ?_⟩
      · intro c hc x hx
        rcases mem_union.1 hc with hc | hc
        · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
          have := Prod.mk.inj (hg₂ hx)
          exact hR₁g c₁ hc₁ x this.2
        · exact hR₂g c hc _ hx
      · refine hY₂.trans (union_subset ?_ (subset_union_right.trans subset_union_right))
        refine hYsub.trans ?_
        rw [hfibimg]
        exact union_subset_union subset_rfl subset_union_left
      · intro c hc
        rcases mem_union.1 hc with hc | hc
        · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
          rw [hends₂' T hT c₁ (mem_union_right _ hc₁)]
          exact hR₁Zo c₁ hc₁
        · exact hR₂Zo c hc
    · simp only [if_neg hT', union_empty]
      have hY0 := hYempty T hT hT'
      rw [hY0, image_empty] at hrel
      have hself : IsResidualMultiRefiner (q - i) (r - i) C₂ (ends₂ T) ∅ ∅ ∅ ∅ :=
        isResidualMultiRefiner_self C₂ (by simp [MIsRGraph])
      have hcomp := hrel.trans hself (empty_subset _) (disjoint_empty_left _)
      rw [union_empty, union_empty, hfibimg] at hcomp
      refine ⟨?_, hcomp, by simp [IsFlat], empty_subset _, ?_⟩
      · intro c hc x hx
        obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        exact hR₁g c₁ hc₁ x (Prod.mk.inj (hg₂ hx)).2
      · intro c hc
        obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        rw [hends₂' T hT c₁ (mem_union_right _ hc₁)]
        exact hR₁Zo c₁ hc₁
  · have hsplit : ∀ T ∈ Ts, mdeg (fun c => T ∪ ends₂ T c)
        ((R₁ T).image (fun c => g₂ (T, c)) ∪ (if T ∈ Ts₁ then R₂ T else ∅)) S ≤
        mdeg (fun c => T ∪ ends₁ T c) (R₁ T) S +
          (if T ∈ Ts₁ then mdeg (fun c => T ∪ ends₂ T c) (R₂ T) S else 0) := by
      intro T hT
      refine le_trans (by unfold mdeg; rw [filter_union]; exact card_union_le _ _)
        (Nat.add_le_add (le_of_eq ?_) (le_of_eq ?_))
      · exact mdeg_image_eq (A := R₁ T) (ends := fun c => T ∪ ends₁ T c)
          (fun c hc => by simp only [hends₂' T hT c (mem_union_right _ hc)]) (hinj T).injOn
          subset_rfl S
      · split_ifs <;> simp [mdeg]
    refine (sum_le_sum hsplit).trans ?_
    rw [sum_add_distrib, sum_ite_mem, inter_eq_right.2 hTs₁]
    exact Nat.add_le_add (hdeg₁ S hS) (hdeg₂ S hS)
  · have hsplit : ∀ T ∈ Ts, pdeg (fun c => T ∪ ends₂ T c)
        ((𝒲₁ T).image (image fun c => g₂ (T, c)) ∪ (if T ∈ Ts₁ then 𝒲₂ T else ∅)) S ≤
        pdeg (fun c => T ∪ ends₁ T c) (𝒲₁ T) S +
          (if T ∈ Ts₁ then pdeg (fun c => T ∪ ends₂ T c) (𝒲₂ T) S else 0) := by
      intro T hT
      refine (pdeg_union_le _ _ _ _).trans (Nat.add_le_add ?_ (le_of_eq ?_))
      · exact pdeg_image_le_of_mem (ends₁ := fun c => T ∪ ends₁ T c) _ _
          (fun W hW c hc => by
            simp only [hends₂' T hT c ((hT₁ T hT).2.1.subset W hW hc)]) S
      · split_ifs <;> simp [pdeg]
    refine (sum_le_sum hsplit).trans ?_
    rw [sum_add_distrib, sum_ite_mem, inter_eq_right.2 hTs₁]
    exact Nat.add_le_add (hpd₁ S hS) (hpd₂ S hS)

/-- **Chaining the flat steps of all link graphs at once.**  From bodies that are `j`-flat with
respect to the sub-reserve `Z`, the link levels `i + 1, …, i + j` (in `ε`-form) give, for all
fibres at once, residual refiners with residue inside `Z`, whose lifted new copies and pieces have
`(r-1)`-degrees `≤ C_s · D + B · |Z| / 2^s` summed over all tags. -/
theorem taggedChainE {q r i : ℕ} (hrq : r < q)
    (hL : ∀ j, 1 ≤ j → i + j < r → PlacedLinkLevelE q r (i + j)) :
    ∀ j, i + j < r → ∀ K : ℕ, ∃ Cr B : ℕ, ∀ s : ℕ, ∃ Cs C : ℕ, ∀ (n : ℕ) {E : Type}
      [DecidableEq E] (tg bd : E → Finset (Fin n)) (Zo Z U : Finset (Fin n)) (X : Finset E)
      (D : ℕ),
      Z ⊆ Zo → (∀ x, Disjoint (tg x) Zo) → (∀ x, bd x ⊆ Zo) →
      (∀ x ∈ X, (tg x).card = i) → (∀ x ∈ X, (bd x).card = r - i) → IsFlat j Z bd X →
      Zo ⊆ U → (∀ x ∈ X, liftEnds tg bd x ⊆ U) → U.card ≤ K * Z.card → q + r ≤ Z.card →
      1 ≤ D → Cs ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) →
      ∃ Bd : ℕ, 2 ^ s * Bd ≤ 2 ^ s * C * D + B * Z.card ∧
        TaggedOutE q r i 0 Cr tg bd Zo Z X Bd := by
  intro j
  induction j with
  | zero =>
    intro _ K
    refine ⟨1, 0, fun s => ⟨0, 0, ?_⟩⟩
    intro n E _ tg bd Zo Z U X D _ _ _ _ hbdc hX _ _ _ _ _ _ _
    refine ⟨0, by simp, E, inferInstance, id, fun _ => bd, fun _ => ∅, fun T => fibre tg X T,
      fun _ => ∅, Function.injective_id, fun T c => rfl, fun T _ => ?_, fun S _ => by simp [mdeg],
      fun S _ => by simp [pdeg]⟩
    rw [image_id]
    refine ⟨by simp, isResidualMultiRefiner_self 1 fun x hx => hbdc x (fibre_subset _ _ _ hx),
      fun x hx => hX x (fibre_subset _ _ _ hx), by simp, by simp⟩
  | succ j ih =>
    intro hj K
    obtain ⟨Cr₁, B₁, hstep⟩ := taggedStep_of_levelE (j := j + 1) (by omega) hj hrq
      (hL (j + 1) (by omega) hj) K
    obtain ⟨Cr₂, B₂, hrest⟩ := ih (by omega) K
    refine ⟨Cr₁ + Cr₂, B₁ + B₂, fun s => ?_⟩
    obtain ⟨Cs₂, C₂, hrest'⟩ := hrest (s + 1)
    obtain ⟨Cs₁, C₁, hstep'⟩ := hstep (s + (C₂ + 1))
    refine ⟨Cs₁ + Cs₂, 2 ^ (C₂ + 1) * C₁ + 2 * C₂, ?_⟩
    intro n E _ tg bd Zo Z U X D hZ htg hbd htgc hbdc hX hZoU hU hUK hZq hD1 hCD hdeg
    obtain ⟨Bd₁, hBd₁, hout₁⟩ :=
      hstep' n tg bd Zo Z U X D hZ htg hbd htgc hbdc hX hU hUK hZq hD1 (le_trans (by omega) hCD)
        hdeg
    rw [Nat.add_sub_cancel] at hout₁
    obtain ⟨Bd₂, hBd₂, hout⟩ := hout₁.comp
      (fun Bd₂ => 2 ^ (s + 1) * Bd₂ ≤ 2 ^ (s + 1) * C₂ * (D + Bd₁) + B₂ * Z.card)
      (fun E₁ _ tg₁ bd₁ X₁ h1 h2 h3 h4 h5 h6 h7 => hrest' n tg₁ bd₁ Zo Z U X₁ (D + Bd₁) hZ h1 h2
        h3 h4 h5 hZoU h6 hUK hZq (by omega) (le_trans (by omega) hCD) h7)
      htg hbd htgc hZoU hU hdeg
    refine ⟨Bd₁ + Bd₂, ?_, hout⟩
    have hC2 : 2 * (C₂ + 1) ≤ 2 ^ (C₂ + 1) := by
      have := Nat.lt_two_pow_self (n := C₂)
      rw [pow_succ]; omega
    have e1 : 2 ^ (s + (C₂ + 1)) = 2 ^ s * 2 ^ (C₂ + 1) := pow_add _ _ _
    rw [e1] at hBd₁
    have e2 : 2 ^ (s + 1) = 2 ^ s * 2 := pow_succ _ _
    rw [e2] at hBd₂
    have h3 : 2 * (2 ^ s * ((C₂ + 1) * Bd₁)) ≤ 2 ^ s * 2 ^ (C₂ + 1) * Bd₁ := by
      calc 2 * (2 ^ s * ((C₂ + 1) * Bd₁)) = 2 ^ s * (2 * (C₂ + 1)) * Bd₁ := by ring
        _ ≤ 2 ^ s * 2 ^ (C₂ + 1) * Bd₁ :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hC2)
    have key : 2 * (2 ^ s * (Bd₁ + Bd₂)) ≤
        2 * (2 ^ s * (2 ^ (C₂ + 1) * C₁ + 2 * C₂) * D + (B₁ + B₂) * Z.card) := by
      have e3 : 2 ^ s * 2 * Bd₂ = 2 * (2 ^ s * Bd₂) := by ring
      have e4 : 2 ^ s * 2 * C₂ * (D + Bd₁) = 2 * (2 ^ s * C₂ * D) + 2 * (2 ^ s * C₂ * Bd₁) := by
        ring
      rw [e3, e4] at hBd₂
      have e5 : 2 ^ s * ((C₂ + 1) * Bd₁) = 2 ^ s * C₂ * Bd₁ + 2 ^ s * Bd₁ := by ring
      have e6 : 2 ^ s * 2 ^ (C₂ + 1) * C₁ * D = 2 ^ s * (2 ^ (C₂ + 1) * C₁) * D := by ring
      have e7 : 2 * (2 ^ s * (2 ^ (C₂ + 1) * C₁ + 2 * C₂) * D + (B₁ + B₂) * Z.card) =
          2 * (2 ^ s * (2 ^ (C₂ + 1) * C₁) * D) + 4 * (2 ^ s * C₂ * D) +
            2 * (B₁ * Z.card) + 2 * (B₂ * Z.card) := by ring
      have e8 : 2 ^ s * (Bd₁ + Bd₂) = 2 ^ s * Bd₁ + 2 ^ s * Bd₂ := by ring
      rw [e7, e8]
      rw [e5] at h3
      omega
    omega

end RefinedAbsorption.LinkSpread
