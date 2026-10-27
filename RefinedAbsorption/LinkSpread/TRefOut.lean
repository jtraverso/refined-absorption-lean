module
public import RefinedAbsorption.LinkSpread.Stage
public import RefinedAbsorption.LinkSpread.Assembly

/-!
# Complete tagged refiners and their bookkeeping

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

`TRefOut q r i C tg bd Z X β`: for every tag `T` of `X`, a complete chain refiner (constants
`C, C, C`, empty residue) of the bodies of the fibre of `T`, with new copies inside `Z`; the lifted
new copies and lifted pieces have `(r-1)`-degree at most `β S` at every `(r-1)`-set `S`, summed
over the tags.  The budget is allowed to depend on `S`: this is what lets disjoint reserves be
used by different classes of tags at no extra cost.

* `IsChainRefiner.relabel`: chain refiners are preserved by injective relabelling.
* `TRefOut.mono`, `TRefOut.toTaggedRefOutE`.
* **`TRefOut.union`**: tagged refiners of the two classes `{T ∈ A}` and `{T ∉ A}` of tags combine,
  with budget `β₁ + β₂`.
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown

/-- Chain refiners are preserved by injective relabelling. -/
theorem _root_.RefinedAbsorption.MultiRefiner.IsChainRefiner.relabel {V E E' : Type*}
    [DecidableEq V] [DecidableEq E] [DecidableEq E'] {q r A B P : ℕ} {ends : E → Finset V}
    {X R Y : Finset E} {𝒲 : Finset (Finset E)} (h : IsChainRefiner q r A B P ends X R Y 𝒲)
    (g : E → E') (ends' : E' → Finset V) (hends : ∀ c ∈ X ∪ R, ends' (g c) = ends c)
    (hg : Function.Injective g) :
    IsChainRefiner q r A B P ends' (X.image g) (R.image g) (Y.image g) (𝒲.image (image g)) := by
  have hcnt : ∀ c : E, ((𝒲.image (image g)).filter fun W => g c ∈ W).card ≤
      (𝒲.filter fun W => c ∈ W).card := by
    intro c
    rw [filter_image]
    refine card_image_le.trans (le_of_eq ?_)
    congr 1
    refine filter_congr fun W _ => ?_
    constructor
    · intro h'
      obtain ⟨d, hd, hdc⟩ := mem_image.1 h'
      rw [hg hdc] at hd; exact hd
    · exact fun h' => mem_image_of_mem _ h'
  refine ⟨(residual_relabel h.base g ends' hends hg.injOn
    (h.residue_sub.trans subset_union_right)).mono le_rfl, fun W hW => ?_,
    image_subset_image h.residue_sub, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨W₀, hW₀, rfl⟩ := mem_image.1 hW
    exact card_image_le.trans (h.card_le W₀ hW₀)
  · obtain ⟨c₀, hc₀, rfl⟩ := mem_image.1 hc
    exact (hcnt c₀).trans (h.multX c₀ hc₀)
  · obtain ⟨c₀, hc₀, rfl⟩ := mem_image.1 hc
    exact (hcnt c₀).trans (h.multR c₀ hc₀)
  · obtain ⟨c₀, hc₀, rfl⟩ := mem_image.1 hc
    exact (hcnt c₀).trans (h.multY c₀ hc₀)

/-- Complete tagged refiners inside `Z` with an `S`-dependent budget `β`. -/
def TRefOut (q r i C : ℕ) {n : ℕ} {E : Type} (tg bd : E → Finset (Fin n)) (Z : Finset (Fin n))
    (X : Finset E) (β : Finset (Fin n) → ℕ) : Prop :=
  ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : Finset (Fin n) → E' → Finset (Fin n))
    (R : Finset (Fin n) → Finset E') (𝒲 : Finset (Fin n) → Finset (Finset E')),
    Function.Injective g ∧ (∀ T c, ends' T (g c) = bd c) ∧
    (∀ T ∈ X.image tg, (∀ c ∈ R T, ∀ x, g x ≠ c) ∧
      IsChainRefiner (q - i) (r - i) C C C (ends' T) ((fibre tg X T).image g) (R T) ∅ (𝒲 T) ∧
      ∀ c ∈ R T, ends' T c ⊆ Z) ∧
    (∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T ∈ X.image tg, mdeg (fun c => T ∪ ends' T c) (R T) S ≤ β S) ∧
    ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T ∈ X.image tg, pdeg (fun c => T ∪ ends' T c) (𝒲 T) S ≤ β S

section Basic

variable {q r i C : ℕ} {n : ℕ} {E : Type} [DecidableEq E] {tg bd : E → Finset (Fin n)}
  {Z : Finset (Fin n)} {X : Finset E}

theorem TRefOut.mono {C' : ℕ} {β β' : Finset (Fin n) → ℕ} (h : TRefOut q r i C tg bd Z X β)
    (hC : C ≤ C') (hβ : ∀ S, S.card = r - 1 → β S ≤ β' S) :
    TRefOut q r i C' tg bd Z X β' := by
  obtain ⟨E', _, g, ends', R, 𝒲, hg, he, hT, hd, hp⟩ := h
  exact ⟨E', inferInstance, g, ends', R, 𝒲, hg, he,
    fun T hT' => ⟨(hT T hT').1, (hT T hT').2.1.mono' hC hC hC, (hT T hT').2.2⟩,
    fun S hS => (hd S hS).trans (hβ S hS), fun S hS => (hp S hS).trans (hβ S hS)⟩

/-- A `TRefOut` with constant budget gives the tagged multi-refiners of `TaggedRefOutE`. -/
theorem TRefOut.toTaggedRefOutE {Bd : ℕ} (h : TRefOut q r i C tg bd Z X fun _ => Bd) :
    TaggedRefOutE q r i (3 * C) tg bd Z X Bd := by
  obtain ⟨E', _, g, ends', R, 𝒲, hg, he, hT, hd, hp⟩ := h
  exact ⟨E', inferInstance, g, ends', R, 𝒲, hg, he,
    fun T hT' => ⟨(hT T hT').1, (hT T hT').2.1.base.mono (by omega), (hT T hT').2.2⟩, hd, hp⟩

/-- The empty tagged multigraph. -/
theorem TRefOut.empty (β : Finset (Fin n) → ℕ) : TRefOut q r i C tg bd Z ∅ β :=
  ⟨E, inferInstance, id, fun _ => bd, fun _ => ∅, fun _ => ∅, Function.injective_id,
    fun _ _ => rfl, by simp, by simp, by simp⟩

end Basic

section Union

variable {q r i C : ℕ} {n : ℕ} {E : Type} [DecidableEq E] {tg bd : E → Finset (Fin n)}
  {Z : Finset (Fin n)} {X : Finset E}

theorem fibre_filter_of_mem {p : Finset (Fin n) → Prop} [DecidablePred p] {T : Finset (Fin n)}
    (hT : p T) : fibre tg (X.filter fun x => p (tg x)) T = fibre tg X T := by
  ext x
  simp only [fibre, mem_filter]
  constructor
  · rintro ⟨⟨hx, -⟩, h⟩; exact ⟨hx, h⟩
  · rintro ⟨hx, h⟩; exact ⟨⟨hx, h ▸ hT⟩, h⟩

theorem image_filter_tg {p : Finset (Fin n) → Prop} [DecidablePred p] :
    (X.filter fun x => p (tg x)).image tg = (X.image tg).filter p := by
  ext T
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hp⟩, rfl⟩; exact ⟨⟨x, hx, rfl⟩, hp⟩
  · rintro ⟨⟨x, hx, rfl⟩, hp⟩; exact ⟨x, ⟨hx, hp⟩, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **Union of two classes of tags.** -/
theorem TRefOut.union (p : Finset (Fin n) → Prop) [DecidablePred p]
    {β₁ β₂ : Finset (Fin n) → ℕ}
    (h₁ : TRefOut q r i C tg bd Z (X.filter fun x => p (tg x)) β₁)
    (h₂ : TRefOut q r i C tg bd Z (X.filter fun x => ¬ p (tg x)) β₂) :
    TRefOut q r i C tg bd Z X (β₁ + β₂) := by
  obtain ⟨E₁, _, g₁, ends₁, R₁, 𝒲₁, hg₁, he₁, hT₁, hd₁, hp₁⟩ := h₁
  obtain ⟨E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, he₂, hT₂, hd₂, hp₂⟩ := h₂
  set g : E → E₁ ⊕ E₂ := fun x => if p (tg x) then Sum.inl (g₁ x) else Sum.inr (g₂ x) with hgdef
  set ends : Finset (Fin n) → E₁ ⊕ E₂ → Finset (Fin n) :=
    fun T => Sum.elim (ends₁ T) (ends₂ T) with hendsdef
  have hsplit : X.image tg = (X.image tg).filter p ∪ (X.image tg).filter (fun T => ¬ p T) :=
    (filter_union_filter_not_eq _ _).symm
  have hdisj : Disjoint ((X.image tg).filter p) ((X.image tg).filter (fun T => ¬ p T)) :=
    disjoint_filter_filter_not _ _ _
  refine ⟨E₁ ⊕ E₂, inferInstance, g, ends,
    fun T => if p T then (R₁ T).image Sum.inl else (R₂ T).image Sum.inr,
    fun T => if p T then (𝒲₁ T).image (image Sum.inl) else (𝒲₂ T).image (image Sum.inr),
    ?_, ?_, fun T hT => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · intro x y hxy
    by_cases hx : p (tg x) <;> by_cases hy : p (tg y) <;> simp [hgdef, hx, hy] at hxy
    · exact hg₁ hxy
    · exact hg₂ hxy
  · intro T c
    by_cases hc : p (tg c) <;> simp [hgdef, hendsdef, hc, he₁, he₂]
  · by_cases hpT : p T
    · have hT' : T ∈ (X.filter fun x => p (tg x)).image tg := by
        rw [image_filter_tg]; exact mem_filter.2 ⟨hT, hpT⟩
      obtain ⟨hf, hch, hZ⟩ := hT₁ T hT'
      rw [fibre_filter_of_mem (p := p) hpT] at hch
      have hrel := hch.relabel Sum.inl (ends T) (fun c _ => rfl) Sum.inl_injective
      have himg : ((fibre tg X T).image g₁).image Sum.inl = (fibre tg X T).image g := by
        rw [image_image]
        refine image_congr fun x hx => ?_
        simp only [Function.comp, hgdef, (mem_fibre.1 hx).2, if_pos hpT]
      rw [himg, image_empty] at hrel
      simp only [if_pos hpT]
      refine ⟨fun c hc x hx => ?_, hrel, fun c hc => ?_⟩
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        by_cases hpx : p (tg x) <;> simp [hgdef, hpx] at hx
        exact hf c₁ hc₁ x hx
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        exact hZ c₁ hc₁
    · have hT' : T ∈ (X.filter fun x => ¬ p (tg x)).image tg := by
        rw [image_filter_tg (p := fun T => ¬ p T)]; exact mem_filter.2 ⟨hT, hpT⟩
      obtain ⟨hf, hch, hZ⟩ := hT₂ T hT'
      rw [fibre_filter_of_mem (p := fun T => ¬ p T) hpT] at hch
      have hrel := hch.relabel Sum.inr (ends T) (fun c _ => rfl) Sum.inr_injective
      have himg : ((fibre tg X T).image g₂).image Sum.inr = (fibre tg X T).image g := by
        rw [image_image]
        refine image_congr fun x hx => ?_
        simp only [Function.comp, hgdef, (mem_fibre.1 hx).2, if_neg hpT]
      rw [himg, image_empty] at hrel
      simp only [if_neg hpT]
      refine ⟨fun c hc x hx => ?_, hrel, fun c hc => ?_⟩
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        by_cases hpx : p (tg x) <;> simp [hgdef, hpx] at hx
        exact hf c₁ hc₁ x hx
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        exact hZ c₁ hc₁
  · rw [hsplit, sum_union hdisj]
    refine Nat.add_le_add ?_ ?_
    · rw [← image_filter_tg]
      refine le_trans (le_of_eq (sum_congr rfl fun T hT => ?_)) (hd₁ S hS)
      have hpT : p T := by
        rw [image_filter_tg] at hT; exact (mem_filter.1 hT).2
      simp only [if_pos hpT]
      exact mdeg_image_eq (A := R₁ T) (ends := fun c => T ∪ ends₁ T c)
        (ends' := fun c => T ∪ ends T c) (g := Sum.inl) (fun c _ => rfl)
        Sum.inl_injective.injOn subset_rfl S
    · rw [← image_filter_tg (p := fun T => ¬ p T)]
      refine le_trans (le_of_eq (sum_congr rfl fun T hT => ?_)) (hd₂ S hS)
      have hpT : ¬ p T := by
        rw [image_filter_tg (p := fun T => ¬ p T)] at hT; exact (mem_filter.1 hT).2
      simp only [if_neg hpT]
      exact mdeg_image_eq (A := R₂ T) (ends := fun c => T ∪ ends₂ T c)
        (ends' := fun c => T ∪ ends T c) (g := Sum.inr) (fun c _ => rfl)
        Sum.inr_injective.injOn subset_rfl S
  · rw [hsplit, sum_union hdisj]
    refine Nat.add_le_add ?_ ?_
    · rw [← image_filter_tg]
      refine le_trans (sum_le_sum fun T hT => ?_) (hp₁ S hS)
      have hpT : p T := by
        rw [image_filter_tg] at hT; exact (mem_filter.1 hT).2
      simp only [if_pos hpT]
      exact pdeg_image_le Sum.inl (fun c => rfl) _ S
    · rw [← image_filter_tg (p := fun T => ¬ p T)]
      refine le_trans (sum_le_sum fun T hT => ?_) (hp₂ S hS)
      have hpT : ¬ p T := by
        rw [image_filter_tg (p := fun T => ¬ p T)] at hT; exact (mem_filter.1 hT).2
      simp only [if_neg hpT]
      exact pdeg_image_le Sum.inr (fun c => rfl) _ S

end Union

section Prepend

/-- A lifted set inside `T ∪ A` with `A ⊆ Z₁ ⊆ Zo` and `T` outside `Zo` meets `Zo` only inside
`Z₁`. -/
theorem lift_meet_sub {n : ℕ} {T S A Zo Z₁ : Finset (Fin n)} (hT : Disjoint T Zo)
    (hTS : T.card < S.card) (hA : A ⊆ Z₁) (hZ : Z₁ ⊆ Zo) (hS : S ⊆ T ∪ A) :
    (S ∩ Zo).Nonempty ∧ S ∩ Zo ⊆ Z₁ := by
  have hsub : S \ T ⊆ A := fun v hv => by
    rcases mem_union.1 (hS (mem_sdiff.1 hv).1) with h | h
    · exact absurd h (mem_sdiff.1 hv).2
    · exact h
  have hne : (S \ T).Nonempty := by
    rw [← card_pos]
    have := card_le_card_sdiff_add_card (s := S) (t := T)
    omega
  refine ⟨?_, fun v hv => ?_⟩
  · obtain ⟨v, hv⟩ := hne
    exact ⟨v, mem_inter.2 ⟨(mem_sdiff.1 hv).1, hZ (hA (hsub hv))⟩⟩
  · obtain ⟨hvS, hvZ⟩ := mem_inter.1 hv
    rcases mem_union.1 (hS hvS) with h | h
    · exact absurd hvZ (disjoint_left.1 hT h)
    · exact hA h

theorem biUnion_lift_subset {V E : Type} [DecidableEq V] (W : Finset E) (T : Finset V)
    (f : E → Finset V) : W.biUnion (fun c => T ∪ f c) ⊆ T ∪ W.biUnion f := by
  intro v hv
  obtain ⟨c, hc, hv⟩ := mem_biUnion.1 hv
  rcases mem_union.1 hv with h | h
  · exact mem_union_left _ h
  · exact mem_union_right _ (mem_biUnion.2 ⟨c, hc, h⟩)

set_option maxHeartbeats 4000000 in
/-- **A stage followed by complete refiners of its residue.**  The residue of the stage is handed
over (as a tagged multigraph all of whose copies are residue copies) to a construction `hnext`
of complete tagged refiners inside `Z₁`; the result is a complete tagged refiner inside `Zo`.  The
second budget is only charged at `(r-1)`-sets meeting `Zo` inside `Z₁`. -/
theorem TStageOut.prepend {q r i Cr M C : ℕ} (hC : Cr ≤ C) (hir : i + 1 < r) {n : ℕ} {E : Type}
    [DecidableEq E] {tg bd : E → Finset (Fin n)} {Zo Z₁ : Finset (Fin n)} {X : Finset E}
    {Bd₁ : ℕ} (hZ₁ : Z₁ ⊆ Zo) (htg : ∀ x, Disjoint (tg x) Zo) (htgc : ∀ x ∈ X, (tg x).card = i)
    (P : ℕ → Prop) (h : TStageOut q r i Cr M tg bd Zo Z₁ X Bd₁)
    (hnext : ∀ (E₁ : Type) [DecidableEq E₁] (tg₁ bd₁ : E₁ → Finset (Fin n)) (X₁ : Finset E₁),
      (∀ x, Disjoint (tg₁ x) Zo) → (∀ x, bd₁ x ⊆ Z₁) → (∀ x ∈ X₁, (tg₁ x).card = i) →
      (∀ x ∈ X₁, (bd₁ x).card = r - i) → X₁.image tg₁ ⊆ X.image tg →
      (∀ T e, mult bd₁ (fibre tg₁ X₁ T) e ≤ M) →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg₁ bd₁) X₁ S ≤ Bd₁) →
      ∃ Bd₂, P Bd₂ ∧ TRefOut q r i C tg₁ bd₁ Z₁ X₁ (fun _ => Bd₂)) :
    ∃ Bd₂, P Bd₂ ∧ TRefOut q r i C tg bd Zo X
      (fun S => Bd₁ + if (S ∩ Zo).Nonempty ∧ S ∩ Zo ⊆ Z₁ then Bd₂ else 0) := by
  obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, hg₁, hends₁, hT₁, hdeg₁, hpd₁⟩ := h
  set Ts := X.image tg with hTsdef
  have hTsZ : ∀ T ∈ Ts, Disjoint T Zo := by
    intro T hT; obtain ⟨x, -, rfl⟩ := mem_image.1 hT; exact htg x
  have hTsc : ∀ T ∈ Ts, T.card = i := by
    intro T hT; obtain ⟨x, hx, rfl⟩ := mem_image.1 hT; exact htgc x hx
  -- the residue as a tagged multigraph
  let Sb := {p : Finset (Fin n) × E₁ // p ∈ pairSet Ts Y₁}
  have hSb : ∀ p : Sb, p.1.1 ∈ Ts ∧ p.1.2 ∈ Y₁ p.1.1 := fun p => mem_pairSet.1 p.2
  let tg₁ : Sb → Finset (Fin n) := fun p => p.1.1
  let bd₁ : Sb → Finset (Fin n) := fun p => ends₁ p.1.1 p.1.2
  have h1 : ∀ p : Sb, Disjoint (tg₁ p) Zo := fun p => hTsZ _ (hSb p).1
  have h2 : ∀ p : Sb, bd₁ p ⊆ Z₁ := fun p => (hT₁ _ (hSb p).1).2.2.2.1 _ (hSb p).2
  have h3 : ∀ p ∈ (univ : Finset Sb), (tg₁ p).card = i := fun p _ => hTsc _ (hSb p).1
  have h4 : ∀ p ∈ (univ : Finset Sb), (bd₁ p).card = r - i := fun p _ =>
    (hT₁ _ (hSb p).1).2.1.rgraph _ (mem_union_right _ ((hT₁ _ (hSb p).1).2.2.1 (hSb p).2))
  have h5 : (univ : Finset Sb).image tg₁ ⊆ Ts := by
    intro T hT; obtain ⟨p, -, rfl⟩ := mem_image.1 hT; exact (hSb p).1
  have h6 : ∀ T e, mult bd₁ (fibre tg₁ univ T) e ≤ M := by
    intro T e
    by_cases hT : T ∈ Ts
    · refine le_trans ?_ ((hT₁ T hT).2.2.2.2.1 e)
      unfold mult fibre
      refine card_le_card_of_injOn (fun p => p.1.2) ?_ ?_
      · intro p hp
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hp ⊢
        obtain ⟨hpT, hpe⟩ := hp
        have hpT' : p.1.1 = T := hpT
        refine ⟨hpT' ▸ (hSb p).2, ?_⟩
        rw [← hpT']; exact hpe
      · intro p hp p' hp' hpp
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hp hp'
        have e1 : p.1.1 = p'.1.1 := hp.1.trans hp'.1.symm
        exact Subtype.ext (Prod.ext e1 hpp)
    · have : fibre tg₁ (univ : Finset Sb) T = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro p hp
        exact hT ((mem_fibre.1 hp).2 ▸ (hSb p).1)
      rw [this]; simp [mult]
  have h7 : ∀ S : Finset (Fin n), S.card = r - 1 →
      mdeg (liftEnds tg₁ bd₁) (univ : Finset Sb) S ≤ Bd₁ := by
    intro S hS
    refine le_trans ?_ ((sum_le_sum fun T hT => mdeg_mono _ ((hT₁ T hT).2.2.1) S).trans
      (hdeg₁ S hS))
    unfold mdeg
    rw [← card_sigma]
    refine card_le_card_of_injOn (fun p => ⟨p.1.1, p.1.2⟩) ?_ ?_
    · intro p hp
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hp
      simp only [mem_coe, mem_sigma, mem_filter]
      exact ⟨(hSb p).1, (hSb p).2, hp⟩
    · intro p _ p' _ hpp
      simp only [Sigma.mk.injEq] at hpp
      exact Subtype.ext (Prod.ext hpp.1 (eq_of_heq hpp.2))
  obtain ⟨Bd₂, hP, E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, hends₂, hT₂, hdeg₂, hpd₂⟩ :=
    hnext Sb tg₁ bd₁ univ h1 h2 h3 h4 h5 h6 h7
  set Ts₁ := (univ : Finset Sb).image tg₁ with hTs₁def
  -- relabelling of the copies of the stage
  let gT : Finset (Fin n) → E₁ → (Finset (Fin n) × E₁) ⊕ E₂ := fun T c =>
    if hc : T ∈ Ts ∧ c ∈ Y₁ T then Sum.inr (g₂ ⟨(T, c), mem_pairSet.2 hc⟩) else Sum.inl (T, c)
  let ends₃ : Finset (Fin n) → (Finset (Fin n) × E₁) ⊕ E₂ → Finset (Fin n) :=
    fun T => Sum.elim (fun p => ends₁ p.1 p.2) (ends₂ T)
  have hgT_ends : ∀ T c, ends₃ T (gT T c) = ends₁ T c := by
    intro T c
    by_cases hc : T ∈ Ts ∧ c ∈ Y₁ T
    · simp only [gT, ends₃, dif_pos hc, Sum.elim_inr]; exact hends₂ T _
    · simp only [gT, ends₃, dif_neg hc, Sum.elim_inl]
  have hgT_inj : ∀ T, Function.Injective (gT T) := by
    intro T c c' hcc
    by_cases hc : T ∈ Ts ∧ c ∈ Y₁ T <;> by_cases hc' : T ∈ Ts ∧ c' ∈ Y₁ T
    · dsimp only [gT] at hcc; rw [dif_pos hc, dif_pos hc'] at hcc
      exact congrArg (fun p : Sb => p.1.2) (hg₂ (Sum.inr_injective hcc))
    · dsimp only [gT] at hcc; rw [dif_pos hc, dif_neg hc'] at hcc
      exact absurd hcc Sum.inr_ne_inl
    · dsimp only [gT] at hcc; rw [dif_neg hc, dif_pos hc'] at hcc
      exact absurd hcc Sum.inl_ne_inr
    · dsimp only [gT] at hcc; rw [dif_neg hc, dif_neg hc'] at hcc
      exact (Prod.mk.inj (Sum.inl_injective hcc)).2
  have hgT_old : ∀ T x, tg x = T → gT T (g₁ x) = Sum.inl (tg x, g₁ x) := by
    intro T x hx
    have hc : ¬ (T ∈ Ts ∧ g₁ x ∈ Y₁ T) := by
      rintro ⟨hT, hY⟩
      exact (hT₁ T hT).1 _ ((hT₁ T hT).2.2.1 hY) x rfl
    simp only [gT, dif_neg hc, hx]
  refine ⟨Bd₂, hP, (Finset (Fin n) × E₁) ⊕ E₂, inferInstance, fun x => Sum.inl (tg x, g₁ x),
    ends₃, fun T => (R₁ T).image (gT T) ∪ (if T ∈ Ts₁ then (R₂ T).image Sum.inr else ∅),
    fun T => (𝒲₁ T).image (image (gT T)) ∪
      (if T ∈ Ts₁ then (𝒲₂ T).image (image Sum.inr) else ∅),
    fun x y hxy => hg₁ (Prod.mk.inj (Sum.inl_injective hxy)).2,
    fun T c => by simp only [ends₃, Sum.elim_inl, hends₁], fun T hT => ?_, fun S hS => ?_,
    fun S hS => ?_⟩
  · obtain ⟨hR₁f, hres₁, hYR, hYZ, -, hR₁Zo⟩ := hT₁ T hT
    have hfib : ((fibre tg X T).image g₁).image (gT T) =
        (fibre tg X T).image fun x => Sum.inl (tg x, g₁ x) := by
      rw [image_image]
      exact image_congr fun x hx => hgT_old T x (mem_fibre.1 hx).2
    have hfresh : ∀ c ∈ (R₁ T).image (gT T) ∪ (if T ∈ Ts₁ then (R₂ T).image Sum.inr else ∅),
        ∀ x, (Sum.inl (tg x, g₁ x) : (Finset (Fin n) × E₁) ⊕ E₂) ≠ c := by
      intro c hc x hx
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        by_cases hc' : T ∈ Ts ∧ c₁ ∈ Y₁ T
        · simp only [gT, dif_pos hc', reduceCtorEq] at hx
        · simp only [gT, dif_neg hc', Sum.inl.injEq, Prod.mk.injEq] at hx
          exact hR₁f c₁ hc₁ x hx.2
      · split_ifs at hc
        · obtain ⟨c₂, -, rfl⟩ := mem_image.1 hc
          exact Sum.inl_ne_inr hx
        · simp at hc
    have hZo : ∀ c ∈ (R₁ T).image (gT T) ∪ (if T ∈ Ts₁ then (R₂ T).image Sum.inr else ∅),
        ends₃ T c ⊆ Zo := by
      intro c hc
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        rw [hgT_ends]; exact hR₁Zo c₁ hc₁
      · split_ifs at hc
        · obtain ⟨c₂, hc₂, rfl⟩ := mem_image.1 hc
          obtain ⟨-, -, hR₂Z⟩ := hT₂ T (by assumption)
          exact (hR₂Z c₂ hc₂).trans hZ₁
        · simp at hc
    by_cases hT' : T ∈ Ts₁
    · obtain ⟨hR₂f, hch₂, hR₂Z⟩ := hT₂ T hT'
      have hrel := hch₂.relabel Sum.inr (ends₃ T) (fun c _ => rfl) Sum.inr_injective
      have hYimg : ((fibre tg₁ univ T).image g₂).image Sum.inr = (Y₁ T).image (gT T) := by
        ext c
        simp only [mem_image, fibre, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨c₂, ⟨p, hp, rfl⟩, rfl⟩
          have hpT : p.1.1 = T := hp
          refine ⟨p.1.2, hpT ▸ (hSb p).2, ?_⟩
          have hc : T ∈ Ts ∧ p.1.2 ∈ Y₁ T := hpT ▸ hSb p
          simp only [gT, dif_pos hc]
          congr 2
          exact Subtype.ext (Prod.ext hpT.symm rfl)
        · rintro ⟨c₁, hc₁, rfl⟩
          have hc : T ∈ Ts ∧ c₁ ∈ Y₁ T := ⟨hT, hc₁⟩
          refine ⟨g₂ ⟨(T, c₁), mem_pairSet.2 hc⟩, ⟨⟨(T, c₁), mem_pairSet.2 hc⟩, rfl, rfl⟩, ?_⟩
          simp only [gT, dif_pos hc]
      rw [hYimg, image_empty] at hrel
      have hpre := IsChainRefiner.prepend_relabel hres₁ hYR hC (gT T) (hgT_inj T)
        (hgT_ends T) hrel (fun c hc x hx => by
          obtain ⟨c₂, hc₂, rfl⟩ := mem_image.1 hc
          by_cases hx' : T ∈ Ts ∧ x ∈ Y₁ T
          · simp only [gT, dif_pos hx', Sum.inr.injEq] at hx
            exact hR₂f c₂ hc₂ _ hx
          · simp only [gT, dif_neg hx', reduceCtorEq] at hx)
      rw [hfib] at hpre
      simp only [if_pos hT']
      simp only [if_pos hT'] at hfresh hZo
      exact ⟨hfresh, hpre, hZo⟩
    · have hY0 : Y₁ T = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro c hc
        exact hT' (mem_image.2 ⟨⟨(T, c), mem_pairSet.2 ⟨hT, hc⟩⟩, mem_univ _, rfl⟩)
      have hch := (IsChainRefiner.ofResidual hres₁ hYR).mono' hC hC hC
      rw [hY0] at hch
      have hrel := hch.relabel (gT T) (ends₃ T) (fun c _ => hgT_ends T c) (hgT_inj T)
      rw [hfib, image_empty] at hrel
      simp only [if_neg hT', union_empty]
      simp only [if_neg hT', union_empty] at hfresh hZo
      exact ⟨hfresh, hrel, hZo⟩
  · -- lifted degrees
    have hsplit : ∀ T ∈ Ts, mdeg (fun c => T ∪ ends₃ T c)
        ((R₁ T).image (gT T) ∪ (if T ∈ Ts₁ then (R₂ T).image Sum.inr else ∅)) S ≤
        mdeg (fun c => T ∪ ends₁ T c) (R₁ T) S +
          (if T ∈ Ts₁ then mdeg (fun c => T ∪ ends₂ T c) (R₂ T) S else 0) := by
      intro T _
      refine (RefinedAbsorption.Dense.mdeg_union_le _ _ _ S).trans
        (Nat.add_le_add (le_of_eq ?_) (le_of_eq ?_))
      · exact mdeg_image_eq (A := R₁ T) (ends := fun c => T ∪ ends₁ T c)
          (ends' := fun c => T ∪ ends₃ T c) (g := gT T)
          (fun c _ => by simp only [hgT_ends]) (hgT_inj T).injOn subset_rfl S
      · split_ifs
        · exact mdeg_image_eq (A := R₂ T) (ends := fun c => T ∪ ends₂ T c)
            (ends' := fun c => T ∪ ends₃ T c) (g := Sum.inr) (fun c _ => rfl)
            Sum.inr_injective.injOn subset_rfl S
        · simp [mdeg]
    refine (sum_le_sum hsplit).trans ?_
    rw [sum_add_distrib, sum_ite_mem, inter_eq_right.2 h5]
    refine Nat.add_le_add (hdeg₁ S hS) ?_
    split_ifs with hcond
    · exact hdeg₂ S hS
    · refine le_of_eq (sum_eq_zero fun T hT => ?_)
      unfold mdeg
      rw [card_eq_zero, filter_eq_empty_iff]
      intro c hc hSc
      obtain ⟨-, -, hR₂Z⟩ := hT₂ T hT
      exact hcond (lift_meet_sub (hTsZ T (h5 hT)) (by rw [hTsc T (h5 hT), hS]; omega)
        (hR₂Z c hc) hZ₁ hSc)
  · -- lifted piece degrees
    have hsplit : ∀ T ∈ Ts, pdeg (fun c => T ∪ ends₃ T c)
        ((𝒲₁ T).image (image (gT T)) ∪
          (if T ∈ Ts₁ then (𝒲₂ T).image (image Sum.inr) else ∅)) S ≤
        pdeg (fun c => T ∪ ends₁ T c) (𝒲₁ T) S +
          (if T ∈ Ts₁ then pdeg (fun c => T ∪ ends₂ T c) (𝒲₂ T) S else 0) := by
      intro T _
      refine (pdeg_union_le _ _ _ S).trans (Nat.add_le_add ?_ ?_)
      · exact pdeg_image_le (gT T) (fun c => by simp only [hgT_ends]) _ S
      · split_ifs
        · exact pdeg_image_le Sum.inr (fun c => rfl) _ S
        · simp [pdeg]
    refine (sum_le_sum hsplit).trans ?_
    rw [sum_add_distrib, sum_ite_mem, inter_eq_right.2 h5]
    refine Nat.add_le_add (hpd₁ S hS) ?_
    split_ifs with hcond
    · exact hpd₂ S hS
    · refine le_of_eq (sum_eq_zero fun T hT => ?_)
      unfold pdeg
      rw [card_eq_zero, filter_eq_empty_iff]
      intro W hW hSW
      obtain ⟨-, hch₂, -⟩ := hT₂ T hT
      have hspan : W.biUnion (ends₂ T) ⊆ Z₁ := by
        refine biUnion_subset.2 fun c hc => ?_
        rcases mem_union.1 (hch₂.base.subset W hW hc) with hc | hc
        · obtain ⟨p, -, rfl⟩ := mem_image.1 hc
          rw [hends₂]; exact h2 p
        · obtain ⟨-, -, hR₂Z⟩ := hT₂ T hT
          exact hR₂Z c hc
      exact hcond (lift_meet_sub (hTsZ T (h5 hT)) (by rw [hTsc T (h5 hT), hS]; omega)
        hspan hZ₁ (hSW.trans (biUnion_lift_subset _ _ _)))

end Prepend

end RefinedAbsorption.LinkSpread
