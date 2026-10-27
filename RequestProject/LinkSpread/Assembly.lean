module
public import RequestProject.LinkSpread.Comp
public import RequestProject.FlatDown.LinkAccounting
public import RequestProject.Placement.ReserveLemma52
public import RequestProject.Dense.ExistenceE

/-!
# Link levels from tagged link refiners

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

`TaggedLinkRefinersE q r i` is the requirement of the open item, stated for tagged multigraphs:
refiners of the bodies of **all** fibres (link graphs) at once, inside the reserve `Z`, with the
`(r-1)`-degrees of the lifted new copies `T ∪ c` and of the lifted pieces, **summed over all tags
`T`**, bounded by `C_s · D + B · |Z| / 2^s`.  Unlike `PlacedLinkLevelE`, it asks for no density
bound on the pieces for sets `J` of every size: only for `(r-1)`-sets.

**`placedLinkLevelE_of_tagged`**: `TaggedLinkRefinersE q r i → PlacedLinkLevelE q r i`.  The
density bound on the pieces follows from the lifted piece degrees by root incidence (every nonempty
lifted piece spans at least `r` vertices of `U ∪ Z`).
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown

/-- Tagged multi-refiners: for every tag `T`, a multi-refiner (empty residue, constant `C`) of the
bodies of the fibre of `T`, with new copies inside `Z`, such that the lifted new copies and the
lifted pieces, summed over all tags, have `(r-1)`-degrees at most `Bd`. -/
def TaggedRefOutE (q r i C : ℕ) {n : ℕ} {E : Type} (tg bd : E → Finset (Fin n))
    (Z : Finset (Fin n)) (X : Finset E) (Bd : ℕ) : Prop :=
  ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : Finset (Fin n) → E' → Finset (Fin n))
    (R : Finset (Fin n) → Finset E') (𝒲 : Finset (Fin n) → Finset (Finset E')),
    Function.Injective g ∧ (∀ T c, ends' T (g c) = bd c) ∧
    (∀ T ∈ X.image tg, (∀ c ∈ R T, ∀ x, g x ≠ c) ∧
      IsMultiRefiner (q - i) (r - i) C (ends' T) ((fibre tg X T).image g) (R T) (𝒲 T) ∧
      ∀ c ∈ R T, ends' T c ⊆ Z) ∧
    (∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T ∈ X.image tg, mdeg (fun c => T ∪ ends' T c) (R T) S ≤ Bd) ∧
    ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T ∈ X.image tg, pdeg (fun c => T ∪ ends' T c) (𝒲 T) S ≤ Bd

/-- **Tagged link refiners at level `i`, `ε`-form.**  For every `K` there are a refinedness `Cl`
and an additive constant `B` such that for every precision `s`, every tagged multigraph (tags
`i`-sets outside `Z`, bodies `(r-i)`-sets inside `Z`, lifted copies inside `U`, `|U| ≤ K |Z|`)
whose lifted copies have `(r-1)`-degrees `≤ D` has tagged multi-refiners inside `Z` with budget
`Bd`, `2^s · Bd ≤ 2^s · Cg · D + B · |Z|`. -/
def TaggedLinkRefinersE (q r i : ℕ) : Prop :=
  ∀ K : ℕ, ∃ Cl B : ℕ, ∀ s : ℕ, ∃ Ch Cg : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E]
    (tg bd : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
    (∀ x, Disjoint (tg x) Z) → (∀ x, bd x ⊆ Z) → (∀ x ∈ X, (tg x).card = i) →
    (∀ x ∈ X, (bd x).card = r - i) → (∀ x ∈ X, liftEnds tg bd x ⊆ U) →
    U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → Ch ≤ Z.card →
    (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) →
    ∃ Bd : ℕ, 2 ^ s * Bd ≤ 2 ^ s * Cg * D + B * Z.card ∧ TaggedRefOutE q r i Cl tg bd Z X Bd

section Relabel

variable {E E' : Type} [DecidableEq E] [DecidableEq E']

open Classical in
/-- Sending the relabelled old copies back to `E` and the new copies to the right summand. -/
noncomputable def backLabel (g : E → E') (c : E') : E ⊕ E' :=
  if hc : ∃ x, g x = c then Sum.inl hc.choose else Sum.inr c

omit [DecidableEq E] [DecidableEq E'] in
theorem backLabel_g {g : E → E'} (hg : Function.Injective g) (x : E) :
    backLabel g (g x) = Sum.inl x := by
  have hc : ∃ y, g y = g x := ⟨x, rfl⟩
  unfold backLabel
  rw [dif_pos hc]
  exact congrArg Sum.inl (hg hc.choose_spec)

omit [DecidableEq E] [DecidableEq E'] in
theorem backLabel_new {g : E → E'} {c : E'} (hc : ∀ x, g x ≠ c) : backLabel g c = Sum.inr c := by
  unfold backLabel
  rw [dif_neg (fun ⟨x, hx⟩ => hc x hx)]

omit [DecidableEq E] [DecidableEq E'] in
theorem backLabel_injective {g : E → E'} : Function.Injective (backLabel g) := by
  intro c c' h
  unfold backLabel at h
  split_ifs at h with h1 h2 h2 <;>
    first
    | exact Sum.inr_injective h
    | exact absurd h Sum.inl_ne_inr
    | exact absurd h Sum.inr_ne_inl
    | rw [← h1.choose_spec, ← h2.choose_spec, Sum.inl_injective h]

end Relabel

/-- A nonempty union of sets each containing `T`. -/
theorem biUnion_union_left {V E : Type} [DecidableEq V] {W : Finset E} (hW : W.Nonempty)
    (T : Finset V) (f : E → Finset V) : W.biUnion (fun c => T ∪ f c) = T ∪ W.biUnion f := by
  obtain ⟨c₀, hc₀⟩ := hW
  ext v
  simp only [mem_biUnion, mem_union]
  constructor
  · rintro ⟨c, hc, hv | hv⟩
    · exact Or.inl hv
    · exact Or.inr ⟨c, hc, hv⟩
  · rintro (hv | ⟨c, hc, hv⟩)
    · exact ⟨c₀, hc₀, Or.inl hv⟩
    · exact ⟨c, hc, Or.inr hv⟩

/-- **Link levels from tagged link refiners.** -/
theorem placedLinkLevelE_of_tagged {q r i : ℕ} (h : TaggedLinkRefinersE q r i) :
    PlacedLinkLevelE q r i := by
  intro K
  obtain ⟨Cl, B, hT⟩ := h K
  refine ⟨Cl, B * (K + 1) ^ (r - 1), fun s => ?_⟩
  obtain ⟨Ch, Cg, hT'⟩ := hT s
  refine ⟨Ch, Cg * (K + 1) ^ (r - 1), Cg, ?_⟩
  intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 hCh hdeg
  set X' := X.filter fun x => (ends x \ Z).card = i with hX'def
  set tg : E → Finset (Fin n) := fun x => ends x \ Z with htgdef
  set bd : E → Finset (Fin n) := fun x => ends x ∩ Z with hbddef
  have hlift : liftEnds tg bd = ends := funext fun x => sdiff_union_inter _ _
  have hbdc : ∀ x ∈ X', (bd x).card = r - i := by
    intro x hx
    have h1 := card_sdiff_add_card_inter (ends x) Z
    have h2 := hXr x (mem_filter.1 hx).1
    have h3 := (mem_filter.1 hx).2
    simp only [hbddef]
    omega
  obtain ⟨Bd, hBd, E', _, g, ends', R, 𝒲, hg, hends, hfib, hdegR, hpdR⟩ :=
    hT' n tg bd Z U X' D (fun x => sdiff_disjoint) (fun x => inter_subset_right)
      (fun x hx => (mem_filter.1 hx).2) hbdc
      (fun x hx => by rw [hlift]; exact hU x (mem_filter.1 hx).1) hUK hZq hD1 hCh
      (fun S hS => by rw [hlift]; exact (mdeg_mono _ (filter_subset _ _) S).trans (hdeg S hS))
  have hout : outParts ends Z i X = X'.image tg := rfl
  have hlnk : ∀ T ∈ outParts ends Z i X, lnk ends Z X T = fibre tg X' T := by
    intro T hT
    have hTc := (outParts_card hT).1
    ext x
    simp only [lnk, fibre, hX'def, htgdef, mem_filter]
    constructor
    · rintro ⟨hx, he⟩; exact ⟨⟨hx, by rw [he, hTc]⟩, he⟩
    · rintro ⟨⟨hx, -⟩, he⟩; exact ⟨hx, he⟩
  -- ends of the old and new copies
  have hcompat : ∀ T ∈ outParts ends Z i X, ∀ c ∈ (fibre tg X' T).image g ∪ R T,
      lE ends Z ends' T (backLabel g c) = ends' T c := by
    intro T hT c hc
    rcases mem_union.1 hc with hc | hc
    · obtain ⟨x, -, rfl⟩ := mem_image.1 hc
      rw [backLabel_g hg, hends]
      rfl
    · rw [backLabel_new ((hfib T hT).1 c hc)]
      rfl
  have hrefT : ∀ T ∈ outParts ends Z i X,
      IsMultiRefiner (q - i) (r - i) Cl (lE ends Z ends' T) ((lnk ends Z X T).image Sum.inl)
        ((R T).image Sum.inr) ((𝒲 T).image (image (backLabel g))) := by
    intro T hT
    obtain ⟨hRg, href, -⟩ := hfib T hT
    have hrel := residual_relabel href (backLabel g) (lE ends Z ends' T) (hcompat T hT)
      backLabel_injective.injOn (empty_subset _)
    rw [image_empty, image_image] at hrel
    have e1 : (fibre tg X' T).image (backLabel g ∘ g) = (lnk ends Z X T).image Sum.inl := by
      rw [hlnk T hT]
      exact image_congr fun x _ => backLabel_g hg x
    have e2 : (R T).image (backLabel g) = (R T).image Sum.inr :=
      image_congr fun c hc => backLabel_new (hRg c hc)
    rw [e1, e2] at hrel
    exact hrel
  have hLR : LinkRefiners q r i Cl ends Z X ends' R fun T => (𝒲 T).image (image (backLabel g)) :=
    ⟨hrefT, fun T hT => (hfib T hT).2.2⟩
  refine ⟨E', inferInstance, ends', R, _, hLR.filter_nonempty, fun J hJ => ?_, fun S hS => ?_⟩
  · -- density of the pieces, by root incidence
    set Ts := X'.image tg with hTs
    set I := Ts.sigma fun T => (𝒲 T).filter Finset.Nonempty with hI
    set Rt : (Σ _ : Finset (Fin n), Finset E') → Finset (Fin n) :=
      fun p => p.1 ∪ p.2.biUnion (ends' p.1) with hRt
    have hsigma : ∀ P : (Σ _ : Finset (Fin n), Finset E') → Prop, ∀ [DecidablePred P],
        (I.filter P).card = ∑ T ∈ Ts, (((𝒲 T).filter Finset.Nonempty).filter
          fun W => P ⟨T, W⟩).card := by
      intro P _
      rw [← card_sigma]
      congr 1
      ext ⟨T, W⟩
      simp [hI, mem_sigma, mem_filter, and_assoc]
    have hWsub : ∀ T ∈ Ts, ∀ W ∈ 𝒲 T, W ⊆ (fibre tg X' T).image g ∪ R T :=
      fun T hT W hW => (hfib T hT).2.1.subset W hW
    have hcZ : ∀ T ∈ Ts, ∀ c ∈ (fibre tg X' T).image g ∪ R T, ends' T c ⊆ Z := by
      intro T hT c hc
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨x, -, rfl⟩ := mem_image.1 hc
        rw [hends]; exact inter_subset_right
      · exact (hfib T hT).2.2 c hc
    have hRU : ∀ p ∈ I, Rt p ⊆ U ∪ Z := by
      rintro ⟨T, W⟩ hp
      rw [mem_sigma, mem_filter] at hp
      refine union_subset ?_ ?_
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hp.1
        exact (sdiff_subset.trans (hU x (mem_filter.1 hx).1)).trans subset_union_left
      · refine biUnion_subset.2 fun c hc => ?_
        exact (hcZ T hp.1 c (hWsub T hp.1 W hp.2.1 hc)).trans subset_union_right
    have hRc : ∀ p ∈ I, r - 1 ≤ (Rt p).card := by
      rintro ⟨T, W⟩ hp
      rw [mem_sigma, mem_filter] at hp
      obtain ⟨c, hc⟩ := hp.2.2
      have hcm := hWsub T hp.1 W hp.2.1 hc
      have hcard := (hfib T hp.1).2.1.rgraph c hcm
      have hTc := (outParts_card (hout ▸ hp.1)).1
      have hdisj : Disjoint T (ends' T c) :=
        disjoint_of_subset_right (hcZ T hp.1 c hcm) (outParts_card (hout ▸ hp.1)).2
      have hsub : T ∪ ends' T c ⊆ Rt ⟨T, W⟩ :=
        union_subset_union subset_rfl (subset_biUnion_of_mem _ hc)
      have := card_le_card hsub
      rw [card_union_of_disjoint hdisj, hTc, hcard] at this
      omega
    have hDeg : ∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun p => S ⊆ Rt p).card ≤ Bd := by
      intro S hS
      rw [hsigma]
      refine le_trans (sum_le_sum fun T _ => ?_) (hpdR S hS)
      refine card_le_card fun W hW => ?_
      simp only [mem_filter] at hW ⊢
      refine ⟨hW.1.1, ?_⟩
      rw [biUnion_union_left hW.1.2]
      exact hW.2
    have hinc := rootIncidence_of_subset I Rt (U ∪ Z) Bd hRU hRc hDeg J hJ
    rw [hsigma] at hinc
    have hle : ∑ T ∈ (outParts ends Z i X).filter (fun T => J \ Z ⊆ T),
        ((((𝒲 T).image (image (backLabel g))).filter Finset.Nonempty).filter
          fun W => J ∩ Z ⊆ W.biUnion (lE ends Z ends' T)).card ≤
        ∑ T ∈ Ts, (((𝒲 T).filter Finset.Nonempty).filter
          fun W => J ⊆ Rt ⟨T, W⟩).card := by
      rw [← hout]
      refine le_trans (sum_le_sum fun T hT => ?_) (sum_le_sum_of_subset (filter_subset _ _))
      obtain ⟨hT, hJT⟩ := mem_filter.1 hT
      rw [filter_filter, filter_image]
      refine card_image_le.trans (card_le_card fun W hW => ?_)
      simp only [mem_filter] at hW ⊢
      obtain ⟨hW, hne, hJW⟩ := hW
      refine ⟨⟨hW, ?_⟩, ?_⟩
      · obtain ⟨c, hc⟩ := hne
        obtain ⟨c', hc', -⟩ := mem_image.1 hc
        exact ⟨c', hc'⟩
      · have hspan : (W.image (backLabel g)).biUnion (lE ends Z ends' T) = W.biUnion (ends' T) := by
          rw [image_biUnion]
          exact biUnion_congr rfl fun c hc => hcompat T hT c (hWsub T (hout ▸ hT) W hW hc)
        rw [hspan] at hJW
        intro v hv
        by_cases hvZ : v ∈ Z
        · exact mem_union_right _ (hJW (mem_inter.2 ⟨hv, hvZ⟩))
        · exact mem_union_left _ (hJT (mem_sdiff.2 ⟨hv, hvZ⟩))
    have hUZ : (U ∪ Z).card ^ (r - 1 - J.card) ≤ (K + 1) ^ (r - 1) * Z.card ^ (r - 1 - J.card) := by
      calc (U ∪ Z).card ^ (r - 1 - J.card) ≤ ((K + 1) * Z.card) ^ (r - 1 - J.card) :=
            Nat.pow_le_pow_left ((card_union_le U Z).trans (by nlinarith)) _
        _ = (K + 1) ^ (r - 1 - J.card) * Z.card ^ (r - 1 - J.card) := mul_pow _ _ _
        _ ≤ (K + 1) ^ (r - 1) * Z.card ^ (r - 1 - J.card) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
    calc 2 ^ s * ∑ T ∈ (outParts ends Z i X).filter (fun T => J \ Z ⊆ T),
          ((((𝒲 T).image (image (backLabel g))).filter Finset.Nonempty).filter
            fun W => J ∩ Z ⊆ W.biUnion (lE ends Z ends' T)).card
        ≤ 2 ^ s * (Bd * ((K + 1) ^ (r - 1) * Z.card ^ (r - 1 - J.card))) :=
          Nat.mul_le_mul_left _ ((hle.trans hinc).trans (Nat.mul_le_mul_left _ hUZ))
      _ = (2 ^ s * Bd) * (K + 1) ^ (r - 1) * Z.card ^ (r - 1 - J.card) := by ring
      _ ≤ (2 ^ s * Cg * D + B * Z.card) * (K + 1) ^ (r - 1) * Z.card ^ (r - 1 - J.card) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hBd)
      _ = (2 ^ s * (Cg * (K + 1) ^ (r - 1)) * D + B * (K + 1) ^ (r - 1) * Z.card) *
            Z.card ^ (r - 1 - J.card) := by ring
  · -- the link degrees
    have hsum : ∑ T ∈ (outParts ends Z i X).filter (fun T => S \ Z ⊆ T),
        mdeg (ends' T) (R T) (S ∩ Z) ≤ Bd := by
      refine le_trans ?_ (hdegR S hS)
      rw [← hout]
      refine le_trans (sum_le_sum fun T hT => ?_) (sum_le_sum_of_subset (filter_subset _ _))
      have hST := (mem_filter.1 hT).2
      refine card_le_card fun c hc => ?_
      simp only [mem_filter] at hc ⊢
      refine ⟨hc.1, fun v hv => ?_⟩
      replace hc := hc.2
      by_cases hvZ : v ∈ Z
      · exact mem_union_right _ (hc (mem_inter.2 ⟨hv, hvZ⟩))
      · exact mem_union_left _ (hST (mem_sdiff.2 ⟨hv, hvZ⟩))
    have hB : B * Z.card ≤ B * (K + 1) ^ (r - 1) * Z.card :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by positivity))
    exact (Nat.mul_le_mul_left _ hsum).trans (hBd.trans (Nat.add_le_add_left hB _))

/-- The Existence Conjecture for `r = 3` from tagged link refiners at level `1`. -/
theorem steinerExistenceFor_three_of_tagged {q : ℕ} (hq : 3 < q)
    (hL : TaggedLinkRefinersE q 3 1) : RefinedAbsorption.Dense.SteinerExistenceFor q 3 :=
  RefinedAbsorption.Dense.steinerExistenceFor_threeE hq (placedLinkLevelE_of_tagged hL)

/-- The Existence Conjecture from tagged link refiners at the intermediate levels. -/
theorem steinerExistence_of_tagged
    (h : ∀ q r i : ℕ, 3 ≤ r → r < q → 1 ≤ i → i < r - 1 → TaggedLinkRefinersE q r i) :
    SteinerExistenceConjecture :=
  RefinedAbsorption.Dense.steinerExistence_of_levelsE fun q r i hr hrq hi hir =>
    placedLinkLevelE_of_tagged (h q r i hr hrq hi hir)

end RefinedAbsorption.LinkSpread
