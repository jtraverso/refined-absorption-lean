module
public import RequestProject.Local.TaggedA

/-!
# Sparse link levels and the sparse chain of flat levels

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, §4), with the hypothesis
`Δ ≤ n / C` of Theorems 3.7 and 3.8.  Lean formalization: Juan Pablo Traverso Gianini,
Apache-2.0.

The *sparse* versions of the link levels only require their conclusion when the degree parameter
`D` is small compared with the reserve: `Ch · D ≤ |Z|` (in place of `Ch ≤ |Z|`).

* `PlacedLinkLevelS`, `TaggedLinkRefinersS`: the sparse forms of `PlacedLinkLevelA` and
  `TaggedLinkRefinersA`; `PlacedLinkLevelA.toS`, `PlacedLinkLevel.toS`.
* `placedLinkLevelS_of_taggedS`: as `placedLinkLevelA_of_taggedA` (same proof).
* `placedStep_of_levelS`, `placedChainS`: as `placedStep_of_level` and `placedChain`, with the
  hypothesis `Cs · D ≤ |Z|`.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown

/-- **Sparse placed link refiners at level `i`**: `PlacedLinkLevelA` with the hypothesis
`Ch · D ≤ |Z|` in place of `Ch ≤ |Z|`. -/
def PlacedLinkLevelS (q r i : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ K : ℕ, ∃ Cl Ch Cd Cg : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
    (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
    MIsRGraph r ends X → IsFlat i Z ends X → (∀ x ∈ X, ends x ⊆ U) →
    U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → a Z.card ≤ D → Ch * D ≤ Z.card →
    (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
    ∃ (N : Type) (_ : DecidableEq N) (endsN : Finset (Fin n) → N → Finset (Fin n))
      (RN : Finset (Fin n) → Finset N) (𝒲 : Finset (Fin n) → Finset (Finset (E ⊕ N))),
      LinkRefiners q r i Cl ends Z X endsN RN 𝒲 ∧
      (∀ J : Finset (Fin n), J.card ≤ r - 1 →
        ∑ T ∈ (outParts ends Z i X).filter (fun T => J \ Z ⊆ T),
          ((𝒲 T).filter fun W => J ∩ Z ⊆ W.biUnion (lE ends Z endsN T)).card ≤
          Cd * D * Z.card ^ (r - 1 - J.card)) ∧
      ∀ S : Finset (Fin n), S.card = r - 1 →
        ∑ T ∈ (outParts ends Z i X).filter (fun T => S \ Z ⊆ T),
          mdeg (endsN T) (RN T) (S ∩ Z) ≤ Cg * D

theorem PlacedLinkLevelA.toS {q r i : ℕ} {a : ℕ → ℕ} (h : PlacedLinkLevelA q r i a) :
    PlacedLinkLevelS q r i a := by
  intro K
  obtain ⟨Cl, Ch, Cd, Cg, hlev⟩ := h K
  exact ⟨Cl, Ch, Cd, Cg, fun n E _ ends Z U X D hXr hX hU hUK hZq hD1 haD hCh hdeg =>
    hlev n ends Z U X D hXr hX hU hUK hZq hD1 haD
      (le_trans (Nat.le_mul_of_pos_right _ hD1) hCh) hdeg⟩

theorem PlacedLinkLevel.toS {q r i : ℕ} (h : PlacedLinkLevel q r i) (a : ℕ → ℕ) :
    PlacedLinkLevelS q r i a :=
  (h.toA a).toS

/-- **A degree-controlled flat step from a placed level.** -/
theorem placedStep_of_levelS {q r i : ℕ} {a : ℕ → ℕ} (hir : i < r) (hrq : r < q)
    (hL : PlacedLinkLevelS q r i a) (K : ℕ) :
    ∃ Cs C : ℕ, 0 < Cs ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → IsFlat i Z ends X → (∀ x ∈ X, ends x ⊆ U) →
      U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → a Z.card ≤ D → Cs * D ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      PlacedOut q r (i - 1) C ends Z U X D := by
  obtain ⟨Cl, Ch, Cd, Cg, hlev⟩ := hL K
  obtain ⟨Cs₀, Cs', -, hflat⟩ := placedFlatStep_link q r i Cl hir hrq
  refine ⟨Ch + Cs₀ + 1, flatConst q r Cl + Cg + Cs' * Cd, by omega, ?_⟩
  intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 haD hCD hdeg
  have hCh : Ch * D ≤ Z.card := le_trans (Nat.mul_le_mul_right _ (by omega)) hCD
  have hCs : Cs₀ ≤ Z.card :=
    le_trans (by omega) (le_trans (Nat.le_mul_of_pos_right _ hD1) hCD)
  obtain ⟨N, _, endsN, RN, 𝒲, hLR, hdens, hdegL⟩ :=
    hlev n ends Z U X D hXr hX hU hUK hZq hD1 haD hCh hdeg
  obtain ⟨R, Y, 𝒲', h1, h2, -, h4, h5, h6, h7, h8⟩ :=
    hflat n ends Z endsN X RN 𝒲 (Cd * D) hXr hX hLR hZq hCs hdens
  refine ⟨E ⊕ FLab (Fin n) E N, inferInstance, Sum.inl, fEnds ends endsN, R, Y, 𝒲',
    Sum.inl_injective, fun c => rfl, fun c hc x hx => h5 c hc x hx.symm,
    h1.mono (by omega), h2, h4, fun c hc => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · obtain ⟨T, hT, hcT⟩ := h6 c hc
    exact hcT.trans (union_subset_union (outParts_subset hU hT) subset_rfl)
  · refine (h7 S hS).trans ?_
    have := hdegL S hS
    calc _ ≤ Cg * D + Cs' * (Cd * D) := Nat.add_le_add_right this _
      _ ≤ (flatConst q r Cl + Cg + Cs' * Cd) * D := by nlinarith
  · refine (h8 S hS).trans ?_
    calc Cs' * (Cd * D) = (Cs' * Cd) * D := by ring
      _ ≤ (flatConst q r Cl + Cg + Cs' * Cd) * D := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- **Chaining the levels** `j, j - 1, …, 1`, given placed link refiners at each of them. -/
theorem placedChainS {q r : ℕ} {a : ℕ → ℕ} (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelS q r i a) :
    ∀ j, j < r → ∀ K : ℕ, ∃ Cs C : ℕ, 0 < Cs ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E]
      (ends : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → IsFlat j Z ends X → (∀ x ∈ X, ends x ⊆ U) →
      U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → a Z.card ≤ D → Cs * D ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      PlacedOut q r 0 C ends Z U X D := by
  intro j
  induction j with
  | zero =>
    intro _ K
    refine ⟨1, 1, one_pos, ?_⟩
    intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 _ hCD hdeg
    refine ⟨E, inferInstance, id, ends, ∅, X, ∅, Function.injective_id, fun c => rfl,
      by simp, ?_, hX, by simp, by simp, fun S _ => by simp [mdeg], fun S _ => by simp [pdeg]⟩
    rw [image_id]
    exact isResidualMultiRefiner_self 1 hXr
  | succ j ih =>
    intro hj K
    obtain ⟨Cs₁, C₁, hCs₁, hstep⟩ :=
      placedStep_of_levelS hj hrq (hL (j + 1) (by omega) hj) K
    obtain ⟨Cs₂, C₂, -, hrest⟩ := ih (by omega) (K + 1)
    refine ⟨Cs₁ + Cs₂ * (1 + C₁), C₁ + C₂ + C₂ * (1 + C₁), by omega, ?_⟩
    intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 haD hCD hdeg
    have hCD₁ : Cs₁ * D ≤ Z.card := le_trans (Nat.mul_le_mul_right _ (by omega)) hCD
    obtain ⟨E₁, _, g, ends₁, R₁, Y₁, 𝒲₁, hg, hends, hR₁, h₁, hflat₁, hY₁, hR₁U, hdeg₁, hpd₁⟩ :=
      hstep n ends Z U X D hXr hX hU hUK hZq hD1 haD hCD₁ hdeg
    rw [Nat.add_sub_cancel] at hflat₁
    have hYr : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (hY₁ hc)
    have hYU : ∀ c ∈ Y₁, ends₁ c ⊆ U ∪ Z := by
      intro c hc
      rcases mem_union.1 (hY₁ hc) with hc | hc
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
        rw [hends]; exact (hU x hx).trans subset_union_left
      · exact hR₁U c hc
    have hUK' : (U ∪ Z).card ≤ (K + 1) * Z.card := by
      have := card_union_le U Z
      nlinarith
    have hD₁ : 1 ≤ (1 + C₁) * D := by nlinarith
    have hCD₂ : Cs₂ * ((1 + C₁) * D) ≤ Z.card := by
      rw [← mul_assoc]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hCD
    have hdegY : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ (1 + C₁) * D := by
      intro S hS
      calc mdeg ends₁ Y₁ S ≤ mdeg ends₁ (X.image g ∪ R₁) S := mdeg_mono _ hY₁ S
        _ ≤ mdeg ends₁ (X.image g) S + mdeg ends₁ R₁ S := by
          unfold mdeg; rw [filter_union]; exact card_union_le _ _
        _ ≤ D + C₁ * D := by
          rw [mdeg_image_eq (A := X) (fun c _ => hends c) hg.injOn subset_rfl]
          exact Nat.add_le_add (hdeg S hS) (hdeg₁ S hS)
        _ = (1 + C₁) * D := by ring
    obtain ⟨E₂, _, g₂, ends₂, R₂, Y₂, 𝒲₂, hg₂, hends₂, hR₂, h₂, hflat₂, hY₂, hR₂U,
      hdeg₂, hpd₂⟩ := hrest n ends₁ Z (U ∪ Z) Y₁ ((1 + C₁) * D) hYr hflat₁ hYU hUK' hZq hD₁
        (haD.trans (by nlinarith)) hCD₂ hdegY
    have h₁' := residual_relabel h₁ g₂ ends₂ (fun c _ => hends₂ c) hg₂.injOn hY₁
    have hcomp := h₁'.trans h₂ (by rw [← image_union]; exact image_subset_image hY₁) (by
      rw [disjoint_left]
      intro c hc hc'
      rw [← image_union] at hc'
      obtain ⟨x, -, rfl⟩ := mem_image.1 hc'
      exact hR₂ _ hc x rfl)
    refine ⟨E₂, inferInstance, g₂ ∘ g, ends₂, R₁.image g₂ ∪ R₂, Y₂, 𝒲₁.image (image g₂) ∪ 𝒲₂,
      hg₂.comp hg, fun c => by simp [hends₂, hends], ?_, ?_, hflat₂, ?_, ?_, ?_, ?_⟩
    · intro c hc x hx
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        exact hR₁ c₁ hc₁ x (hg₂ hx)
      · exact hR₂ c hc _ hx
    · rw [← image_image]
      exact hcomp.mono (by nlinarith)
    · intro c hc
      rcases mem_union.1 (hY₂ hc) with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        rcases mem_union.1 (hY₁ hc₁) with h | h
        · obtain ⟨x, hx, rfl⟩ := mem_image.1 h
          exact mem_union_left _ (mem_image.2 ⟨x, hx, rfl⟩)
        · exact mem_union_right _ (mem_union_left _ (mem_image_of_mem _ h))
      · exact mem_union_right _ (mem_union_right _ hc)
    · intro c hc
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
        rw [hends₂]; exact hR₁U c₁ hc₁
      · refine (hR₂U c hc).trans ?_
        rw [union_assoc, union_self]
    · intro S hS
      calc mdeg ends₂ (R₁.image g₂ ∪ R₂) S ≤ mdeg ends₂ (R₁.image g₂) S + mdeg ends₂ R₂ S := by
            unfold mdeg; rw [filter_union]; exact card_union_le _ _
        _ ≤ C₁ * D + C₂ * ((1 + C₁) * D) := by
          rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
          exact Nat.add_le_add (hdeg₁ S hS) (hdeg₂ S hS)
        _ ≤ (C₁ + C₂ + C₂ * (1 + C₁)) * D := by nlinarith
    · intro S hS
      calc pdeg ends₂ (𝒲₁.image (image g₂) ∪ 𝒲₂) S
          ≤ pdeg ends₂ (𝒲₁.image (image g₂)) S + pdeg ends₂ 𝒲₂ S := pdeg_union_le _ _ _ _
        _ ≤ C₁ * D + C₂ * ((1 + C₁) * D) :=
          Nat.add_le_add ((pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)) (hpd₂ S hS)
        _ ≤ (C₁ + C₂ + C₂ * (1 + C₁)) * D := by nlinarith

end RefinedAbsorption.Placement

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown

/-- **Sparse tagged link refiners at level `i`**: `TaggedLinkRefinersA` with the hypothesis
`Ch · D ≤ |Z|` in place of `Ch ≤ |Z|`. -/
def TaggedLinkRefinersS (q r i : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ K : ℕ, ∃ Cl Ch Cg : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E]
    (tg bd : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
    (∀ x, Disjoint (tg x) Z) → (∀ x, bd x ⊆ Z) → (∀ x ∈ X, (tg x).card = i) →
    (∀ x ∈ X, (bd x).card = r - i) → (∀ x ∈ X, liftEnds tg bd x ⊆ U) →
    U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → a Z.card ≤ D → Ch * D ≤ Z.card →
    (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) →
    ∃ Bd : ℕ, Bd ≤ Cg * D ∧ TaggedRefOutE q r i Cl tg bd Z X Bd

/-- **Sparse link levels from sparse tagged link refiners.** -/
theorem placedLinkLevelS_of_taggedS {q r i : ℕ} {a : ℕ → ℕ} (h : TaggedLinkRefinersS q r i a) :
    PlacedLinkLevelS q r i a := by
  intro K
  obtain ⟨Cl, Ch, Cg, hT'⟩ := h K
  refine ⟨Cl, Ch, Cg * (K + 1) ^ (r - 1), Cg, ?_⟩
  intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 haD hCh hdeg
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
      (fun x hx => by rw [hlift]; exact hU x (mem_filter.1 hx).1) hUK hZq hD1 haD hCh
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
    calc ∑ T ∈ (outParts ends Z i X).filter (fun T => J \ Z ⊆ T),
          ((((𝒲 T).image (image (backLabel g))).filter Finset.Nonempty).filter
            fun W => J ∩ Z ⊆ W.biUnion (lE ends Z ends' T)).card
        ≤ Bd * ((K + 1) ^ (r - 1) * Z.card ^ (r - 1 - J.card)) :=
          (hle.trans hinc).trans (Nat.mul_le_mul_left _ hUZ)
      _ ≤ (Cg * D) * ((K + 1) ^ (r - 1) * Z.card ^ (r - 1 - J.card)) :=
          Nat.mul_le_mul_right _ hBd
      _ = Cg * (K + 1) ^ (r - 1) * D * Z.card ^ (r - 1 - J.card) := by ring
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
    exact hsum.trans hBd

end RefinedAbsorption.LinkSpread
