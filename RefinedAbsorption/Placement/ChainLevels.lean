module
public import RefinedAbsorption.Placement.LastFlat
public import RefinedAbsorption.RefineDown.ReserveRound

/-!
# Chaining the flat levels in `Fin n`

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, the flat steps).
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

`PlacedLinkLevel q r i` packages what `placedFlatStep_link` needs at level `i`: for every
`i`-flat `r`-multigraph `X` on `Fin n` whose copies lie in a set `U` with `|U| ≤ K |Z|` and whose
`(r-1)`-degrees are `≤ D`, link refiners (of uniformity `r - i`) inside the reserve `Z`, with

* pieces of density `≤ Cd · D · |Z|^(r-1-|J|)` (the density hypothesis of `placedFlatStep_link`);
* `∑_{T ⊇ S \ Z} mdeg(RN T, S ∩ Z) ≤ Cg · D` for every `(r-1)`-set `S` (this single sum covers
  both the `(r-i-1)`-degrees, `|S \ Z| = i`, and the spread multiplicities of `(r-i)`-sets,
  `|S \ Z| = i - 1`).

`placedLinkLevel_last` proves it for `i = r - 1` (spread chain refiners).  `placedStep_of_level`
turns a level into a degree-controlled flat step, and `placedChain` chains the levels
`j, j-1, …, 1`: from a `j`-flat multigraph to a residue inside the reserve, with new copies of
`(r-1)`-degree `≤ C · D`.  For `r = 2` the only level is `1 = r - 1`, so `placedChain_two` is
unconditional.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown

/-- **Placed link refiners at level `i`** (see the module docstring). -/
def PlacedLinkLevel (q r i : ℕ) : Prop :=
  ∀ K : ℕ, ∃ Cl Ch Cd Cg : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
    (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
    MIsRGraph r ends X → IsFlat i Z ends X → (∀ x ∈ X, ends x ⊆ U) →
    U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → Ch ≤ Z.card →
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

/-- **Placed link refiners at level `i`, with an additive term.**  As `PlacedLinkLevel`, but the
link refiners are only required for degree parameters `D ≥ a |Z|`.  Equivalently, the bounds may
carry an additive term `a |Z|`: `Cg · (D + a |Z|)` in place of `Cg · D` (apply the definition with
`D + a |Z|`).  For `a = 0` this is `PlacedLinkLevel`; for a sublinear `a` (e.g.
`a m ≈ m^{1-1/(r-i)} log m`, the additive term of the Refine Down Lemma in uniformity `r - i`) the
construction still yields an `o(n)` budget (`nativeWeakStrongMultiRefiners_of_levelsA`). -/
def PlacedLinkLevelA (q r i : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ K : ℕ, ∃ Cl Ch Cd Cg : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
    (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
    MIsRGraph r ends X → IsFlat i Z ends X → (∀ x ∈ X, ends x ⊆ U) →
    U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → a Z.card ≤ D → Ch ≤ Z.card →
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

theorem PlacedLinkLevel.toA {q r i : ℕ} (h : PlacedLinkLevel q r i) (a : ℕ → ℕ) :
    PlacedLinkLevelA q r i a := by
  intro K
  obtain ⟨Cl, Ch, Cd, Cg, hlev⟩ := h K
  exact ⟨Cl, Ch, Cd, Cg, fun n E _ ends Z U X D hXr hX hU hUK hZq hD1 _ hCh hdeg =>
    hlev n ends Z U X D hXr hX hU hUK hZq hD1 hCh hdeg⟩

/-- Conclusion of a degree-controlled step (or chain of steps) from `X`: after an injective
relabelling `g` of the copies, a residual refiner with residue `Y`, all new copies inside
`U ∪ Z`, residue `j`-flat and new `(r-1)`-degrees `≤ C · D`. -/
def PlacedOut (q r j C : ℕ) {n : ℕ} {E : Type} (ends : E → Finset (Fin n))
    (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ) : Prop :=
  ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
    (R Y : Finset E') (𝒲 : Finset (Finset E')),
    Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
    IsResidualMultiRefiner q r C ends' (X.image g) R Y 𝒲 ∧ IsFlat j Z ends' Y ∧
    Y ⊆ X.image g ∪ R ∧ (∀ c ∈ R, ends' c ⊆ U ∪ Z) ∧
    (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ C * D) ∧
    ∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤ C * D

theorem outParts_subset {n : ℕ} {E : Type} [DecidableEq E] {ends : E → Finset (Fin n)}
    {Z U : Finset (Fin n)} {X : Finset E} {i : ℕ} (hU : ∀ x ∈ X, ends x ⊆ U)
    {T : Finset (Fin n)} (hT : T ∈ outParts ends Z i X) : T ⊆ U := by
  unfold outParts at hT
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hT
  exact sdiff_subset.trans (hU x (mem_filter.1 hx).1)

/-- **The last level** `i = r - 1`: spread chain refiners. -/
theorem placedLinkLevel_last (q r : ℕ) (hr : 2 ≤ r) (hrq : r < q) :
    PlacedLinkLevel q r (r - 1) := by
  intro K
  set q' := q - (r - 1) with hq'
  set capC := 3 * 2 ^ (r - 1) * (3 + 2 * K) + 1 with hcapC
  set Cd := (4 * q' + 1) * (2 + 2 * capC) * (K + 1) ^ (r - 1) with hCd
  refine ⟨4 * q' + 1, 0, Cd, 4 * (q' - 1) + (q' - 1) * (1 + 3 * capC), ?_⟩
  intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 _ hdeg
  have hZ0 : 0 < Z.card := by omega
  obtain ⟨v₀, -⟩ := card_pos.1 hZ0
  have hcap : lfCap r K D ≤ capC * D := by
    have e : lfCap r K D = (3 * 2 ^ (r - 1) * (3 + 2 * K)) * D + 1 := by unfold lfCap; ring
    have e2 : capC * D = (3 * 2 ^ (r - 1) * (3 + 2 * K)) * D + D := by rw [hcapC]; ring
    omega
  have hpow : ∀ e ≤ r - 1, U.card ^ e ≤ (K + 1) ^ (r - 1) * Z.card ^ e := by
    intro e he
    calc U.card ^ e ≤ ((K + 1) * Z.card) ^ e :=
          Nat.pow_le_pow_left (hUK.trans (Nat.mul_le_mul_right _ (by omega))) _
      _ = (K + 1) ^ e * Z.card ^ e := mul_pow _ _ _
      _ ≤ (K + 1) ^ (r - 1) * Z.card ^ e :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) he)
  by_cases hXne : X.Nonempty
  · obtain ⟨e₀, -⟩ := hXne
    obtain ⟨σ, hσZ, hload⟩ := lf_pivots (e₀ := e₀) (v₀ := v₀) hXr hr hU hUK hZ0 hdeg
    refine ⟨ChainRefiner.Lab, inferInstance, lfEndsN ends Z X e₀ v₀ σ, lfRN ends Z X q', lfW ends Z X e₀ q',
      lf_linkRefiners hXr hr hrq hσZ, fun J hJ => ?_, fun S hS => ?_⟩
    · refine (lf_density hXr hr hU hdeg hload J hJ).trans ?_
      have h2D : 2 * D + 2 * lfCap r K D ≤ (2 + 2 * capC) * D := by nlinarith
      calc (4 * q' + 1) * ((2 * D + 2 * lfCap r K D) * U.card ^ (r - 1 - J.card))
          ≤ (4 * q' + 1) * (((2 + 2 * capC) * D) *
              ((K + 1) ^ (r - 1) * Z.card ^ (r - 1 - J.card))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul h2D (hpow _ (by omega)))
        _ = Cd * D * Z.card ^ (r - 1 - J.card) := by rw [hCd]; ring
    · have hsum := lf_degSum (q := q') hXr hr (by omega) hdeg hload S hS
      have hb : 4 * (q' - 1) * D + (q' - 1) * (D + 3 * lfCap r K D) ≤
          (4 * (q' - 1) + (q' - 1) * (1 + 3 * capC)) * D := by
        have : (q' - 1) * (D + 3 * lfCap r K D) ≤ (q' - 1) * ((1 + 3 * capC) * D) :=
          Nat.mul_le_mul_left _ (by nlinarith)
        nlinarith
      exact hsum.trans hb
  · rw [not_nonempty_iff_eq_empty] at hXne
    subst hXne
    have hout : outParts ends Z (r - 1) (∅ : Finset E) = ∅ := by simp [outParts]
    refine ⟨ChainRefiner.Lab, inferInstance, fun _ _ => ∅, fun _ => ∅, fun _ => ∅,
      ⟨fun T hT => by rw [hout] at hT; simp at hT, fun T hT => by rw [hout] at hT; simp at hT⟩,
      fun J _ => by rw [hout, filter_empty, sum_empty]; exact Nat.zero_le _,
      fun S _ => by rw [hout, filter_empty, sum_empty]; exact Nat.zero_le _⟩

/-- **A degree-controlled flat step from a placed level.** -/
theorem placedStep_of_level {q r i : ℕ} {a : ℕ → ℕ} (hir : i < r) (hrq : r < q)
    (hL : PlacedLinkLevelA q r i a) (K : ℕ) :
    ∃ Cs C : ℕ, 0 < Cs ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → IsFlat i Z ends X → (∀ x ∈ X, ends x ⊆ U) →
      U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → a Z.card ≤ D → Cs ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      PlacedOut q r (i - 1) C ends Z U X D := by
  obtain ⟨Cl, Ch, Cd, Cg, hlev⟩ := hL K
  obtain ⟨Cs₀, Cs', -, hflat⟩ := placedFlatStep_link q r i Cl hir hrq
  refine ⟨Ch + Cs₀ + 1, flatConst q r Cl + Cg + Cs' * Cd, by omega, ?_⟩
  intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 haD hCD hdeg
  have hCh : Ch ≤ Z.card := le_trans (by omega) hCD
  have hCs : Cs₀ ≤ Z.card := le_trans (by omega) hCD
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
theorem placedChain {q r : ℕ} {a : ℕ → ℕ} (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelA q r i a) :
    ∀ j, j < r → ∀ K : ℕ, ∃ Cs C : ℕ, 0 < Cs ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E]
      (ends : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → IsFlat j Z ends X → (∀ x ∈ X, ends x ⊆ U) →
      U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → a Z.card ≤ D → Cs ≤ Z.card →
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
      placedStep_of_level hj hrq (hL (j + 1) (by omega) hj) K
    obtain ⟨Cs₂, C₂, -, hrest⟩ := ih (by omega) (K + 1)
    refine ⟨Cs₁ + Cs₂, C₁ + C₂ + C₂ * (1 + C₁), by omega, ?_⟩
    intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 haD hCD hdeg
    have hCD₁ : Cs₁ ≤ Z.card := le_trans (by omega) hCD
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
    have hCD₂ : Cs₂ ≤ Z.card := le_trans (by omega) hCD
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

/-- A residual refiner gives a `PlacedOut` (relabel the new copies into a fresh copy of `E`). -/
theorem placedOut_of_residual {q r j C : ℕ} {n : ℕ} {E : Type} [DecidableEq E]
    {ends : E → Finset (Fin n)} {Z U : Finset (Fin n)} {X R Y : Finset E}
    {𝒲 : Finset (Finset E)} {D : ℕ} (h : IsResidualMultiRefiner q r C ends X R Y 𝒲)
    (hY : Y ⊆ X ∪ R) (hflat : IsFlat j Z ends Y) (hRU : ∀ c ∈ R, ends c ⊆ U ∪ Z)
    (hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends R S ≤ C * D)
    (hpd : ∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends 𝒲 S ≤ C * D) :
    PlacedOut q r j C ends Z U X D := by
  classical
  let φ : E → E ⊕ E := fun c => if c ∈ X then Sum.inl c else Sum.inr c
  have hends : ∀ c, Sum.elim ends ends (φ c) = ends c := by
    intro c; simp only [φ]; split_ifs <;> rfl
  have hφ : Function.Injective φ := by
    intro c c' hcc'
    simp only [φ] at hcc'
    split_ifs at hcc' <;> simpa using hcc'
  have hXφ : X.image φ = X.image Sum.inl :=
    image_congr fun c hc => by simp only [φ, if_pos (mem_coe.1 hc)]
  have hRφ : ∀ c ∈ R, φ c = Sum.inr c := fun c hc => by
    simp only [φ, if_neg (disjoint_right.1 h.disjoint hc)]
  have h' := residual_relabel h φ (Sum.elim ends ends) (fun c _ => hends c) hφ.injOn hY
  rw [hXφ] at h'
  refine ⟨E ⊕ E, inferInstance, Sum.inl, Sum.elim ends ends, R.image φ, Y.image φ,
    𝒲.image (image φ), Sum.inl_injective, fun c => rfl, ?_, h', ?_, ?_, ?_, ?_,
    fun S hS => (pdeg_image_le φ hends 𝒲 S).trans (hpd S hS)⟩
  · intro c hc x hx
    obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
    rw [hRφ c₁ hc₁] at hx
    exact Sum.inl_ne_inr hx
  · intro c hc
    obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
    rw [hends]; exact hflat c₁ hc₁
  · rw [← hXφ, ← image_union]; exact image_subset_image hY
  · intro c hc
    obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
    rw [hends]; exact hRU c₁ hc₁
  · intro S hS
    rw [mdeg_image_eq (A := R) (fun c _ => hends c) hφ.injOn subset_rfl]
    exact hdeg S hS

/-- **Composition of `PlacedOut`s**: a first stage to a `j`-flat residue, followed by a chain
from that residue (whose copies lie in `U ∪ Z` and have degree `≤ D₁`), to a `0`-flat residue. -/
theorem PlacedOut.comp {q r j C₁ C₂ C : ℕ} {n : ℕ} {E : Type} [DecidableEq E]
    {ends : E → Finset (Fin n)} {Z U : Finset (Fin n)} {X : Finset E} {D D₁ : ℕ}
    (h : PlacedOut q r j C₁ ends Z U X D)
    (hnext : ∀ (E₁ : Type) [DecidableEq E₁] (ends₁ : E₁ → Finset (Fin n)) (Y₁ : Finset E₁),
      MIsRGraph r ends₁ Y₁ → IsFlat j Z ends₁ Y₁ → (∀ c ∈ Y₁, ends₁ c ⊆ U ∪ Z) →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ D₁) →
      PlacedOut q r 0 C₂ ends₁ Z (U ∪ Z) Y₁ D₁)
    (hXU : ∀ x ∈ X, ends x ⊆ U)
    (hdegX : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D)
    (hD₁ : D + C₁ * D ≤ D₁) (hC : C₁ + C₂ ≤ C) (hCD : C₁ * D + C₂ * D₁ ≤ C * D) :
    PlacedOut q r 0 C ends Z U X D := by
  obtain ⟨E₁, _, g, ends₁, R₁, Y₁, 𝒲₁, hg, hends, hR₁, h₁, hflat₁, hY₁, hR₁U, hdeg₁, hpd₁⟩ := h
  have hYr : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (hY₁ hc)
  have hYU : ∀ c ∈ Y₁, ends₁ c ⊆ U ∪ Z := by
    intro c hc
    rcases mem_union.1 (hY₁ hc) with hc | hc
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
      rw [hends]; exact (hXU x hx).trans subset_union_left
    · exact hR₁U c hc
  have hdegY : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ D₁ := by
    intro S hS
    calc mdeg ends₁ Y₁ S ≤ mdeg ends₁ (X.image g ∪ R₁) S := mdeg_mono _ hY₁ S
      _ ≤ mdeg ends₁ (X.image g) S + mdeg ends₁ R₁ S := by
        unfold mdeg; rw [filter_union]; exact card_union_le _ _
      _ ≤ D + C₁ * D := by
        rw [mdeg_image_eq (A := X) (fun c _ => hends c) hg.injOn subset_rfl]
        exact Nat.add_le_add (hdegX S hS) (hdeg₁ S hS)
      _ ≤ D₁ := hD₁
  obtain ⟨E₂, _, g₂, ends₂, R₂, Y₂, 𝒲₂, hg₂, hends₂, hR₂, h₂, hflat₂, hY₂, hR₂U,
    hdeg₂, hpd₂⟩ := hnext E₁ ends₁ Y₁ hYr hflat₁ hYU hdegY
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
    exact hcomp.mono hC
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
      _ ≤ C₁ * D + C₂ * D₁ := by
        rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
        exact Nat.add_le_add (hdeg₁ S hS) (hdeg₂ S hS)
      _ ≤ C * D := hCD
  · intro S hS
    calc pdeg ends₂ (𝒲₁.image (image g₂) ∪ 𝒲₂) S
        ≤ pdeg ends₂ (𝒲₁.image (image g₂)) S + pdeg ends₂ 𝒲₂ S := pdeg_union_le _ _ _ _
      _ ≤ C₁ * D + C₂ * D₁ :=
        Nat.add_le_add ((pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)) (hpd₂ S hS)
      _ ≤ C * D := hCD

/-- **Refine Down into the reserve.**  Given placed link refiners at all levels `1, …, r - 1`:
for every `r`-multigraph `X` on `Fin n` with `(r-1)`-degrees `≤ D`, and every reserve `Z` with
`n ≤ K |Z|`, `|Z| ≥ q + r` and `Cs · D ≤ |Z|`, there is a residual `K_q^r`-refiner of `X` whose
residue lies inside `Z` (`0`-flat) and whose new copies have `(r-1)`-degrees `≤ C · D`.  The
first stage is the anti-edge round into the reserve (`placedReserveRound`), whose residue is
`(r-1)`-flat; then the levels `r - 1, …, 1` are chained (`placedChain`). -/
theorem placedIntoReserve {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevel q r i) (K : ℕ) :
    ∃ Cs C : ℕ, 0 < Cs ∧ ∀ (n : ℕ) (X : Finset (Lab n)) (Z : Finset (Fin n)) (D : ℕ),
      MIsRGraph r labEnds X → n ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → Cs * D ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg labEnds X S ≤ D) →
      PlacedOut q r 0 C labEnds Z univ X D := by
  obtain ⟨C₀, hC₀, hround⟩ := placedReserveRound (q := q) (r := r) (by omega) hrq
  obtain ⟨Cs₂, C₂, -, hrest⟩ := placedChain (a := fun _ => 0) hrq
    (fun i h1 h2 => (hL i h1 h2).toA _) (r - 1) (by omega) K
  set Kp := (K + 1) ^ (r - 1) with hKp
  have hKp1 : 1 ≤ Kp := Nat.one_le_pow _ _ (by omega)
  set C₁ := C₀ * Kp with hC₁
  have hC₀₁ : C₀ ≤ C₁ := Nat.le_mul_of_pos_right _ hKp1
  refine ⟨C₁ + Cs₂ * (1 + C₁) + 1, C₁ + C₂ + C₂ * C₁, by omega, ?_⟩
  intro n X Z D hXr hnK hZq hD1 hCD hdeg
  have hZ0 : 0 < Z.card := by omega
  have hcu : (univ : Finset (Fin n)).card = n := card_fin n
  have hXJ : ∀ J : Finset (Fin n), J.card ≤ r - 1 →
      mdeg labEnds X J ≤ Kp * D * Z.card ^ (r - 1 - J.card) := by
    intro J hJ
    refine (mdeg_le_pow (U := univ) hXr (fun _ _ => subset_univ _) hdeg hJ).trans ?_
    rw [hcu]
    calc D * n ^ (r - 1 - J.card) ≤ D * ((K + 1) * Z.card) ^ (r - 1 - J.card) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hnK.trans (by nlinarith)) _)
      _ = D * ((K + 1) ^ (r - 1 - J.card) * Z.card ^ (r - 1 - J.card)) := by rw [mul_pow]
      _ ≤ D * (Kp * Z.card ^ (r - 1 - J.card)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
            (Nat.pow_le_pow_right (by omega) (by omega)))
      _ = Kp * D * Z.card ^ (r - 1 - J.card) := by ring
  have hD' : C₀ * (Kp * D) ≤ Z.card := by
    rw [← mul_assoc]; exact le_trans (Nat.mul_le_mul_right _ (by omega)) hCD
  obtain ⟨R, Y, 𝒲, hspec, hmeet⟩ := hround n (X.sup Prod.fst) X ∅ Z (Kp * D)
    (fun c hc => le_sup (f := Prod.fst) hc) hXr hXJ (fun S _ => by simp [deg]) hD' hZ0
  have hflat : IsFlat (r - 1) Z labEnds Y := by
    intro c hc
    have hcR := hspec.residue_sub hc
    have hcard := hspec.refiner.rgraph c (mem_union_right _ hcR)
    have h1 : 0 < (labEnds c ∩ Z).card := (hmeet c hcR).card_pos
    have := card_sdiff_add_card_inter (labEnds c) Z
    omega
  have hstage : PlacedOut q r (r - 1) C₁ labEnds Z univ X D :=
    placedOut_of_residual (hspec.refiner.mono hC₀₁)
      (hspec.residue_sub.trans subset_union_right) hflat
      (fun c _ => (subset_univ _).trans subset_union_left)
      (fun S hS => (hspec.degR S hS).trans (by rw [hC₁, mul_assoc]))
      (fun S hS => (hspec.pieceDeg S hS).trans (by rw [hC₁, mul_assoc]))
  refine hstage.comp (D₁ := (1 + C₁) * D) (C₂ := C₂)
    (fun E₁ _ ends₁ Y₁ hYr hYf hYU hYd => hrest n ends₁ Z (univ ∪ Z) Y₁ ((1 + C₁) * D) hYr hYf
      hYU ?_ hZq (by nlinarith) (Nat.zero_le _) ?_ hYd)
    (fun _ _ => subset_univ _) hdeg (by nlinarith) (by nlinarith) (by nlinarith)
  · rw [union_eq_left.2 (subset_univ Z), hcu]; exact hnK
  · exact le_trans (Nat.le_mul_of_pos_right _ hD1) (le_trans (Nat.mul_le_mul_right _ (by nlinarith)) hCD)

/-- **All flat levels for `r = 2`, unconditionally.** -/
theorem placedChain_two {q : ℕ} (hq : 2 < q) (K : ℕ) :
    ∃ Cs C : ℕ, 0 < Cs ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E]
      (ends : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph 2 ends X → IsFlat 1 Z ends X → (∀ x ∈ X, ends x ⊆ U) →
      U.card ≤ K * Z.card → q + 2 ≤ Z.card → 1 ≤ D → Cs ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = 1 → mdeg ends X S ≤ D) →
      PlacedOut q 2 0 C ends Z U X D := by
  obtain ⟨Cs, C, hCs, h⟩ := placedChain (a := fun _ => 0) hq (fun i hi hi2 => by
    obtain rfl : i = 2 - 1 := by omega
    exact (placedLinkLevel_last q 2 le_rfl hq).toA _) 1 (by omega) K
  exact ⟨Cs, C, hCs, fun n E _ ends Z U X D hXr hX hU hUK hZq hD1 hCD hdeg =>
    h n ends Z U X D hXr hX hU hUK hZq hD1 (Nat.zero_le _) hCD hdeg⟩

/-- **Refine Down into the reserve for `r = 2`, unconditionally**: every graph-multigraph `X`
on `Fin n` with vertex degrees `≤ D` has, for every reserve `Z` with `n ≤ K |Z|`, `|Z| ≥ q + 2`
and `Cs · D ≤ |Z|`, a residual `K_q^2`-refiner whose residue lies inside `Z` and whose new
copies have vertex degrees `≤ C · D`. -/
theorem placedIntoReserve_two {q : ℕ} (hq : 2 < q) (K : ℕ) :
    ∃ Cs C : ℕ, 0 < Cs ∧ ∀ (n : ℕ) (X : Finset (Lab n)) (Z : Finset (Fin n)) (D : ℕ),
      MIsRGraph 2 labEnds X → n ≤ K * Z.card → q + 2 ≤ Z.card → 1 ≤ D → Cs * D ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = 1 → mdeg labEnds X S ≤ D) →
      PlacedOut q 2 0 C labEnds Z univ X D :=
  placedIntoReserve le_rfl hq (fun i hi hi2 => by
    obtain rfl : i = 2 - 1 := by omega
    exact placedLinkLevel_last q 2 le_rfl hq) K

end RefinedAbsorption.Placement
