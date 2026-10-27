module
public import RefinedAbsorption.Placement.ChainLevels

/-!
# Link levels with a vanishing additive term (`ε`-form)

`PlacedLinkLevelE q r i` weakens `PlacedLinkLevel q r i` (and `PlacedLinkLevelA q r i a` for a
sublinear `a`): for every precision `s`, the link refiners may carry an additive term
`B · |Z| / 2^s`, where `B` (and the refinedness `Cl`) do **not** depend on `s`, while the
coefficients of `D` may.  In the natural-number form used here, the bounds read
`2^s · (…) ≤ 2^s · C_s · D + B · |Z|`.

This is exactly the shape of budget given by refiners without the fine compression of the Refine
Down Lemma: a degree bound `≈ D^α m^{1-α}` is `≤ C_ε D + ε m` for every `ε > 0`, by the weighted
AM–GM inequality.

* `PlacedLinkLevel.toE`, `PlacedLinkLevelA.toE`: the previous forms imply the new one.
* `PlacedOutE`: as `PlacedOut`, with the refinedness constant and the degree bound separated.
* `placedStep_of_levelE`, **`placedChainE`**: the flat steps and their chaining, in `ε`-form.  The
  precisions of the successive levels are chosen backwards, so that the additive terms of the
  earlier levels are not amplified by the constants of the later ones.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown

/-- **Placed link refiners at level `i`, `ε`-form.**  For every `K` there are a refinedness
constant `Cl` and an additive constant `B` such that for every precision `s` the link refiners
exist with bounds `C_s · D + B · |Z| / 2^s` (written `2^s · (…) ≤ 2^s · C_s · D + B · |Z|`). -/
def PlacedLinkLevelE (q r i : ℕ) : Prop :=
  ∀ K : ℕ, ∃ Cl B : ℕ, ∀ s : ℕ, ∃ Ch Cd Cg : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E]
    (ends : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
    MIsRGraph r ends X → IsFlat i Z ends X → (∀ x ∈ X, ends x ⊆ U) →
    U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → Ch ≤ Z.card →
    (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
    ∃ (N : Type) (_ : DecidableEq N) (endsN : Finset (Fin n) → N → Finset (Fin n))
      (RN : Finset (Fin n) → Finset N) (𝒲 : Finset (Fin n) → Finset (Finset (E ⊕ N))),
      LinkRefiners q r i Cl ends Z X endsN RN 𝒲 ∧
      (∀ J : Finset (Fin n), J.card ≤ r - 1 →
        2 ^ s * ∑ T ∈ (outParts ends Z i X).filter (fun T => J \ Z ⊆ T),
          ((𝒲 T).filter fun W => J ∩ Z ⊆ W.biUnion (lE ends Z endsN T)).card ≤
          (2 ^ s * Cd * D + B * Z.card) * Z.card ^ (r - 1 - J.card)) ∧
      ∀ S : Finset (Fin n), S.card = r - 1 →
        2 ^ s * ∑ T ∈ (outParts ends Z i X).filter (fun T => S \ Z ⊆ T),
          mdeg (endsN T) (RN T) (S ∩ Z) ≤ 2 ^ s * Cg * D + B * Z.card

/-- `PlacedLinkLevel` (no additive term) implies the `ε`-form, with `B = 0`. -/
theorem PlacedLinkLevel.toE {q r i : ℕ} (h : PlacedLinkLevel q r i) : PlacedLinkLevelE q r i := by
  intro K
  obtain ⟨Cl, Ch, Cd, Cg, hlev⟩ := h K
  refine ⟨Cl, 0, fun s => ⟨Ch, Cd, Cg, ?_⟩⟩
  intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 hCh hdeg
  obtain ⟨N, _, endsN, RN, 𝒲, hLR, hdens, hdegL⟩ :=
    hlev n ends Z U X D hXr hX hU hUK hZq hD1 hCh hdeg
  refine ⟨N, inferInstance, endsN, RN, 𝒲, hLR, fun J hJ => ?_, fun S hS => ?_⟩
  · have := Nat.mul_le_mul_left (2 ^ s) (hdens J hJ)
    calc _ ≤ 2 ^ s * (Cd * D * Z.card ^ (r - 1 - J.card)) := this
      _ = (2 ^ s * Cd * D + 0 * Z.card) * Z.card ^ (r - 1 - J.card) := by ring
  · have := Nat.mul_le_mul_left (2 ^ s) (hdegL S hS)
    calc _ ≤ 2 ^ s * (Cg * D) := this
      _ = 2 ^ s * Cg * D + 0 * Z.card := by ring

/-- `PlacedLinkLevelA` with a sublinear additive term implies the `ε`-form. -/
theorem PlacedLinkLevelA.toE {q r i : ℕ} {a : ℕ → ℕ} (h : PlacedLinkLevelA q r i a)
    (hsub : ∀ k : ℕ, ∃ m₀ : ℕ, ∀ m ≥ m₀, k * a m ≤ m) : PlacedLinkLevelE q r i := by
  intro K
  obtain ⟨Cl, Ch, Cd, Cg, hlev⟩ := h K
  refine ⟨Cl, 1, fun s => ?_⟩
  obtain ⟨m₀, hm₀⟩ := hsub (2 ^ s * (Cd + Cg))
  refine ⟨Ch + m₀, Cd, Cg, ?_⟩
  intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 hCh hdeg
  have ha := hm₀ Z.card (by omega)
  obtain ⟨N, _, endsN, RN, 𝒲, hLR, hdens, hdegL⟩ :=
    hlev n ends Z U X (D + a Z.card) hXr hX hU hUK hZq (by omega) (Nat.le_add_left _ _)
      (by omega) (fun S hS => (hdeg S hS).trans (Nat.le_add_right _ _))
  have hCd : 2 ^ s * Cd * a Z.card ≤ Z.card :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))) ha
  have hCg : 2 ^ s * Cg * a Z.card ≤ Z.card :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))) ha
  refine ⟨N, inferInstance, endsN, RN, 𝒲, hLR, fun J hJ => ?_, fun S hS => ?_⟩
  · have := Nat.mul_le_mul_left (2 ^ s) (hdens J hJ)
    calc _ ≤ 2 ^ s * (Cd * (D + a Z.card) * Z.card ^ (r - 1 - J.card)) := this
      _ = (2 ^ s * Cd * D + 2 ^ s * Cd * a Z.card) * Z.card ^ (r - 1 - J.card) := by ring
      _ ≤ (2 ^ s * Cd * D + 1 * Z.card) * Z.card ^ (r - 1 - J.card) :=
          Nat.mul_le_mul_right _ (by omega)
  · have := Nat.mul_le_mul_left (2 ^ s) (hdegL S hS)
    calc _ ≤ 2 ^ s * (Cg * (D + a Z.card)) := this
      _ = 2 ^ s * Cg * D + 2 ^ s * Cg * a Z.card := by ring
      _ ≤ 2 ^ s * Cg * D + 1 * Z.card := by omega

/-- Output of a degree-controlled stage, with refinedness `C` and degree bound `Bd` separated
(compare `PlacedOut`, where the degree bound is `C · D`). -/
def PlacedOutE (q r j C : ℕ) {n : ℕ} {E : Type} (ends : E → Finset (Fin n))
    (Z U : Finset (Fin n)) (X : Finset E) (Bd : ℕ) : Prop :=
  ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
    (R Y : Finset E') (𝒲 : Finset (Finset E')),
    Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
    IsResidualMultiRefiner q r C ends' (X.image g) R Y 𝒲 ∧ IsFlat j Z ends' Y ∧
    Y ⊆ X.image g ∪ R ∧ (∀ c ∈ R, ends' c ⊆ U ∪ Z) ∧
    (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ Bd) ∧
    ∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤ Bd

theorem placedOut_iff_E {q r j C : ℕ} {n : ℕ} {E : Type} {ends : E → Finset (Fin n)}
    {Z U : Finset (Fin n)} {X : Finset E} {D : ℕ} :
    PlacedOut q r j C ends Z U X D ↔ PlacedOutE q r j C ends Z U X (C * D) := Iff.rfl

/-- **Composition of `PlacedOutE`s.** -/
theorem PlacedOutE.comp {q r j C₁ C₂ : ℕ} {n : ℕ} {E : Type} [DecidableEq E]
    {ends : E → Finset (Fin n)} {Z U : Finset (Fin n)} {X : Finset E} {D Bd₁ : ℕ}
    (P : ℕ → Prop) (h : PlacedOutE q r j C₁ ends Z U X Bd₁)
    (hnext : ∀ (E₁ : Type) [DecidableEq E₁] (ends₁ : E₁ → Finset (Fin n)) (Y₁ : Finset E₁),
      MIsRGraph r ends₁ Y₁ → IsFlat j Z ends₁ Y₁ → (∀ c ∈ Y₁, ends₁ c ⊆ U ∪ Z) →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ D + Bd₁) →
      ∃ Bd₂, P Bd₂ ∧ PlacedOutE q r 0 C₂ ends₁ Z (U ∪ Z) Y₁ Bd₂)
    (hXU : ∀ x ∈ X, ends x ⊆ U)
    (hdegX : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) :
    ∃ Bd₂, P Bd₂ ∧ PlacedOutE q r 0 (C₁ + C₂) ends Z U X (Bd₁ + Bd₂) := by
  obtain ⟨E₁, _, g, ends₁, R₁, Y₁, 𝒲₁, hg, hends, hR₁, h₁, hflat₁, hY₁, hR₁U, hdeg₁, hpd₁⟩ := h
  have hYr : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (hY₁ hc)
  have hYU : ∀ c ∈ Y₁, ends₁ c ⊆ U ∪ Z := by
    intro c hc
    rcases mem_union.1 (hY₁ hc) with hc | hc
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
      rw [hends]; exact (hXU x hx).trans subset_union_left
    · exact hR₁U c hc
  have hdegY : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ D + Bd₁ := by
    intro S hS
    calc mdeg ends₁ Y₁ S ≤ mdeg ends₁ (X.image g ∪ R₁) S := mdeg_mono _ hY₁ S
      _ ≤ mdeg ends₁ (X.image g) S + mdeg ends₁ R₁ S := by
        unfold mdeg; rw [filter_union]; exact card_union_le _ _
      _ ≤ D + Bd₁ := by
        rw [mdeg_image_eq (A := X) (fun c _ => hends c) hg.injOn subset_rfl]
        exact Nat.add_le_add (hdegX S hS) (hdeg₁ S hS)
  obtain ⟨Bd₂, hP, E₂, _, g₂, ends₂, R₂, Y₂, 𝒲₂, hg₂, hends₂, hR₂, h₂, hflat₂, hY₂, hR₂U,
    hdeg₂, hpd₂⟩ := hnext E₁ ends₁ Y₁ hYr hflat₁ hYU hdegY
  have h₁' := residual_relabel h₁ g₂ ends₂ (fun c _ => hends₂ c) hg₂.injOn hY₁
  have hcomp := h₁'.trans h₂ (by rw [← image_union]; exact image_subset_image hY₁) (by
    rw [disjoint_left]
    intro c hc hc'
    rw [← image_union] at hc'
    obtain ⟨x, -, rfl⟩ := mem_image.1 hc'
    exact hR₂ _ hc x rfl)
  refine ⟨Bd₂, hP, E₂, inferInstance, g₂ ∘ g, ends₂, R₁.image g₂ ∪ R₂, Y₂,
    𝒲₁.image (image g₂) ∪ 𝒲₂, hg₂.comp hg, fun c => by simp [hends₂, hends], ?_, ?_, hflat₂,
    ?_, ?_, ?_, ?_⟩
  · intro c hc x hx
    rcases mem_union.1 hc with hc | hc
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 hc
      exact hR₁ c₁ hc₁ x (hg₂ hx)
    · exact hR₂ c hc _ hx
  · rw [← image_image]
    exact hcomp
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
      _ ≤ Bd₁ + Bd₂ := by
        rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
        exact Nat.add_le_add (hdeg₁ S hS) (hdeg₂ S hS)
  · intro S hS
    calc pdeg ends₂ (𝒲₁.image (image g₂) ∪ 𝒲₂) S
        ≤ pdeg ends₂ (𝒲₁.image (image g₂)) S + pdeg ends₂ 𝒲₂ S := pdeg_union_le _ _ _ _
      _ ≤ Bd₁ + Bd₂ :=
        Nat.add_le_add ((pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)) (hpd₂ S hS)

/-- Arithmetic: `2^s · x ≤ 2^s · a + b` gives `x ≤ a + b / 2^s`. -/
theorem le_add_div_of_pow_mul_le {s x a b : ℕ} (h : 2 ^ s * x ≤ 2 ^ s * a + b) :
    x ≤ a + b / 2 ^ s := by
  have hpos : 0 < 2 ^ s := by positivity
  have : x ≤ (b + 2 ^ s * a) / 2 ^ s := by
    rw [Nat.le_div_iff_mul_le hpos]; linarith
  rw [Nat.add_mul_div_left _ _ hpos] at this
  omega

/-- Arithmetic: rounding up `b / 2^s`. -/
theorem le_pow_mul_div_add_one (s b : ℕ) : b ≤ 2 ^ s * (b / 2 ^ s + 1) := by
  have hpos : 0 < 2 ^ s := by positivity
  have := Nat.lt_div_mul_add (a := b) hpos
  nlinarith

/-- **A degree-controlled flat step from a level in `ε`-form.** -/
theorem placedStep_of_levelE {q r i : ℕ} (hir : i < r) (hrq : r < q)
    (hL : PlacedLinkLevelE q r i) (K : ℕ) :
    ∃ Cr B : ℕ, ∀ s : ℕ, ∃ Cs C : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E]
      (ends : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → IsFlat i Z ends X → (∀ x ∈ X, ends x ⊆ U) →
      U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → Cs ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      ∃ Bd : ℕ, 2 ^ s * Bd ≤ 2 ^ s * C * D + B * Z.card ∧
        PlacedOutE q r (i - 1) Cr ends Z U X Bd := by
  obtain ⟨Cl, B, hlev⟩ := hL K
  obtain ⟨Cs₀, Cs', -, hflat⟩ := placedFlatStep_link q r i Cl hir hrq
  refine ⟨flatConst q r Cl, (1 + Cs') * B, fun s => ?_⟩
  obtain ⟨Ch, Cd, Cg, hlev'⟩ := hlev s
  refine ⟨Ch + Cs₀, Cg + Cs' * Cd + Cs', ?_⟩
  intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 hCD hdeg
  have hpos : 0 < 2 ^ s := by positivity
  obtain ⟨N, _, endsN, RN, 𝒲, hLR, hdens, hdegL⟩ :=
    hlev' n ends Z U X D hXr hX hU hUK hZq hD1 (le_trans (by omega) hCD) hdeg
  set Dd := Cd * D + B * Z.card / 2 ^ s + 1 with hDd
  have hround := le_pow_mul_div_add_one s (B * Z.card)
  have hdiv : 2 ^ s * (B * Z.card / 2 ^ s) ≤ B * Z.card := Nat.mul_div_le _ _
  have hDd1 : 2 ^ s * Cd * D + B * Z.card ≤ 2 ^ s * Dd := by
    have e : 2 ^ s * Dd = 2 ^ s * Cd * D + 2 ^ s * (B * Z.card / 2 ^ s + 1) := by
      rw [hDd]; ring
    omega
  have hdens' : ∀ J : Finset (Fin n), J.card ≤ r - 1 →
      ∑ T ∈ (outParts ends Z i X).filter (fun T => J \ Z ⊆ T),
        ((𝒲 T).filter fun W => J ∩ Z ⊆ W.biUnion (lE ends Z endsN T)).card ≤
        Dd * Z.card ^ (r - 1 - J.card) := by
    intro J hJ
    refine Nat.le_of_mul_le_mul_left ((hdens J hJ).trans ?_) hpos
    calc (2 ^ s * Cd * D + B * Z.card) * Z.card ^ (r - 1 - J.card)
        ≤ (2 ^ s * Dd) * Z.card ^ (r - 1 - J.card) := Nat.mul_le_mul_right _ hDd1
      _ = 2 ^ s * (Dd * Z.card ^ (r - 1 - J.card)) := by ring
  obtain ⟨R, Y, 𝒲', h1, h2, -, h4, h5, h6, h7, h8⟩ :=
    hflat n ends Z endsN X RN 𝒲 Dd hXr hX hLR hZq (le_trans (by omega) hCD) hdens'
  refine ⟨Cg * D + B * Z.card / 2 ^ s + Cs' * Dd, ?_, E ⊕ FLab (Fin n) E N, inferInstance,
    Sum.inl, fEnds ends endsN, R, Y, 𝒲', Sum.inl_injective, fun c => rfl,
    fun c hc x hx => h5 c hc x hx.symm, h1, h2, h4, fun c hc => ?_, fun S hS => ?_,
    fun S hS => ?_⟩
  · have e1 : 2 ^ s * (Cg * D + B * Z.card / 2 ^ s + Cs' * Dd) =
        2 ^ s * Cg * D + 2 ^ s * (B * Z.card / 2 ^ s) +
          Cs' * (2 ^ s * Cd * D + 2 ^ s * (B * Z.card / 2 ^ s) + 2 ^ s) := by rw [hDd]; ring
    have e2 : 2 ^ s * (Cg + Cs' * Cd + Cs') * D + (1 + Cs') * B * Z.card =
        2 ^ s * Cg * D + B * Z.card + Cs' * (2 ^ s * Cd * D + B * Z.card + 2 ^ s * D) := by ring
    rw [e1, e2]
    have h2D : 2 ^ s ≤ 2 ^ s * D := Nat.le_mul_of_pos_right _ hD1
    have := Nat.mul_le_mul_left Cs' (show 2 ^ s * Cd * D + 2 ^ s * (B * Z.card / 2 ^ s) + 2 ^ s ≤
      2 ^ s * Cd * D + B * Z.card + 2 ^ s * D by omega)
    omega
  · obtain ⟨T, hT, hcT⟩ := h6 c hc
    exact hcT.trans (union_subset_union (outParts_subset hU hT) subset_rfl)
  · refine (h7 S hS).trans (Nat.add_le_add_right ?_ _)
    exact le_add_div_of_pow_mul_le (by have := hdegL S hS; rw [mul_assoc] at this; exact this)
  · exact (h8 S hS).trans (Nat.le_add_left _ _)

/-- **Chaining the levels `j, …, 1` in `ε`-form.** -/
theorem placedChainE {q r : ℕ} (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelE q r i) :
    ∀ j, j < r → ∀ K : ℕ, ∃ Cr B : ℕ, ∀ s : ℕ, ∃ Cs C : ℕ, ∀ (n : ℕ) {E : Type}
      [DecidableEq E] (ends : E → Finset (Fin n)) (Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph r ends X → IsFlat j Z ends X → (∀ x ∈ X, ends x ⊆ U) →
      U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D → Cs ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
      ∃ Bd : ℕ, 2 ^ s * Bd ≤ 2 ^ s * C * D + B * Z.card ∧
        PlacedOutE q r 0 Cr ends Z U X Bd := by
  intro j
  induction j with
  | zero =>
    intro _ K
    refine ⟨1, 0, fun s => ⟨0, 0, ?_⟩⟩
    intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 _ hdeg
    refine ⟨0, by simp, E, inferInstance, id, ends, ∅, X, ∅, Function.injective_id,
      fun c => rfl, by simp, ?_, hX, by simp, by simp, fun S _ => by simp [mdeg],
      fun S _ => by simp [pdeg]⟩
    rw [image_id]
    exact isResidualMultiRefiner_self 1 hXr
  | succ j ih =>
    intro hj K
    obtain ⟨Cr₁, B₁, hstep⟩ := placedStep_of_levelE hj hrq (hL (j + 1) (by omega) hj) K
    obtain ⟨Cr₂, B₂, hrest⟩ := ih (by omega) (K + 1)
    refine ⟨Cr₁ + Cr₂, B₁ + B₂, fun s => ?_⟩
    obtain ⟨Cs₂, C₂, hrest'⟩ := hrest (s + 1)
    obtain ⟨Cs₁, C₁, hstep'⟩ := hstep (s + (C₂ + 1))
    refine ⟨Cs₁ + Cs₂, 2 ^ (C₂ + 1) * C₁ + 2 * C₂, ?_⟩
    intro n E _ ends Z U X D hXr hX hU hUK hZq hD1 hCD hdeg
    obtain ⟨Bd₁, hBd₁, hout₁⟩ :=
      hstep' n ends Z U X D hXr hX hU hUK hZq hD1 (le_trans (by omega) hCD) hdeg
    rw [Nat.add_sub_cancel] at hout₁
    have hUK' : (U ∪ Z).card ≤ (K + 1) * Z.card := by
      have := card_union_le U Z
      nlinarith
    obtain ⟨Bd₂, hBd₂, hout⟩ := hout₁.comp
      (fun Bd₂ => 2 ^ (s + 1) * Bd₂ ≤ 2 ^ (s + 1) * C₂ * (D + Bd₁) + B₂ * Z.card)
      (fun E₁ _ ends₁ Y₁ hYr hYf hYU hYd => hrest' n ends₁ Z (U ∪ Z) Y₁ (D + Bd₁) hYr hYf hYU
        hUK' hZq (by omega) (le_trans (by omega) hCD) hYd) hU hdeg
    refine ⟨Bd₁ + Bd₂, ?_, hout⟩
    -- arithmetic
    have hC2 : 2 * (C₂ + 1) ≤ 2 ^ (C₂ + 1) := by
      have := Nat.lt_two_pow_self (n := C₂)
      rw [pow_succ]; omega
    have e1 : 2 ^ (s + (C₂ + 1)) = 2 ^ s * 2 ^ (C₂ + 1) := pow_add _ _ _
    rw [e1] at hBd₁
    have e2 : 2 ^ (s + 1) = 2 ^ s * 2 := pow_succ _ _
    rw [e2] at hBd₂
    -- `2 · 2^s · (1 + C₂) · Bd₁ ≤ 2^s · 2^(C₂+1) · Bd₁`
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

end RefinedAbsorption.Placement
