module
public import RefinedAbsorption.LinkSpread.Flat
public import RefinedAbsorption.Placement.ChainLevelsE

/-!
# Chaining the flat steps of all link graphs at once

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

`TaggedOutE q r i j C tg bd Zo Z X Bd` is the output of a degree-controlled construction applied to
all fibres of a tagged multigraph at once: after an injective relabelling `g` of the copies, for
every tag `T` a residual `K_{q-i}^{r-i}`-refiner (constant `C`) of the bodies of the fibre of `T`,
with `j`-flat residue and new copies inside `Zo`, such that the lifted new copies `T ∪ c` and the
lifted pieces, summed over all tags, have `(r-1)`-degrees at most `Bd`.

* `taggedStep_of_levelE`: one flat step (level `j` of the bodies) for all fibres at once, from the
  link level `PlacedLinkLevelE q r (i + j)` of the lifted multigraph, in `ε`-form.
* `TaggedOutE.comp`: composition, fibre by fibre.
* **`taggedChainE`**: from `j`-flat bodies to bodies inside the sub-reserve `Z`, for all fibres
  at once, from the link levels `i + 1, …, i + j`.

So **the flat part of the link refiners at level `i` reduces to the higher link levels.**
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown

/-- Output of a degree-controlled construction on all fibres of a tagged multigraph at once. -/
def TaggedOutE (q r i j C : ℕ) {n : ℕ} {E : Type} (tg bd : E → Finset (Fin n))
    (Zo Z : Finset (Fin n)) (X : Finset E) (Bd : ℕ) : Prop :=
  ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : Finset (Fin n) → E' → Finset (Fin n))
    (R Y : Finset (Fin n) → Finset E') (𝒲 : Finset (Fin n) → Finset (Finset E')),
    Function.Injective g ∧ (∀ T c, ends' T (g c) = bd c) ∧
    (∀ T ∈ X.image tg, (∀ c ∈ R T, ∀ x, g x ≠ c) ∧
      IsResidualMultiRefiner (q - i) (r - i) C (ends' T) ((fibre tg X T).image g) (R T) (Y T)
        (𝒲 T) ∧
      IsFlat j Z (ends' T) (Y T) ∧ Y T ⊆ (fibre tg X T).image g ∪ R T ∧
      ∀ c ∈ R T, ends' T c ⊆ Zo) ∧
    (∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T ∈ X.image tg, mdeg (fun c => T ∪ ends' T c) (R T) S ≤ Bd) ∧
    ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T ∈ X.image tg, pdeg (fun c => T ∪ ends' T c) (𝒲 T) S ≤ Bd

section Basic

variable {n : ℕ} {E : Type} {tg bd : E → Finset (Fin n)} {Zo Z : Finset (Fin n)}

/-- The lifted copies are `r`-sets. -/
theorem liftEnds_rgraph {i r : ℕ} (hir : i ≤ r) (htg : ∀ x, Disjoint (tg x) Zo)
    (hbd : ∀ x, bd x ⊆ Zo) {X : Finset E} (htgc : ∀ x ∈ X, (tg x).card = i)
    (hbdc : ∀ x ∈ X, (bd x).card = r - i) : MIsRGraph r (liftEnds tg bd) X := by
  intro x hx
  unfold liftEnds
  rw [card_union_of_disjoint (disjoint_of_subset_right (hbd x) (htg x)), htgc x hx, hbdc x hx]
  omega

/-- The lifted multigraph of `j`-flat bodies is `(i + j)`-flat. -/
theorem liftEnds_flat {i j : ℕ} (hZ : Z ⊆ Zo) (htg : ∀ x, Disjoint (tg x) Zo) {X : Finset E}
    (htgc : ∀ x ∈ X, (tg x).card = i) (hX : IsFlat j Z bd X) :
    IsFlat (i + j) Z (liftEnds tg bd) X := by
  intro x hx
  rw [liftEnds_sdiff hZ htg]
  exact (card_union_le _ _).trans (by rw [htgc x hx]; exact Nat.add_le_add_left (hX x hx) _)

/-- Lifted degrees of a multigraph are the sums of the lifted degrees of its fibres. -/
theorem mdeg_liftEnds_eq_sum (X : Finset E) (S : Finset (Fin n)) :
    mdeg (liftEnds tg bd) X S =
      ∑ T ∈ X.image tg, mdeg (fun c => T ∪ bd c) (fibre tg X T) S := by
  unfold mdeg liftEnds fibre
  rw [card_eq_sum_card_fiberwise (f := tg) (t := X.image tg)
    (by intro x hx; exact mem_image_of_mem _ (mem_filter.1 hx).1)]
  refine sum_congr rfl fun T _ => congrArg card ?_
  ext x
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hx, hS⟩, rfl⟩; exact ⟨⟨hx, rfl⟩, hS⟩
  · rintro ⟨⟨hx, rfl⟩, hS⟩; exact ⟨⟨hx, hS⟩, rfl⟩

end Basic

/-- **One flat step for all fibres at once, from a link level in `ε`-form.**  The bodies are
`j`-flat with respect to `Z`; the level `PlacedLinkLevelE q r (i + j)` is applied to the lifted
multigraph, and the flat step is run in every fibre (`taggedFlatStep`). -/
theorem taggedStep_of_levelE {q r i j : ℕ} (hj : 1 ≤ j) (hijr : i + j < r) (hrq : r < q)
    (hL : PlacedLinkLevelE q r (i + j)) (K : ℕ) :
    ∃ Cr B : ℕ, ∀ s : ℕ, ∃ Cs C : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E]
      (tg bd : E → Finset (Fin n)) (Zo Z U : Finset (Fin n)) (X : Finset E) (D : ℕ),
      Z ⊆ Zo → (∀ x, Disjoint (tg x) Zo) → (∀ x, bd x ⊆ Zo) →
      (∀ x ∈ X, (tg x).card = i) → (∀ x ∈ X, (bd x).card = r - i) → IsFlat j Z bd X →
      (∀ x ∈ X, liftEnds tg bd x ⊆ U) → U.card ≤ K * Z.card → q + r ≤ Z.card → 1 ≤ D →
      Cs ≤ Z.card →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) →
      ∃ Bd : ℕ, 2 ^ s * Bd ≤ 2 ^ s * C * D + B * Z.card ∧
        TaggedOutE q r i (j - 1) Cr tg bd Zo Z X Bd := by
  obtain ⟨Cl, B, hlev⟩ := hL K
  obtain ⟨Cs₀, Cs', -, hflat⟩ := taggedFlatStep q r i j Cl hj hijr hrq
  refine ⟨flatConst (q - i) (r - i) Cl, (1 + Cs') * B, fun s => ?_⟩
  obtain ⟨Ch, Cd, Cg, hlev'⟩ := hlev s
  refine ⟨Ch + Cs₀, Cg + Cs' * Cd + Cs', ?_⟩
  intro n E _ tg bd Zo Z U X D hZ htg hbd htgc hbdc hX hU hUK hZq hD1 hCD hdeg
  have hpos : 0 < 2 ^ s := by positivity
  obtain ⟨N, _, endsN, RN, 𝒲, hLR, hdens, hdegL⟩ :=
    hlev' n (liftEnds tg bd) Z U X D (liftEnds_rgraph (by omega) htg hbd htgc hbdc)
      (liftEnds_flat hZ htg htgc hX) hU hUK hZq hD1 (le_trans (by omega) hCD) hdeg
  set Dd := Cd * D + B * Z.card / 2 ^ s + 1 with hDd
  have hround := le_pow_mul_div_add_one s (B * Z.card)
  have hdiv : 2 ^ s * (B * Z.card / 2 ^ s) ≤ B * Z.card := Nat.mul_div_le _ _
  have hDd1 : 2 ^ s * Cd * D + B * Z.card ≤ 2 ^ s * Dd := by
    have e : 2 ^ s * Dd = 2 ^ s * Cd * D + 2 ^ s * (B * Z.card / 2 ^ s + 1) := by
      rw [hDd]; ring
    omega
  have hdens' : ∀ J : Finset (Fin n), J.card ≤ r - 1 →
      ∑ A ∈ (outParts (liftEnds tg bd) Z (i + j) X).filter (fun A => J \ Z ⊆ A),
        ((𝒲 A).filter fun W => J ∩ Z ⊆ W.biUnion (lE (liftEnds tg bd) Z endsN A)).card ≤
        Dd * Z.card ^ (r - 1 - J.card) := by
    intro J hJ
    refine Nat.le_of_mul_le_mul_left ((hdens J hJ).trans ?_) hpos
    calc (2 ^ s * Cd * D + B * Z.card) * Z.card ^ (r - 1 - J.card)
        ≤ (2 ^ s * Dd) * Z.card ^ (r - 1 - J.card) := Nat.mul_le_mul_right _ hDd1
      _ = 2 ^ s * (Dd * Z.card ^ (r - 1 - J.card)) := by ring
  obtain ⟨R, Y, 𝒲', hfib, hdegR, hpdR⟩ := hflat n tg bd Zo Z endsN X RN 𝒲 Dd hZ htg hbd htgc
    hbdc hX hLR hZq (le_trans (by omega) hCD) hdens'
  refine ⟨Cg * D + B * Z.card / 2 ^ s + Cs' * Dd, ?_, E ⊕ FLab (Fin n) E N, inferInstance,
    Sum.inl, fun T => fEnds bd (fun T₂ => endsN (T ∪ T₂)), R, Y, 𝒲', Sum.inl_injective,
    fun T c => rfl, fun T hT => ?_, fun S hS => ?_, fun S hS => ?_⟩
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
  · obtain ⟨h1, h2, -, h4, h5, h6⟩ := hfib T hT
    exact ⟨fun c hc x hx => h5 c hc x hx.symm, h1, h2, h4, h6⟩
  · refine (hdegR S hS).trans (Nat.add_le_add_right ?_ _)
    exact le_add_div_of_pow_mul_le (by have := hdegL S hS; rw [mul_assoc] at this; exact this)
  · exact (hpdR S hS).trans (Nat.le_add_left _ _)

end RefinedAbsorption.LinkSpread
