module
public import RequestProject.FlatOmni.StageK
public import RequestProject.FlatOmni.Descent

/-!
# Local refiners for graphs with the sublinear additive term

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Theorem 3.8 for graphs, in the local
form used in §4.  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

**`localRefiner`**: a graph multigraph `L` whose copies lie in a set `Y`, with vertex degrees
`≤ D`, has, for every set `P` with `|Y| ≤ K |P|` (and `|P|` large), a complete multi-refiner whose
new copies lie inside `Y ∪ P`, whose pieces contain at most one copy of `L`, and whose new copies
and pieces have vertex degrees `≤ C · (D + sharpPot 2 |P|)`.

The construction is one refine-down stage from `Y` into `P` (`multiStageK`), followed by the
descent through windows inside `P` (`localDescent`).
-/

@[expose] public section

namespace RefinedAbsorption.FlatOmni

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement RefinedAbsorption.Dense RefinedAbsorption.Window
  RefinedAbsorption.Sharp

/-- **Local refiners for graphs** (see the module docstring). -/
theorem localRefiner {q : ℕ} (hq : 2 < q) (K : ℕ) :
    ∃ C Ch : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (Y P : Finset (Fin n)) (L : Finset E) (D : ℕ),
      Y.card ≤ K * P.card → Ch ≤ P.card → MIsRGraph 2 ends L → (∀ x ∈ L, ends x ⊆ Y) →
      1 ≤ D → (∀ v, mdeg ends L {v} ≤ D) →
      ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
        (R : Finset E') (𝒲 : Finset (Finset E')),
        Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
        IsMultiRefiner q 2 C ends' (L.image g) R 𝒲 ∧ (∀ c ∈ R, ends' c ⊆ Y ∪ P) ∧
        (∀ W ∈ 𝒲, (W.filter (· ∈ L.image g)).card ≤ 1) ∧
        (∀ v, mdeg ends' R {v} ≤ C * (D + sharpPot 2 P.card)) ∧
        (∀ v, pdeg ends' 𝒲 {v} ≤ C * (D + sharpPot 2 P.card)) := by
  classical
  obtain ⟨Cs, C₁, M, -, -, hst⟩ := multiStageK (q := q) (r := 2) (a := fun _ => 0) le_rfl hq
    (fun i hi hir => by
      obtain rfl : i = 1 := by omega
      exact (placedLinkLevel_last q 2 le_rfl hq).toA _) K
  obtain ⟨C₂, A, hdesc⟩ := localDescent hq M
  refine ⟨C₁ + C₂ + A * (C₁ + 2), Cs, ?_⟩
  intro n E _ ends Y P L D hYK hCs hLr hLY hD1 hdeg
  have hdeg' : ∀ S : Finset (Fin n), S.card = 2 - 1 → mdeg ends L S ≤ D := by
    intro S hS
    obtain ⟨v, rfl⟩ := card_eq_one.1 hS
    exact hdeg v
  obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hY₁P, hY₁m, hR₁U, hdeg₁,
    hone₁, hpd₁⟩ := hst n ends P Y L D hLr hLY hYK hCs hD1 (Nat.zero_le _) hdeg'
  have hY₁r : MIsRGraph 2 ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
  set D₁ := (C₁ + 1) * D with hD₁
  have hD₁1 : 1 ≤ D₁ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hdegY₁ : ∀ v, mdeg ends₁ Y₁ {v} ≤ D₁ := by
    intro v
    refine (mdeg_mono _ hY₁R _).trans ((hdeg₁ {v} (by simp)).trans ?_)
    exact Nat.mul_le_mul_right _ (by omega)
  obtain ⟨E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, hends₂, hR₂f, h₂, hR₂P, hdeg₂, hpd₂⟩ :=
    hdesc n ends₁ P Y₁ D₁ hY₁r hY₁P hD₁1 hY₁m hdegY₁
  have h12 := IsResidualMultiRefiner.compose g₂ hg₂ hends₂ h₁
    (hY₁R.trans subset_union_right) h₂ hR₂f
  have hone := oneX_compose g₂ hg₂ h₁.disjoint hY₁R hone₁ h₂ hR₂f
  rw [image_image] at h12 hone
  set Φ := sharpPot 2 P.card with hΦ
  have hbound : C₁ * D + A * (D₁ + Φ) ≤ (C₁ + C₂ + A * (C₁ + 2)) * (D + Φ) := by
    have e : (C₁ + C₂ + A * (C₁ + 2)) * (D + Φ) = C₁ * D + A * ((C₁ + 1) * D + Φ) +
        (C₁ * Φ + C₂ * (D + Φ) + A * D + A * (C₁ + 1) * Φ) := by ring
    rw [e, hD₁]; exact Nat.le_add_right _ _
  refine ⟨E₂, inferInstance, g₂ ∘ g₁, ends₂, R₁.image g₂ ∪ R₂, 𝒲₁.image (image g₂) ∪ 𝒲₂,
    hg₂.comp hg₁, fun c => by simp [hends₂, hends₁], ?_, h12.mono (Nat.le_add_right _ _), ?_, hone,
    fun v => ?_, fun v => ?_⟩
  · intro c hc x
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      intro hx
      exact hR₁f c₁ hc₁ x (hg₂ hx)
    · exact hR₂f c h _
  · intro c hc
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      rw [hends₂]; exact hR₁U c₁ hc₁
    · exact (hR₂P c h).trans subset_union_right
  · refine (Dense.mdeg_union_le _ _ _ _).trans ?_
    rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
    have := hdeg₁ {v} (by simp)
    have := hdeg₂ v
    omega
  · refine (pdeg_union_le _ _ _ _).trans ?_
    have := (pdeg_image_le g₂ hends₂ 𝒲₁ {v}).trans (hpd₁ {v} (by simp))
    have := hpd₂ v
    omega

end RefinedAbsorption.FlatOmni
