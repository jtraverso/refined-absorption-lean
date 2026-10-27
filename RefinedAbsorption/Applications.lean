module
public import RefinedAbsorption.Multigraph.Existence

/-!
# Applications: the small-girth cases of the high girth conjectures

Section 5 of the survey concerns Steiner systems of high girth.  A `K_q^r`-packing has girth at
least `g` if it contains no `((q-r)i + r, i)`-configuration with `2 ≤ i < g`
(`HasGirthAtLeast`).  For small `g` this condition is automatic:

* every `K_q^r`-decomposition has girth at least `3` (`IsDecomposition.hasGirthAtLeast_three`):
  two distinct blocks share at most `r - 1` vertices;
* every `K_q^2`-decomposition has girth at least `4` (`IsDecomposition.hasGirthAtLeast_four`):
  three blocks pairwise sharing at most one vertex span at least `3q - 3` vertices.

Together with the Existence Conjecture (proved in `RequestProject/Multigraph/Existence.lean`) this
proves the High Girth Existence Conjecture 5.3 for `g = 3`, and for `g ≤ 4` when `r = 2`
(`highGirthExistence_small`), and hence Erdős' Conjecture 5.1 for `g ≤ 4`
(`erdosHighGirth_small`).  The cases of larger girth are the actual content of these
conjectures (theorems of Kwan–Sah–Sawhney–Simkin and of Delcourt–Postle) and are not proved here.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {V : Type*} [DecidableEq V]

/-- In a decomposition, two distinct blocks share fewer than `r` vertices. -/
theorem IsDecomposition.card_inter_lt {q r : ℕ} {G 𝒮 : Finset (Finset V)}
    (h : IsDecomposition q r G 𝒮) {B₁ B₂ : Finset V} (h₁ : B₁ ∈ 𝒮) (h₂ : B₂ ∈ 𝒮)
    (hne : B₁ ≠ B₂) : (B₁ ∩ B₂).card < r := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hlt
  have h1 := h.mult_eq T hTc
  have h2 : 2 ≤ cliqueMult 𝒮 T := by
    unfold cliqueMult
    have : ({B₁, B₂} : Finset (Finset V)) ⊆ 𝒮.filter (fun Q => T ⊆ Q) := by
      intro B hB
      rcases mem_insert.1 hB with rfl | hB
      · exact mem_filter.2 ⟨h₁, hT.trans inter_subset_left⟩
      · rw [mem_singleton.1 hB]; exact mem_filter.2 ⟨h₂, hT.trans inter_subset_right⟩
    exact (card_pair hne).symm.le.trans (card_le_card this)
  split_ifs at h1 <;> omega

theorem vertexSet_pair (B₁ B₂ : Finset V) : vertexSet ({B₁, B₂} : Finset (Finset V)) = B₁ ∪ B₂ := by
  simp [vertexSet]

theorem vertexSet_triple (B₁ B₂ B₃ : Finset V) :
    vertexSet ({B₁, B₂, B₃} : Finset (Finset V)) = B₁ ∪ (B₂ ∪ B₃) := by
  simp [vertexSet]

/-- **Every `K_q^r`-decomposition has girth at least `3`.** -/
theorem IsDecomposition.hasGirthAtLeast_three {q r : ℕ} (hrq : r ≤ q) {G 𝒮 : Finset (Finset V)}
    (h : IsDecomposition q r G 𝒮) : HasGirthAtLeast q r 3 𝒮 := by
  intro i hi2 hi3 𝒞 ⟨h𝒞, hcard, hvert⟩
  obtain rfl : i = 2 := by omega
  obtain ⟨B₁, B₂, hne, rfl⟩ := card_eq_two.1 hcard
  have h₁ : B₁ ∈ 𝒮 := h𝒞 (mem_insert_self _ _)
  have h₂ : B₂ ∈ 𝒮 := h𝒞 (mem_insert_of_mem (mem_singleton_self _))
  have hi := h.card_inter_lt h₁ h₂ hne
  rw [vertexSet_pair] at hvert
  have hu := card_union_add_card_inter B₁ B₂
  rw [h.card_eq B₁ h₁, h.card_eq B₂ h₂] at hu
  have : (q - r) * 2 + r = 2 * q - r := by omega
  omega

/-- **Every `K_q^2`-decomposition has girth at least `4`.** -/
theorem IsDecomposition.hasGirthAtLeast_four {q : ℕ} (hq : 2 ≤ q) {G 𝒮 : Finset (Finset V)}
    (h : IsDecomposition q 2 G 𝒮) : HasGirthAtLeast q 2 4 𝒮 := by
  intro i hi2 hi4 𝒞 h𝒞'
  rcases (show i = 2 ∨ i = 3 by omega) with rfl | rfl
  · exact h.hasGirthAtLeast_three hq 2 le_rfl (by norm_num) 𝒞 h𝒞'
  obtain ⟨h𝒞, hcard, hvert⟩ := h𝒞'
  obtain ⟨B₁, B₂, B₃, h12, h13, h23, rfl⟩ := card_eq_three.1 hcard
  have h₁ : B₁ ∈ 𝒮 := h𝒞 (mem_insert_self _ _)
  have h₂ : B₂ ∈ 𝒮 := h𝒞 (mem_insert_of_mem (mem_insert_self _ _))
  have h₃ : B₃ ∈ 𝒮 := h𝒞 (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
  have i12 := h.card_inter_lt h₁ h₂ h12
  have i13 := h.card_inter_lt h₁ h₃ h13
  have i23 := h.card_inter_lt h₂ h₃ h23
  rw [vertexSet_triple] at hvert
  have c1 := h.card_eq B₁ h₁
  have c2 := h.card_eq B₂ h₂
  have c3 := h.card_eq B₃ h₃
  have u23 := card_union_add_card_inter B₂ B₃
  have u := card_union_add_card_inter B₁ (B₂ ∪ B₃)
  have hint : (B₁ ∩ (B₂ ∪ B₃)).card ≤ (B₁ ∩ B₂).card + (B₁ ∩ B₃).card := by
    rw [inter_union_distrib_left]; exact card_union_le _ _
  have : (q - 2) * 3 + 2 = 3 * q - 4 := by omega
  omega

/-- **The High Girth Existence Conjecture 5.3 for small girth**: for `g = 3`, and for `g ≤ 4`
when `r = 2`. -/
theorem highGirthExistence_small : ∀ q r g : ℕ, 2 ≤ r → r < q → 3 ≤ g → (g = 3 ∨ (r = 2 ∧ g ≤ 4)) →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, IsDivisible q r (completeRGraph (Fin n) r) →
      ∃ 𝒮, IsDecomposition q r (completeRGraph (Fin n) r) 𝒮 ∧ HasGirthAtLeast q r g 𝒮 := by
  intro q r g hr hrq hg hsmall
  obtain ⟨n₀, hn₀⟩ := existenceConjecture_proved.steiner q r hr hrq
  refine ⟨n₀, fun n hn hdiv => ?_⟩
  obtain ⟨𝒮, h𝒮⟩ := hn₀ n hn (isDivisible_completeRGraph_iff.1 hdiv)
  have hdec := isSteinerSystem_iff_isDecomposition.1 h𝒮
  refine ⟨𝒮, hdec, ?_⟩
  rcases hsmall with rfl | ⟨rfl, hg4⟩
  · exact hdec.hasGirthAtLeast_three hrq.le
  · intro i hi2 hig 𝒞
    exact hdec.hasGirthAtLeast_four (by omega) i hi2 (by omega) 𝒞

/-- **Erdős' Conjecture 5.1 for `g ≤ 4`.** -/
theorem erdosHighGirth_small : ∀ g : ℕ, 3 ≤ g → g ≤ 4 → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    IsDivisible 3 2 (completeRGraph (Fin n) 2) →
      ∃ 𝒮, IsDecomposition 3 2 (completeRGraph (Fin n) 2) 𝒮 ∧ HasGirthAtLeast 3 2 g 𝒮 :=
  fun g hg hg4 => highGirthExistence_small 3 2 g le_rfl (by norm_num) hg (Or.inr ⟨rfl, hg4⟩)

end RefinedAbsorption
