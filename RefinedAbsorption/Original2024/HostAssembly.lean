module
public import RefinedAbsorption.Original2024.HostReduction
public import RefinedAbsorption.Placement.Assembly

/-!
# Refiners with attached absorbers avoiding a forbidden graph

From a strong multi-refiner on `Fin n` we build, inside `Fin n`, a strong simple refiner of the
image of `X` together with bounded attached absorbers, such that *no* placed edge (neither of the
refiner nor of an absorber) lies in a forbidden `r`-graph `F`.  Taking for `F` the complement of
a host graph `G ⊇ X` with `δ_{r-1}(G) ≥ (1 - ε) n` puts everything inside `G`: this is the
step that turns the complete-host construction into the host versions of Theorems 1.11 and 1.7
of Delcourt–Postle.
-/

@[expose] public section

namespace RefinedAbsorption.Original2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Absorber17 RefinedAbsorption.Placement

/-- Strong refiners are monotone in the constant. -/
theorem IsStrongRefiner.mono_C {q r C C' n : ℕ} {X R : Finset (Finset (Fin n))}
    {𝒲 : Finset (Finset (Finset (Fin n)))} {D : ℕ} (h : IsStrongRefiner q r C X R 𝒲 D)
    (hC : C ≤ C') : IsStrongRefiner q r C' X R 𝒲 D :=
  ⟨h.refiner.mono hC, h.oneX, h.degX,
    fun S hS => (h.degR S hS).trans (Nat.mul_le_mul_right _ hC),
    fun S hS => (h.pieceDeg S hS).trans (Nat.mul_le_mul_right _ hC)⟩

/-- **Refiner and absorbers avoiding `F`, inside `Fin n`.** -/
theorem hostRefinerAbsorbers {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) (C : ℕ) (hC : 1 ≤ C) :
    ∃ B Cf : ℕ, 1 ≤ Cf ∧ ∀ (n : ℕ) {E : Type*} [DecidableEq E] (ends : E → Finset (Fin n))
      (K X R : Finset E) (𝒲 : Finset (Finset E)) (D : ℕ) (F : Finset (Finset (Fin n))),
      IsStrongMultiRefiner q r C ends K X R 𝒲 D → Cf * D ≤ n →
      (∀ S : Finset (Fin n), S.card = r - 1 → Cf * (D + deg F S) ≤ n) → 0 < n →
      ∃ (R' : Finset (Finset (Fin n))) (𝒲' : Finset (Finset (Finset (Fin n))))
        (A Qon Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
        IsStrongRefiner q r Cf (X.image ends) R' 𝒲' D ∧ Disjoint R' F ∧
        IsAttachedAbsorbers q r (X.image ends) R' 𝒲' A Qon Qoff ∧
        (∀ W ∈ 𝒲', Disjoint (A W) F) ∧
        (∀ W ∈ 𝒲', IsBoundedAbsorber q r B W (A W) (Qon W) (Qoff W)) ∧
        ∀ S : Finset (Fin n), S.card = r - 1 → deg (R' ∪ 𝒲'.sup A) S ≤ Cf * D := by
  obtain ⟨C', hC', hred⟩ := placedMultiplicityReductionHost hr hrq C hC
  obtain ⟨B, Ca, hCa, habs⟩ := placedAttachedAbsorbers (by omega : 1 ≤ r) hrq C'
  set Cf := C' + Ca * (1 + C') + 1 with hCf
  refine ⟨B, Cf, by omega, ?_⟩
  intro n E _ ends K X R 𝒲 D F hS hD hFdeg hn
  have hC'D : C' * D ≤ n := (Nat.mul_le_mul_right _ (by omega)).trans hD
  have hFC' : ∀ S : Finset (Fin n), S.card = r - 1 → C' * (D + deg F S) ≤ n := fun S hS' =>
    (Nat.mul_le_mul_right _ (by omega)).trans (hFdeg S hS')
  obtain ⟨R', 𝒲', hS', hR'F⟩ := hred n ends X R 𝒲 D F (IsStrongMultiRefiner.keepX hS) hC'D hFC' hn
  have hR := hS'.refiner
  -- the forbidden graph for the absorbers: `X ∪ (R' ∪ F)`
  have hdegG : ∀ S : Finset (Fin n), S.card = r - 1 →
      Ca * deg (X.image ends ∪ (R' ∪ F)) S ≤ n := by
    intro S hS''
    have h1 : deg (X.image ends ∪ (R' ∪ F)) S ≤
        deg (X.image ends) S + (deg R' S + deg F S) := by
      unfold deg; rw [filter_union, filter_union]
      exact (card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _)
    have h2 := hS'.degX S hS''
    have h3 := hS'.degR S hS''
    refine le_trans (Nat.mul_le_mul_left _ h1) (le_trans ?_ (hFdeg S hS''))
    have : Ca * (D + (C' * D + deg F S)) ≤ Cf * (D + deg F S) := by
      have e : Ca * (D + (C' * D + deg F S)) + ((C' + 1) * (D + deg F S) + Ca * C' * deg F S) =
          Cf * (D + deg F S) := by simp only [hCf]; ring
      omega
    calc Ca * (deg (X.image ends) S + (deg R' S + deg F S))
        ≤ Ca * (D + (C' * D + deg F S)) := by gcongr
      _ ≤ _ := this
  have hCaD : Ca * (C' * D) ≤ n := by
    refine le_trans ?_ hD
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by simp only [hCf]; nlinarith)
  obtain ⟨A, Qon, Qoff, hA, hbd, hdeg⟩ := habs n (X.image ends) (R' ∪ F) 𝒲' (C' * D)
    (fun W hW e he => hR.rgraph e (hR.subset W hW he)) hR.divisible hR.card_le
    hdegG hS'.pieceDeg hCaD hn
  refine ⟨R', 𝒲', A, Qon, Qoff, IsStrongRefiner.mono_C hS' (by omega), hR'F, ⟨hA.rgraph, ?_, hA.pairwise,
    hA.on, hA.off⟩, ?_, hbd, ?_⟩
  · intro W hW
    exact disjoint_of_subset_right (union_subset_union subset_rfl subset_union_left)
      (hA.disjoint W hW)
  · intro W hW
    exact disjoint_of_subset_right (subset_union_right.trans subset_union_right)
      (hA.disjoint W hW)
  · intro S hS''
    have h1 : deg (R' ∪ 𝒲'.sup A) S ≤ deg R' S + deg (𝒲'.sup A) S := by
      unfold deg; rw [filter_union]; exact card_union_le _ _
    have h2 := hS'.degR S hS''
    have h3 := hdeg S hS''
    calc deg (R' ∪ 𝒲'.sup A) S ≤ C' * D + Ca * (C' * D) := h1.trans (Nat.add_le_add h2 h3)
      _ ≤ Cf * D := by simp only [hCf]; nlinarith

end RefinedAbsorption.Original2024
