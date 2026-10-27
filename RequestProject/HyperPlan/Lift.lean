module
public import RequestProject.GridRefiner.Lift

/-!
# Lifting label-level residual refiners, uniformity `r`

`lift_residualR` is `GridRefiner.lift_residual` for every uniformity `r` (same proof).
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner

variable {Λ V : Type} [DecidableEq Λ] [DecidableEq V]

/-- **Lifting a label-level residual refiner.**  Inputs are single copies (`hI`), every segment is
an `r`-set, the pieces are divisible after lifting, the reservoir is divisible after lifting, and
every input subset `Ls` whose lift is divisible admits a decomposition of `Rl ∪ Ls` into pairwise
disjoint pieces and a residue inside `Yl`.  Then the lifts form a residual multi-refiner. -/
theorem lift_residualR {q r C : ℕ} (sg : Λ → List (Finset V × ℕ)) (pe : Λ → Finset V)
    {I Rl Yl : Finset Λ} {Wl : Finset (Finset Λ)}
    (hI : ∀ ℓ ∈ I, sg ℓ = [(pe ℓ, 1)])
    (hrg : ∀ ℓ ∈ I ∪ Rl, ∀ s ∈ sg ℓ, s.1.card = r)
    (hdj : Disjoint I Rl)
    (hdv : ∀ P ∈ Wl, MIsDivisible q r (cpEnds sg) (liftS sg P))
    (hsb : ∀ P ∈ Wl, P ⊆ I ∪ Rl)
    (hcd : ∀ P ∈ Wl, (liftS sg P).card ≤ C)
    (hml : ∀ ℓ, (Wl.filter (ℓ ∈ ·)).card ≤ C)
    (hRd : MIsDivisible q r (cpEnds sg) (liftS sg Rl))
    (hdc : ∀ Ls ⊆ I, MIsDivisible q r (cpEnds sg) (liftS sg Ls) → ∃ 𝒰 ⊆ Wl, ∃ Res ⊆ Yl,
      (𝒰 : Set (Finset Λ)).PairwiseDisjoint id ∧ Disjoint (𝒰.sup id) Res ∧
        𝒰.sup id ∪ Res = Rl ∪ Ls) :
    IsResidualMultiRefiner q r C (cpEnds sg) (liftS sg I) (liftS sg Rl) (liftS sg Yl)
      (Wl.image (liftS sg)) := by
  refine ⟨?_, disjoint_liftS hdj, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rw [← liftS_union] at hc
    exact hrg _ (mem_liftS.1 hc).1 _ (cpEnds_mem_of_mem_liftS hc)
  · intro W hW
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    exact hdv P hP
  · intro W hW
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    rw [← liftS_union]
    exact liftS_mono (hsb P hP)
  · intro W hW
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    exact hcd P hP
  · intro c _
    have hsub : (Wl.image (liftS sg)).filter (fun W => c ∈ W) ⊆
        (Wl.filter (c.1 ∈ ·)).image (liftS sg) := by
      intro W hW
      rw [mem_filter] at hW
      obtain ⟨hW, hc⟩ := hW
      obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
      exact mem_image.2 ⟨P, mem_filter.2 ⟨hP, (mem_liftS.1 hc).1⟩, rfl⟩
    exact (card_le_card hsub).trans (card_image_le.trans (hml c.1))
  · intro L hL hdiv
    set Ls := I.filter (fun ℓ => (ℓ, 0, 0) ∈ L) with hLs
    have hLsI : Ls ⊆ I := filter_subset _ _
    have hLeq : L = liftS sg Ls := by
      ext c
      rw [liftS_single (fun ℓ hℓ => hI ℓ (hLsI hℓ)), hLs, mem_filter]
      constructor
      · intro hc
        obtain ⟨h0, h1, h2⟩ := (liftS_single hI).1 (hL hc)
        obtain ⟨ℓ, s, t⟩ := c
        simp only at h0 h1 h2
        subst h1; subst h2
        exact ⟨⟨h0, hc⟩, rfl, rfl⟩
      · rintro ⟨⟨_, h⟩, h1, h2⟩
        obtain ⟨ℓ, s, t⟩ := c
        simp only at h h1 h2
        subst h1; subst h2
        exact h
    rw [hLeq] at hdiv
    obtain ⟨𝒰, h𝒰, Res, hRes, hpw, hd, heq⟩ := hdc Ls hLsI hdiv
    have hpw' : ((𝒰.image (liftS sg) : Finset (Finset (Λ × ℕ × ℕ))) :
        Set (Finset (Λ × ℕ × ℕ))).PairwiseDisjoint id := by
      intro W hW W' hW' hne
      simp only [coe_image, Set.mem_image, mem_coe] at hW hW'
      obtain ⟨P, hP, rfl⟩ := hW
      obtain ⟨P', hP', rfl⟩ := hW'
      have hPP : P ≠ P' := fun h => hne (by rw [h])
      exact disjoint_liftS (hpw hP hP' hPP)
    have hsup := liftS_sup (sg := sg) 𝒰
    have hd' : Disjoint ((𝒰.image (liftS sg)).sup id) (liftS sg Res) := by
      rw [hsup]; exact disjoint_liftS hd
    have heq' : (𝒰.image (liftS sg)).sup id ∪ liftS sg Res = liftS sg Rl ∪ L := by
      rw [hsup, ← liftS_union, heq, liftS_union, hLeq]
    refine ⟨𝒰.image (liftS sg), image_subset_image h𝒰, liftS sg Res, liftS_mono hRes, ?_, hpw',
      hd', heq'⟩
    have hA : MIsDivisible q r (cpEnds sg) (liftS sg Rl ∪ L) := by
      rw [hLeq]
      exact MIsDivisible.union (disjoint_liftS (disjoint_of_subset_left hLsI hdj).symm) hRd hdiv
    refine divisible_of_partition hA hpw' ?_ hd' heq'
    intro W hW
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    exact hdv P (h𝒰 hP)

end RefinedAbsorption.HyperPlan
