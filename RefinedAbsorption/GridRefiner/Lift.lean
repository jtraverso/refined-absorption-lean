module
public import RefinedAbsorption.LocalRefiner.Segments

/-!
# Lifting label-level residual refiners

Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

The stages of the grid refiner (`RequestProject/GridRefiner/`) are described at the level of
*labels*: every label stands for a small multigraph given by segments (`LocalRefiner.Segments`),
and pieces are sets of labels.  The labels that are inputs of a stage are *single copies*.

`lift_residual` turns such a label-level description into an `IsResidualMultiRefiner` on the
copies.  The divisibility of the residue does not have to be checked by hand: it follows from the
divisibility of the reservoir, of the input and of the pieces (`divisible_of_partition`).
-/

@[expose] public section

namespace RefinedAbsorption.GridRefiner

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner

section Partition

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- Degrees are additive over a pairwise disjoint family. -/
lemma mdeg_sup_eq_sum (ends : E → Finset V) (𝒰 : Finset (Finset E))
    (h𝒰 : (𝒰 : Set (Finset E)).PairwiseDisjoint id) (S : Finset V) :
    mdeg ends (𝒰.sup id) S = ∑ W ∈ 𝒰, mdeg ends W S := by
  rw [Finset.sup_eq_biUnion]
  unfold mdeg
  rw [filter_biUnion, card_biUnion]
  · rfl
  · intro W hW W' hW' hne
    exact disjoint_filter_filter (h𝒰 hW hW' hne)

/-- **Divisibility of a residue.**  If a divisible multigraph is the disjoint union of pairwise
disjoint divisible pieces and of a residue, the residue is divisible. -/
lemma divisible_of_partition {q r : ℕ} {ends : E → Finset V} {A Res : Finset E}
    {𝒰 : Finset (Finset E)} (hA : MIsDivisible q r ends A)
    (h𝒰 : (𝒰 : Set (Finset E)).PairwiseDisjoint id) (hW : ∀ W ∈ 𝒰, MIsDivisible q r ends W)
    (hd : Disjoint (𝒰.sup id) Res) (heq : 𝒰.sup id ∪ Res = A) :
    MIsDivisible q r ends Res := by
  intro S hS
  have h1 := hA S hS
  rw [← heq, mdeg_union_of_disjoint ends hd, mdeg_sup_eq_sum ends 𝒰 h𝒰] at h1
  have h2 : (q - S.card).choose (r - S.card) ∣ ∑ W ∈ 𝒰, mdeg ends W S :=
    Finset.dvd_sum fun W hW' => hW W hW' S hS
  exact (Nat.dvd_add_right h2).1 h1

end Partition

variable {Λ V : Type} [DecidableEq Λ] [DecidableEq V]

omit [DecidableEq V] in
/-- The lift of a set of single-copy labels. -/
lemma liftS_single {sg : Λ → List (Finset V × ℕ)} {pe : Λ → Finset V} {I : Finset Λ}
    (hI : ∀ ℓ ∈ I, sg ℓ = [(pe ℓ, 1)]) {c : Λ × ℕ × ℕ} :
    c ∈ liftS sg I ↔ c.1 ∈ I ∧ c.2.1 = 0 ∧ c.2.2 = 0 := by
  rw [mem_liftS]
  constructor
  · rintro ⟨h0, h1, h2⟩
    rw [hI _ h0] at h1
    simp only [List.length_singleton, Nat.lt_one_iff] at h1
    rw [segAt, hI _ h0, h1] at h2
    simp only [List.getD_cons_zero, Nat.lt_one_iff] at h2
    exact ⟨h0, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, ?_, ?_⟩
    · rw [hI _ h0, h1]; simp
    · rw [segAt, hI _ h0, h1, h2]; simp

/-- **Lifting a label-level residual refiner.**  Inputs are single copies (`hI`), every segment is
a `2`-set, the pieces are divisible after lifting, the reservoir is divisible after lifting, and
every input subset `Ls` whose lift is divisible admits a decomposition of `Rl ∪ Ls` into pairwise
disjoint pieces and a residue inside `Yl`.  Then the lifts form a residual multi-refiner. -/
theorem lift_residual {q C : ℕ} (sg : Λ → List (Finset V × ℕ)) (pe : Λ → Finset V)
    {I Rl Yl : Finset Λ} {Wl : Finset (Finset Λ)}
    (hI : ∀ ℓ ∈ I, sg ℓ = [(pe ℓ, 1)])
    (hrg : ∀ ℓ ∈ I ∪ Rl, ∀ s ∈ sg ℓ, s.1.card = 2)
    (hdj : Disjoint I Rl)
    (hdv : ∀ P ∈ Wl, MIsDivisible q 2 (cpEnds sg) (liftS sg P))
    (hsb : ∀ P ∈ Wl, P ⊆ I ∪ Rl)
    (hcd : ∀ P ∈ Wl, (liftS sg P).card ≤ C)
    (hml : ∀ ℓ, (Wl.filter (ℓ ∈ ·)).card ≤ C)
    (hRd : MIsDivisible q 2 (cpEnds sg) (liftS sg Rl))
    (hdc : ∀ Ls ⊆ I, MIsDivisible q 2 (cpEnds sg) (liftS sg Ls) → ∃ 𝒰 ⊆ Wl, ∃ Res ⊆ Yl,
      (𝒰 : Set (Finset Λ)).PairwiseDisjoint id ∧ Disjoint (𝒰.sup id) Res ∧
        𝒰.sup id ∪ Res = Rl ∪ Ls) :
    IsResidualMultiRefiner q 2 C (cpEnds sg) (liftS sg I) (liftS sg Rl) (liftS sg Yl)
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
    have hA : MIsDivisible q 2 (cpEnds sg) (liftS sg Rl ∪ L) := by
      rw [hLeq]
      exact MIsDivisible.union (disjoint_liftS (disjoint_of_subset_left hLsI hdj).symm) hRd hdiv
    refine divisible_of_partition hA hpw' ?_ hd' heq'
    intro W hW
    obtain ⟨P, hP, rfl⟩ := mem_image.1 hW
    exact hdv P (h𝒰 hP)

end RefinedAbsorption.GridRefiner
