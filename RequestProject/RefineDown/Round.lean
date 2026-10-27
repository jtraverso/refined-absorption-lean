module
public import RequestProject.RefineDown.RoundGadget

/-!
# One placed refine-down round inside `Fin n`

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855.  Lean formalization: Juan Pablo
Traverso Gianini, Apache-2.0.

`placedRound`: the anti-edge step (`RefineDown.antiEdgeStep`) with all its new vertices placed
inside the same `Fin n` by the clustered Partial Clique Embedding Lemma (`clusteredPlacement`).
No embedding or refiner provider is assumed: the application conditions of Lemma 5.2 are derived
from the input degree bound.  The output satisfies the one-round invariant `RoundSpec`:

* `R` is a residual multi-refiner of `X` with residue in `Y ⊆ R` (divisible residues, pieces of
  uniformly bounded size, every copy in boundedly many pieces);
* the new copies carry the round tag `k + 1`, are simple (`Prod.snd` is injective on `R`) and
  avoid the forbidden host `G`;
* every piece contains at most one copy of `X`;
* `Δ_{r-1}(R) ≤ C · D` and the vertex sets of the pieces have `(r-1)`-degree `≤ C · D`.

Since `Y ⊆ R` is simple with `Δ_{r-1}(Y) ≤ C · D`, the residue is again an admissible input
(flatness needed to continue).
-/

@[expose] public section

namespace RefinedAbsorption.RefineDown

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement

/-- **The one-round invariant.** -/
structure RoundSpec (q r C : ℕ) {n : ℕ} (k : ℕ) (X : Finset (Lab n))
    (G : Finset (Finset (Fin n))) (D : ℕ) (R Y : Finset (Lab n)) (𝒲 : Finset (Finset (Lab n))) :
    Prop where
  refiner : IsResidualMultiRefiner q r C labEnds X R Y 𝒲
  residue_sub : Y ⊆ R
  tag : ∀ c ∈ R, c.1 = k + 1
  simple : Set.InjOn labEnds (R : Set (Lab n))
  avoid : ∀ c ∈ R, c.2 ∉ G
  oneX : ∀ W ∈ 𝒲, (W.filter (· ∈ X)).card ≤ 1
  degR : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg labEnds R S ≤ C * D
  pieceDeg : ∀ S : Finset (Fin n), S.card = r - 1 →
    (𝒲.filter fun W => S ⊆ W.biUnion labEnds).card ≤ C * D

theorem one_le_fakeCount {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) : 1 ≤ fakeCount q r := by
  unfold fakeCount fakeModulus
  have h0 : 2 ≤ q.choose r := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Nat.choose_succ_succ']
    have := Nat.choose_pos (show r' ≤ q' by omega)
    have := Nat.choose_pos (show r' + 1 ≤ q' by omega)
    omega
  have : (q - 0).choose (r - 0) ≤ ∏ s ∈ range r, (q - s).choose (r - s) :=
    Finset.single_le_prod' (f := fun s => (q - s).choose (r - s))
      (fun s hs => Nat.choose_pos (by have := mem_range.1 hs; omega)) (mem_range.2 (by omega))
  simp only [Nat.sub_zero] at this
  omega

variable {n q r : ℕ}

theorem mem_stepR_iff {j₀ : Fin (fakeCount q r)} {X : Finset (Lab n)}
    {c : SC (Fin n) (Lab n) q r} :
    c ∈ stepR q r labEnds j₀ X ↔ ∃ f, c = Sum.inr f ∧ ∃ i ∈ X, f ∈ Ed q r j₀ i := by
  rcases c with i | f
  · simp [stepR]
  · simp [stepR, Ed]

theorem image_liftE_psiV (Φ : Lab n → Fin (roundAux q r) → Fin n) (c : Lab n) :
    (liftE q r labEnds c).image (psiV Φ) = c.2 := by
  ext v
  simp [liftE, lift, ends2, psiV]

set_option maxHeartbeats 1000000 in
/-- **One placed refine-down round.**  For `1 ≤ r < q` there is `C ≥ 1` such that every labelled
`r`-multigraph `X` on `Fin n` (tags `≤ k`) with `Δ_{r-1}(X) ≤ D`, every forbidden host `G` with
`C · Δ_{r-1}(G) ≤ n`, and `C · D ≤ n`, have a round output satisfying `RoundSpec`, with all new
vertices placed inside `Fin n`. -/
theorem placedRound {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (n k : ℕ) (X : Finset (Lab n)) (G : Finset (Finset (Fin n))) (D : ℕ),
      (∀ c ∈ X, c.1 ≤ k) → MIsRGraph r labEnds X →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg labEnds X S ≤ D) →
      (∀ S : Finset (Fin n), S.card = r - 1 → C * deg G S ≤ n) → C * D ≤ n → 0 < n →
      ∃ (R Y : Finset (Lab n)) (𝒲 : Finset (Finset (Lab n))), RoundSpec q r C k X G D R Y 𝒲 := by
  classical
  obtain ⟨Ccl, hCcl, hcl⟩ := clusteredPlacement r (roundAux q r) r r 1
  set C₀ := (fakeCount q r + 1) * q.choose r + 2 with hC₀
  refine ⟨C₀ + 2 * Ccl + 1, by omega, ?_⟩
  intro n k X G D hXk hXr hXD hG hD hn
  have j₀ : Fin (fakeCount q r) := ⟨0, one_le_fakeCount hr hrq⟩
  -- placement of the round gadgets
  obtain ⟨Φ, hvalid, hdisj, hhost, hdeg, hpdeg⟩ := hcl n X (fun i => i.2)
    (roundTemplate q r j₀) X (fun i => i.2) (fun i => {i}) G D
    (fun i hi => roundTemplate_wf (hXr i hi))
    (fun p hp => ⟨(hXr p hp).le, by beta_reduce; rw [hXr p hp]; omega, by simp⟩)
    (fun i hi => by
      refine (card_le_card (t := {i}) fun p hp => ?_).trans (by simp)
      simp only [mem_filter, mem_singleton] at hp; simp [hp.2])
    (fun i hi => ⟨i, hi, mem_singleton_self _, subset_rfl⟩)
    (fun S hS => le_trans (Nat.mul_le_mul_right _ (by omega)) (hG S hS))
    (fun S hS => hXD S hS)
    (le_trans (Nat.mul_le_mul_right _ (by omega)) hD) hn
  -- the abstract step
  have hA := antiEdgeStep (V := Fin n) (ends := labEnds) hrq j₀ X hXr
  set ψ := psiV (q := q) (r := r) Φ
  have hYR : stepY q r labEnds X ⊆ X.map Function.Embedding.inl ∪ stepR q r labEnds j₀ X := by
    intro c hc
    refine mem_union_right _ ?_
    obtain ⟨f, hf, rfl⟩ := mem_map.1 hc
    obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
    exact mem_stepR_iff.2 ⟨f, rfl, i, hi, mem_union_right _ hfi⟩
  have hinj : ∀ c ∈ X.map Function.Embedding.inl ∪ stepR q r labEnds j₀ X,
      Set.InjOn ψ (sends q r labEnds c) := by
    intro c hc
    rcases c with i | f
    · intro x hx y hy hxy
      obtain ⟨v, -, rfl⟩ := mem_map.1 (mem_coe.1 hx)
      obtain ⟨w, -, rfl⟩ := mem_map.1 (mem_coe.1 hy)
      simpa [ψ, psiV] using hxy
    · rcases mem_union.1 hc with hc | hc
      · simp at hc
      · obtain ⟨f', hf', i, hi, hfi⟩ := mem_stepR_iff.1 hc
        cases hf'
        exact psiV_injOn_edge (hvalid i hi) hfi
  have hinjX : Set.InjOn ψ ((X.map Function.Embedding.inl).biUnion (sends q r labEnds)) := by
    intro x hx y hy hxy
    obtain ⟨c, hc, hxc⟩ := mem_biUnion.1 (mem_coe.1 hx)
    obtain ⟨c', hc', hyc'⟩ := mem_biUnion.1 (mem_coe.1 hy)
    obtain ⟨i, -, rfl⟩ := mem_map.1 hc
    obtain ⟨i', -, rfl⟩ := mem_map.1 hc'
    obtain ⟨v, -, rfl⟩ := mem_map.1 hxc
    obtain ⟨w, -, rfl⟩ := mem_map.1 hyc'
    simpa [ψ, psiV] using hxy
  have hB := residual_mapEnds hA ψ hinj hinjX hYR
  -- renaming the copies
  have hnewE : ∀ i ∈ X, ∀ f ∈ Ed q r j₀ i, f.image ψ ∈ newEdges (roundTemplate q r j₀ i) (Φ i) := by
    intro i _ f hf
    rw [newEdges_roundTemplate]
    exact mem_image_of_mem _ hf
  let g : SC (Fin n) (Lab n) q r → Lab n :=
    Sum.elim (fun i => i) (fun f => ((k + 1 : ℕ), f.image ψ))
  have hends : ∀ c ∈ X.map Function.Embedding.inl ∪ stepR q r labEnds j₀ X,
      labEnds (g c) = mapEnds ψ (sends q r labEnds) c := by
    intro c _
    rcases c with i | f
    · exact (image_liftE_psiV Φ i).symm
    · rfl
  have hg : Set.InjOn g ↑(X.map Function.Embedding.inl ∪ stepR q r labEnds j₀ X) := by
    intro c hc c' hc' hcc'
    have hc := mem_coe.1 hc
    have hc' := mem_coe.1 hc'
    rcases c with i | f <;> rcases c' with i' | f'
    · simpa [g] using hcc'
    · exfalso
      rcases mem_union.1 hc with hc | hc
      · obtain ⟨i₀, hi₀, he⟩ := mem_map.1 hc
        have hii : i₀ = _ := Sum.inl_injective he
        rw [hii] at hi₀
        have := hXk _ hi₀
        have h1 := congrArg Prod.fst hcc'
        simp only [g, Sum.elim_inl, Sum.elim_inr] at h1
        omega
      · obtain ⟨_, he, -⟩ := mem_stepR_iff.1 hc; cases he
    · exfalso
      rcases mem_union.1 hc' with hc' | hc'
      · obtain ⟨i₀, hi₀, he⟩ := mem_map.1 hc'
        have hii : i₀ = _ := Sum.inl_injective he
        rw [hii] at hi₀
        have := hXk _ hi₀
        have h1 := congrArg Prod.fst hcc'
        simp only [g, Sum.elim_inl, Sum.elim_inr] at h1
        omega
      · obtain ⟨_, he, -⟩ := mem_stepR_iff.1 hc'; cases he
    · have hc := (mem_union.1 hc).resolve_left (by simp)
      have hc' := (mem_union.1 hc').resolve_left (by simp)
      obtain ⟨_, he, i, hi, hfi⟩ := mem_stepR_iff.1 hc; cases he
      obtain ⟨_, he', i', hi', hfi'⟩ := mem_stepR_iff.1 hc'; cases he'
      have himg : f.image ψ = f'.image ψ := congrArg Prod.snd hcc'
      by_cases hii : i = i'
      · subst hii
        rw [psiV_image_injOn (hXr i hi) (hvalid i hi) hfi hfi' himg]
      · exfalso
        exact disjoint_left.1 (hdisj i hi i' hi' hii) (hnewE i hi f hfi)
          (himg ▸ hnewE i' hi' f' hfi')
  have hC := residual_relabel hB g labEnds hends hg hYR
  have hXg : (X.map Function.Embedding.inl).image g = X := by
    ext c
    constructor
    · intro hc
      obtain ⟨c', hc', rfl⟩ := mem_image.1 hc
      obtain ⟨i, hi, rfl⟩ := mem_map.1 hc'
      exact hi
    · intro hc
      exact mem_image.2 ⟨Sum.inl c, mem_map_of_mem _ hc, rfl⟩
  rw [hXg] at hC
  have hYsub : stepY q r labEnds X ⊆ stepR q r labEnds j₀ X := by
    intro c hc
    obtain ⟨f, hf, rfl⟩ := mem_map.1 hc
    obtain ⟨i, hi, hfi⟩ := mem_biUnion.1 hf
    exact mem_stepR_iff.2 ⟨f, rfl, i, hi, mem_union_right _ hfi⟩
  have hRg : ∀ c ∈ (stepR q r labEnds j₀ X).image g,
      ∃ i ∈ X, ∃ f ∈ Ed q r j₀ i, c = ((k + 1 : ℕ), f.image ψ) := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := mem_image.1 hc
    obtain ⟨f, rfl, i, hi, hfi⟩ := mem_stepR_iff.1 hc'
    exact ⟨i, hi, f, hfi, rfl⟩
  have hsubpv : ∀ i ∈ X, ∀ f ∈ Ed q r j₀ i, f.image ψ ⊆ i.2 ∪ auxImage (Φ i) := by
    intro i hi f hf
    rw [← placeEdge_image_betaV hf]
    exact placeEdge_subset (roundTemplate_wf (j₀ := j₀) (hXr i hi)) (Φ i)
      (mem_image_of_mem _ hf)
  have hpv : ∀ i ∈ X, pvOf (fun i : Lab n => i.2) (fun i => {i}) Φ X i = i.2 ∪ auxImage (Φ i) := by
    intro i hi
    unfold pvOf
    rw [filter_singleton, if_pos hi, singleton_biUnion]
  have hpieceV : ∀ i ∈ X, ∀ W₀, (W₀ = pieceP q r labEnds j₀ i ∨ W₀ = pieceQ q r labEnds j₀ i) →
      (W₀.image g).biUnion labEnds ⊆ i.2 ∪ auxImage (Φ i) := by
    intro i hi W₀ hW₀ v hv
    obtain ⟨x, hx, hvx⟩ := mem_biUnion.1 hv
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
    rcases c with i' | f
    · have : i' = i := by
        rcases hW₀ with rfl | rfl
        · exact mem_pieceP_inl.1 hc
        · exact absurd hc not_mem_pieceQ_inl
      subst this
      exact mem_union_left _ hvx
    · have hf : f ∈ Ed q r j₀ i := by
        rcases hW₀ with rfl | rfl
        · exact mem_union_left _ (mem_pieceP_inr.1 hc)
        · exact mem_union.2 (mem_pieceQ_inr.1 hc)
      exact hsubpv i hi f hf hvx
  refine ⟨(stepR q r labEnds j₀ X).image g, (stepY q r labEnds X).image g,
    (stepW q r labEnds j₀ X).image (image g),
    ⟨hC.mono (by omega), image_subset_image hYsub, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro c hc
    obtain ⟨i, -, f, -, rfl⟩ := hRg c hc
    rfl
  · intro c hc c' hc' hcc'
    obtain ⟨i, -, f, -, rfl⟩ := hRg c (mem_coe.1 hc)
    obtain ⟨i', -, f', -, rfl⟩ := hRg c' (mem_coe.1 hc')
    exact Prod.ext rfl hcc'
  · intro c hc
    obtain ⟨i, hi, f, hf, rfl⟩ := hRg c hc
    exact fun hG' => disjoint_left.1 (hhost i hi) (hnewE i hi f hf) hG'
  · intro W hW
    obtain ⟨W₀, hW₀, rfl⟩ := mem_image.1 hW
    obtain ⟨i, hi, hW₀i⟩ : ∃ i ∈ X,
        W₀ = pieceP q r labEnds j₀ i ∨ W₀ = pieceQ q r labEnds j₀ i := by
      rcases mem_union.1 hW₀ with h | h
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h; exact ⟨i, hi, Or.inl rfl⟩
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h; exact ⟨i, hi, Or.inr rfl⟩
    refine (card_le_card (t := {i}) fun x hx => ?_).trans (by simp)
    obtain ⟨hxW, hxX⟩ := mem_filter.1 hx
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hxW
    rcases c with i' | f
    · have : i' = i := by
        rcases hW₀i with rfl | rfl
        · exact mem_pieceP_inl.1 hc
        · exact absurd hc not_mem_pieceQ_inl
      subst this; exact mem_singleton_self _
    · exfalso
      have := hXk _ hxX
      simp [g] at this
  · intro S hS
    refine le_trans ?_ ((hdeg S hS).trans (Nat.mul_le_mul_right _ (by omega)))
    unfold mdeg deg
    refine card_le_card_of_injOn Prod.snd (fun c hc => ?_) (fun c hc c' hc' hcc' => ?_)
    · obtain ⟨hcR, hSc⟩ := mem_filter.1 (mem_coe.1 hc)
      obtain ⟨i, hi, f, hf, rfl⟩ := hRg c hcR
      exact mem_coe.2 (mem_filter.2 ⟨mem_biUnion.2 ⟨i, hi, hnewE i hi f hf⟩, hSc⟩)
    · obtain ⟨i, -, f, -, rfl⟩ := hRg c (mem_filter.1 (mem_coe.1 hc)).1
      obtain ⟨i', -, f', -, rfl⟩ := hRg c' (mem_filter.1 (mem_coe.1 hc')).1
      exact Prod.ext rfl hcc'
  · intro S hS
    set Xs := X.filter fun p => S ⊆ pvOf (fun i : Lab n => i.2) (fun i => {i}) Φ X p
    have hsub : ((stepW q r labEnds j₀ X).image (image g)).filter
        (fun W => S ⊆ W.biUnion labEnds) ⊆
        Xs.image (fun i => (pieceP q r labEnds j₀ i).image g) ∪
          Xs.image (fun i => (pieceQ q r labEnds j₀ i).image g) := by
      intro W hW
      obtain ⟨hW, hSW⟩ := mem_filter.1 hW
      obtain ⟨W₀, hW₀, rfl⟩ := mem_image.1 hW
      rcases mem_union.1 hW₀ with h | h
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h
        have hS' : S ⊆ pvOf (fun i : Lab n => i.2) (fun i => {i}) Φ X i := by
          rw [hpv i hi]; exact hSW.trans (hpieceV i hi _ (Or.inl rfl))
        exact mem_union_left _ (mem_image.2 ⟨i, mem_filter.2 ⟨hi, hS'⟩, rfl⟩)
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h
        have hS' : S ⊆ pvOf (fun i : Lab n => i.2) (fun i => {i}) Φ X i := by
          rw [hpv i hi]; exact hSW.trans (hpieceV i hi _ (Or.inr rfl))
        exact mem_union_right _ (mem_image.2 ⟨i, mem_filter.2 ⟨hi, hS'⟩, rfl⟩)
    have hXs : Xs.card ≤ Ccl * D := hpdeg S hS
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ Xs.card + Xs.card := Nat.add_le_add card_image_le card_image_le
      _ ≤ (C₀ + 2 * Ccl + 1) * D := by nlinarith

end RefinedAbsorption.RefineDown
