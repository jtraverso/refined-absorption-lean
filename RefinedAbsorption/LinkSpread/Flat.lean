module
public import RefinedAbsorption.LinkSpread.Fibre
public import RefinedAbsorption.Placement.PlacedFlat

/-!
# The flat step for all link graphs at once (tagged flat step)

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, flat steps and Lemma 5.2).
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

Building the link refiners of `PlacedLinkLevelE q r i` requires, inside each link graph (uniformity
`r - i`), the flat steps of the refine-down construction, and these have to be carried out **for
all outside parts `T` at once**, spread over the reserve.  This file does that.

The link graphs form one tagged multigraph (`LinkSpread/Fibre.lean`): copy `x` has tag `tg x`
(outside the region `Zo`) and body `bd x` (inside `Zo`).  Fix a sub-reserve `Z ⊆ Zo` and suppose
the bodies are `j`-flat with respect to `Z`.  Then the lifted multigraph is `(i + j)`-flat, and

* link refiners of the lifted multigraph at level `i + j` (inside `Z`) give, fibre by fibre, link
  refiners of the bodies at level `j` (`linkRefiners_fibre`: link levels compose);
* the completion supports of the lifted pieces are placed **once for all tags** with the Partial
  Clique Embedding Lemma (`multiCliqueEmbedding`), with roots `T ∪ T₂ ∪ V(W)`;
* in every fibre, the flat step of the bodies (`flatStep_deg`, uniformity `r - i`) is run with
  these supports.

`taggedFlatStep`: the result is, for every tag `T`, a residual `K_{q-i}^{r-i}`-refiner of the
bodies of the fibre whose residue is `(j-1)`-flat, with all new copies inside `Zo`; and the lifted
new copies `T ∪ c`, **summed over all tags**, have `(r-1)`-degrees at most the degrees of the
lifted link refiners plus `Cs' · D`, and the same for the lifted pieces.  The hypotheses on the
lifted link refiners (density of pieces, degrees) are exactly the conclusions of
`PlacedLinkLevelE q r (i + j)` applied to the lifted multigraph.
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement

section Aux

/-- Reindexing a double sum along a jointly injective map. -/
theorem sum_sum_le_of_inj {α β γ : Type*} [DecidableEq γ] (Ts : Finset α) (P : α → Finset β)
    (Q : Finset γ) (φ : α → β → γ) (g : γ → ℕ)
    (hmem : ∀ T ∈ Ts, ∀ b ∈ P T, φ T b ∈ Q)
    (hinj : ∀ T ∈ Ts, ∀ b ∈ P T, ∀ T' ∈ Ts, ∀ b' ∈ P T', φ T b = φ T' b' → T = T' ∧ b = b') :
    ∑ T ∈ Ts, ∑ b ∈ P T, g (φ T b) ≤ ∑ A ∈ Q, g A := by
  classical
  rw [sum_sigma', ← sum_image (f := g) (g := fun x : (_ : α) × β => φ x.1 x.2)]
  · refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.zero_le _
    intro A hA
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hA
    obtain ⟨hx1, hx2⟩ := mem_sigma.1 hx
    exact hmem _ hx1 _ hx2
  · intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := mem_sigma.1 (mem_coe.1 hx)
    obtain ⟨hy1, hy2⟩ := mem_sigma.1 (mem_coe.1 hy)
    obtain ⟨h1, h2⟩ := hinj _ hx1 _ hx2 _ hy1 _ hy2 hxy
    obtain ⟨a, b⟩ := x
    obtain ⟨a', b'⟩ := y
    simp only at h1 h2
    subst h1 h2
    rfl

/-- Reindexing a sum of cardinalities along a jointly injective map. -/
theorem sum_card_le_of_inj {α β γ : Type*} [DecidableEq γ] (Ts : Finset α) (s : α → Finset β)
    (Q : Finset γ) (φ : α → β → γ) (hmem : ∀ T ∈ Ts, ∀ b ∈ s T, φ T b ∈ Q)
    (hinj : ∀ T ∈ Ts, ∀ b ∈ s T, ∀ T' ∈ Ts, ∀ b' ∈ s T', φ T b = φ T' b' → T = T' ∧ b = b') :
    ∑ T ∈ Ts, (s T).card ≤ Q.card := by
  have := sum_sum_le_of_inj Ts s Q φ (fun _ => 1) hmem hinj
  simpa [← card_eq_sum_ones] using this

variable {V E : Type*} [DecidableEq V]

theorem sdiff_subset_iff' {s t u : Finset V} : s \ t ⊆ u ↔ s ⊆ t ∪ u := by
  constructor
  · intro h v hv
    by_cases hvt : v ∈ t
    · exact mem_union_left _ hvt
    · exact mem_union_right _ (h (mem_sdiff.2 ⟨hv, hvt⟩))
  · intro h v hv
    obtain ⟨hvs, hvt⟩ := mem_sdiff.1 hv
    rcases mem_union.1 (h hvs) with h' | h'
    · exact absurd h' hvt
    · exact h'

/-- Lifted degrees are degrees of the set with the tag removed. -/
theorem mdeg_lift (T : Finset V) (f : E → Finset V) (G : Finset E) (S : Finset V) :
    mdeg (fun c => T ∪ f c) G S = mdeg f G (S \ T) := by
  unfold mdeg
  congr 1
  exact filter_congr fun c _ => sdiff_subset_iff'.symm

/-- Lifted piece degrees are at most piece degrees of the set with the tag removed. -/
theorem pdeg_lift_le (T : Finset V) (f : E → Finset V) (𝒲 : Finset (Finset E)) (S : Finset V) :
    pdeg (fun c => T ∪ f c) 𝒲 S ≤ pdeg f 𝒲 (S \ T) := by
  unfold pdeg
  refine card_le_card fun W hW => ?_
  obtain ⟨hW, hS⟩ := mem_filter.1 hW
  refine mem_filter.2 ⟨hW, fun v hv => ?_⟩
  obtain ⟨hvS, hvT⟩ := mem_sdiff.1 hv
  obtain ⟨c, hc, hvc⟩ := mem_biUnion.1 (hS hvS)
  rcases mem_union.1 hvc with h | h
  · exact absurd h hvT
  · exact mem_biUnion.2 ⟨c, hc, h⟩

end Aux

set_option maxHeartbeats 1000000 in
/-- **The flat step for all link graphs at once.**  See the module docstring. -/
theorem taggedFlatStep (q r i j Cl : ℕ) (hj : 1 ≤ j) (hijr : i + j < r) (hrq : r < q) :
    ∃ Cs Cs' : ℕ, 0 < Cs ∧ ∀ (n : ℕ) {E N : Type} [DecidableEq E] [DecidableEq N]
      (tg bd : E → Finset (Fin n)) (Zo Z : Finset (Fin n))
      (endsN : Finset (Fin n) → N → Finset (Fin n)) (X : Finset E)
      (RN : Finset (Fin n) → Finset N) (𝒲 : Finset (Fin n) → Finset (Finset (E ⊕ N))) (D : ℕ),
      Z ⊆ Zo → (∀ x, Disjoint (tg x) Zo) → (∀ x, bd x ⊆ Zo) →
      (∀ x ∈ X, (tg x).card = i) → (∀ x ∈ X, (bd x).card = r - i) → IsFlat j Z bd X →
      LinkRefiners q r (i + j) Cl (liftEnds tg bd) Z X endsN RN 𝒲 →
      q + r ≤ Z.card → Cs ≤ Z.card →
      (∀ J : Finset (Fin n), J.card ≤ r - 1 →
        ∑ A ∈ (outParts (liftEnds tg bd) Z (i + j) X).filter (fun A => J \ Z ⊆ A),
          ((𝒲 A).filter fun W => J ∩ Z ⊆ W.biUnion (lE (liftEnds tg bd) Z endsN A)).card ≤
          D * Z.card ^ (r - 1 - J.card)) →
      ∃ (R Y : Finset (Fin n) → Finset (E ⊕ FLab (Fin n) E N))
        (𝒲' : Finset (Fin n) → Finset (Finset (E ⊕ FLab (Fin n) E N))),
        (∀ T ∈ X.image tg,
          IsResidualMultiRefiner (q - i) (r - i) (flatConst (q - i) (r - i) Cl)
            (fEnds bd (fun T₂ => endsN (T ∪ T₂))) ((fibre tg X T).image Sum.inl) (R T) (Y T)
            (𝒲' T) ∧
          IsFlat (j - 1) Z (fEnds bd (fun T₂ => endsN (T ∪ T₂))) (Y T) ∧
          (∀ x, Sum.inl x ∈ Y T → x ∈ fibre tg X T ∧ (bd x \ Z).card < j) ∧
          Y T ⊆ (fibre tg X T).image Sum.inl ∪ R T ∧ (∀ c ∈ R T, ∀ x, c ≠ Sum.inl x) ∧
          (∀ c ∈ R T, fEnds bd (fun T₂ => endsN (T ∪ T₂)) c ⊆ Zo)) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          ∑ T ∈ X.image tg,
            mdeg (fun c => T ∪ fEnds bd (fun T₂ => endsN (T ∪ T₂)) c) (R T) S ≤
          ∑ A ∈ (outParts (liftEnds tg bd) Z (i + j) X).filter (fun A => S \ Z ⊆ A),
            mdeg (endsN A) (RN A) (S ∩ Z) + Cs' * D) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          ∑ T ∈ X.image tg,
            pdeg (fun c => T ∪ fEnds bd (fun T₂ => endsN (T ∪ T₂)) c) (𝒲' T) S ≤ Cs' * D) := by
  obtain ⟨C, hC, hemb⟩ := multiCliqueEmbedding r (q - i + (r - i)) (r + Cl * r)
  set K := (fakeModulus (q - i) (r - i) + 1) * flatCompCard (q - i) (r - i) Cl with hK
  refine ⟨C, K * C + 2 * C, hC, ?_⟩
  intro n E N _ _ tg bd Zo Z endsN X RN 𝒲 D hZ htg hbd htgc hbdc hflat hL hZq hCZ hdens
  classical
  set L := liftEnds tg bd with hLdef
  have hLf := hL.filter_nonempty
  set 𝒲f : Finset (Fin n) → Finset (Finset (E ⊕ N)) := fun A => (𝒲 A).filter Finset.Nonempty
    with h𝒲f
  set I := fI L Z (i + j) X 𝒲f with hI
  have hwf : ∀ t ∈ I, GadgetWF r (r + Cl * r) (flatRoots L Z endsN t)
      (∅ : Finset (Finset (Fin n ⊕ Fin (q - i + (r - i))))) := by
    intro t ht
    obtain ⟨hT, hW⟩ := mem_fI.1 ht
    exact ⟨flatRoots_card_le (by omega) hLf ht,
      le_trans (Nat.sub_le r 1) (flatRoots_card_ge (by omega) hLf ht (mem_filter.1 hW).2),
      by simp, by simp, by simp⟩
  have hroot : ∀ J : Finset (Fin n), J.card ≤ r - 1 →
      (I.filter fun t => J ⊆ flatRoots L Z endsN t).card ≤ D * Z.card ^ (r - 1 - J.card) := by
    intro J hJ
    refine (flatRoots_count_le hLf J).trans (le_trans ?_ (hdens J hJ))
    exact sum_le_sum fun A _ => card_le_card fun W hW => by
      simp only [h𝒲f, mem_filter] at hW ⊢
      exact ⟨hW.1.1, hW.2⟩
  obtain ⟨Φ, hval, hrange, hcount, -⟩ := hemb n I (flatRoots L Z endsN) (fun _ => ∅) Z D hwf
    hCZ hroot
  obtain ⟨Zd, hZd, hZdc⟩ := exists_subset_card_eq (show q - i + (r - i) ≤ Z.card by omega)
  set Z₀ : Finset (Fin n) → Finset (E ⊕ N) → Finset (Fin n) :=
    fun A W => if (A, W) ∈ I then auxImage (Φ (A, W)) else Zd with hZ₀def
  have hZ₀ : ∀ A W, Z₀ A W ⊆ Z := by
    intro A W
    simp only [hZ₀def]
    split_ifs with h
    · intro v hv
      obtain ⟨p, -, rfl⟩ := mem_image.1 hv
      exact hrange _ h p
    · exact hZd
  have hZ₀c : ∀ A W, (Z₀ A W).card = q - i + (r - i) := by
    intro A W
    simp only [hZ₀def]
    split_ifs with h
    · unfold auxImage
      rw [card_image_of_injective _ (hval _ h).1, card_univ, Fintype.card_fin]
    · exact hZdc
  have hTdisj : ∀ T ∈ X.image tg, Disjoint T Zo := by
    intro T hT
    obtain ⟨x, -, rfl⟩ := mem_image.1 hT
    exact htg x
  -- the flat step in every fibre
  have key : ∀ T : Finset (Fin n), ∃ (RT YT : Finset (E ⊕ FLab (Fin n) E N))
      (𝒲T : Finset (Finset (E ⊕ FLab (Fin n) E N))), T ∈ X.image tg →
      IsResidualMultiRefiner (q - i) (r - i) (flatConst (q - i) (r - i) Cl)
          (fEnds bd (fun T₂ => endsN (T ∪ T₂))) ((fibre tg X T).image Sum.inl) RT YT 𝒲T ∧
        IsFlat (j - 1) Z (fEnds bd (fun T₂ => endsN (T ∪ T₂))) YT ∧
        (∀ x, Sum.inl x ∈ YT → x ∈ fibre tg X T ∧ (bd x \ Z).card < j) ∧
        YT ⊆ (fibre tg X T).image Sum.inl ∪ RT ∧ (∀ c ∈ RT, ∀ x, c ≠ Sum.inl x) ∧
        (∀ c ∈ RT, ∃ T₂ ∈ outParts bd Z j (fibre tg X T),
          fEnds bd (fun T₂ => endsN (T ∪ T₂)) c ⊆ T₂ ∪ Z) ∧
        (∀ S : Finset (Fin n), mdeg (fEnds bd (fun T₂ => endsN (T ∪ T₂))) RT S ≤
          ∑ T₂ ∈ outParts bd Z j (fibre tg X T),
            ((RN (T ∪ T₂)).filter fun y => S ⊆ T₂ ∪ endsN (T ∪ T₂) y).card +
          K * ((fI bd Z j (fibre tg X T) (fun T₂ => 𝒲f (T ∪ T₂))).filter fun t =>
            S ⊆ pieceSpan bd Z (fun T₂ => endsN (T ∪ T₂)) (fun T₂ W => Z₀ (T ∪ T₂) W) t).card) ∧
        ∀ S : Finset (Fin n), pdeg (fEnds bd (fun T₂ => endsN (T ∪ T₂))) 𝒲T S ≤
          2 * ((fI bd Z j (fibre tg X T) (fun T₂ => 𝒲f (T ∪ T₂))).filter fun t =>
            S ⊆ pieceSpan bd Z (fun T₂ => endsN (T ∪ T₂)) (fun T₂ W => Z₀ (T ∪ T₂) W) t).card := by
    intro T
    by_cases hT : T ∈ X.image tg
    · have hLT := linkRefiners_fibre hZ htg hbd htgc hLf (hTdisj T hT)
      have hXr : MIsRGraph (r - i) bd (fibre tg X T) :=
        fun x hx => hbdc x (fibre_subset tg X T hx)
      have hXf : IsFlat j Z bd (fibre tg X T) := hflat.mono (fibre_subset tg X T) le_rfl
      obtain ⟨R, Y, 𝒲', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        flatStep_deg (Z₀ := fun T₂ W => Z₀ (T ∪ T₂) W) (by omega : j < r - i)
          (by omega : r - i < q - i) hXr hXf hLT (fun _ _ => hZ₀ _ _) (fun _ _ => hZ₀c _ _)
      exact ⟨R, Y, 𝒲', fun _ => ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩
    · exact ⟨∅, ∅, ∅, fun h => absurd h hT⟩
  choose R Y 𝒲' hRY using key
  -- the lifted supports
  set P : Finset (Fin n) → Finset (Fin n) → Finset (Finset (Fin n) × Finset (E ⊕ N)) :=
    fun S T => (fI bd Z j (fibre tg X T) (fun T₂ => 𝒲f (T ∪ T₂))).filter fun t =>
      S \ T ⊆ pieceSpan bd Z (fun T₂ => endsN (T ∪ T₂)) (fun T₂ W => Z₀ (T ∪ T₂) W) t with hP
  have hPcount : ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ T ∈ X.image tg, (P S T).card ≤ C * D := by
    intro S hS
    refine le_trans ?_ (hcount S hS)
    refine sum_card_le_of_inj _ _ _ (fun T t => (T ∪ t.1, t.2)) ?_ ?_
    · intro T hT t ht
      obtain ⟨ht, hSt⟩ := mem_filter.1 ht
      obtain ⟨hT₂, hW⟩ := mem_fI.1 ht
      have hA := outParts_liftEnds hZ htg hbd htgc hT₂
      have hmem : (T ∪ t.1, t.2) ∈ I := mem_fI.2 ⟨hA, hW⟩
      refine mem_filter.2 ⟨hmem, fun v hv => ?_⟩
      have hZt : Z₀ (T ∪ t.1) t.2 = auxImage (Φ (T ∪ t.1, t.2)) := by
        simp only [hZ₀def, if_pos hmem]
      by_cases hvT : v ∈ T
      · exact mem_union_left _ (mem_union_left _ (mem_union_left _ hvT))
      · have hv' := hSt (mem_sdiff.2 ⟨hv, hvT⟩)
        unfold pieceSpan AW at hv'
        beta_reduce at hv'
        rw [hZt] at hv'
        show v ∈ flatRoots L Z endsN (T ∪ t.1, t.2) ∪ auxImage (Φ (T ∪ t.1, t.2))
        unfold flatRoots
        rw [lE_liftEnds hZ htg]
        simp only [mem_union] at hv' ⊢
        tauto
    · intro T hT t ht T' hT' t' ht' he
      simp only [Prod.mk.injEq] at he
      have h1 := (mem_fI.1 (mem_filter.1 ht).1).1
      have h1' := (mem_fI.1 (mem_filter.1 ht').1).1
      obtain ⟨e1, e2⟩ := union_split_eq (hTdisj T hT) (hTdisj T' hT')
        (outParts_fibre_subset hbd h1) (outParts_fibre_subset hbd h1') he.1
      exact ⟨e1, Prod.ext e2 he.2⟩
  refine ⟨R, Y, 𝒲', fun T hT => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := hRY T hT
    refine ⟨h1, h2, h3, h4, h5, fun c hc => ?_⟩
    obtain ⟨T₂, hT₂, hc⟩ := h6 c hc
    exact hc.trans (union_subset (outParts_fibre_subset hbd hT₂) hZ)
  · -- degrees of the lifted new copies
    have hlink : ∑ T ∈ X.image tg, ∑ T₂ ∈ outParts bd Z j (fibre tg X T),
        ((RN (T ∪ T₂)).filter fun y => S \ T ⊆ T₂ ∪ endsN (T ∪ T₂) y).card ≤
        ∑ A ∈ (outParts L Z (i + j) X).filter (fun A => S \ Z ⊆ A),
          mdeg (endsN A) (RN A) (S ∩ Z) := by
      have e : ∀ T T₂ : Finset (Fin n),
          ((RN (T ∪ T₂)).filter fun y => S \ T ⊆ T₂ ∪ endsN (T ∪ T₂) y) =
          (RN (T ∪ T₂)).filter fun y => S ⊆ (T ∪ T₂) ∪ endsN (T ∪ T₂) y := by
        intro T T₂
        refine filter_congr fun y _ => ?_
        rw [sdiff_subset_iff', union_assoc]
      simp_rw [e]
      refine le_trans (sum_sum_le_of_inj _ _ (outParts L Z (i + j) X) (fun T T₂ => T ∪ T₂)
        (fun A => ((RN A).filter fun y => S ⊆ A ∪ endsN A y).card) ?_ ?_) (linkSum_le hL S)
      · intro T _ T₂ hT₂
        exact outParts_liftEnds hZ htg hbd htgc hT₂
      · intro T hT T₂ hT₂ T' hT' T₂' hT₂' he
        exact union_split_eq (hTdisj T hT) (hTdisj T' hT') (outParts_fibre_subset hbd hT₂)
          (outParts_fibre_subset hbd hT₂') he
    calc ∑ T ∈ X.image tg, mdeg (fun c => T ∪ fEnds bd (fun T₂ => endsN (T ∪ T₂)) c) (R T) S
        = ∑ T ∈ X.image tg, mdeg (fEnds bd (fun T₂ => endsN (T ∪ T₂))) (R T) (S \ T) :=
          sum_congr rfl fun T _ => mdeg_lift _ _ _ _
      _ ≤ ∑ T ∈ X.image tg, (∑ T₂ ∈ outParts bd Z j (fibre tg X T),
            ((RN (T ∪ T₂)).filter fun y => S \ T ⊆ T₂ ∪ endsN (T ∪ T₂) y).card +
            K * (P S T).card) :=
          sum_le_sum fun T hT => (hRY T hT).2.2.2.2.2.2.1 (S \ T)
      _ = ∑ T ∈ X.image tg, ∑ T₂ ∈ outParts bd Z j (fibre tg X T),
            ((RN (T ∪ T₂)).filter fun y => S \ T ⊆ T₂ ∪ endsN (T ∪ T₂) y).card +
            K * ∑ T ∈ X.image tg, (P S T).card := by rw [sum_add_distrib, mul_sum]
      _ ≤ _ := by
          have := hPcount S hS
          have h2 : K * ∑ T ∈ X.image tg, (P S T).card ≤ (K * C + 2 * C) * D := by
            calc K * ∑ T ∈ X.image tg, (P S T).card ≤ K * (C * D) :=
                  Nat.mul_le_mul_left _ this
              _ ≤ (K * C + 2 * C) * D := by nlinarith
          exact Nat.add_le_add hlink h2
  · -- piece degrees
    calc ∑ T ∈ X.image tg,
          pdeg (fun c => T ∪ fEnds bd (fun T₂ => endsN (T ∪ T₂)) c) (𝒲' T) S
        ≤ ∑ T ∈ X.image tg, 2 * (P S T).card :=
          sum_le_sum fun T hT => (pdeg_lift_le _ _ _ _).trans ((hRY T hT).2.2.2.2.2.2.2 (S \ T))
      _ = 2 * ∑ T ∈ X.image tg, (P S T).card := by rw [mul_sum]
      _ ≤ 2 * (C * D) := Nat.mul_le_mul_left _ (hPcount S hS)
      _ ≤ (K * C + 2 * C) * D := by
          have : 2 * (C * D) = 2 * C * D := by ring
          rw [this, add_mul]; exact Nat.le_add_left _ _

end RefinedAbsorption.LinkSpread
