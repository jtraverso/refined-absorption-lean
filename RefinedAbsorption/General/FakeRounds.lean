module
public import RefinedAbsorption.General.MultiRoot
public import RefinedAbsorption.General.Coloring
public import RefinedAbsorption.General.FakesK

/-!
# Placing the fake edges in rounds, keeping the pieces sparse

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Theorem 1.11 (fake edges
embedded with the Partial Clique Embedding Lemma 5.2).  Lean formalization: Juan Pablo Traverso
Gianini, Apache-2.0.

The new copies of a refiner are coloured so that no piece contains two new copies of the same
colour (`exists_piece_coloring`), and the gadgets of the copies of colour `j` are placed in round
`j` with the multi-root embedding lemma (`reserveMultiRootEmbedding`), tracking for every copy the
*round spans* of the pieces containing it: the span of the piece together with the auxiliary
vertices of the gadgets placed in the earlier rounds (`roundSpan`).  This keeps the number of
pieces whose round span contains a given `(k-1)`-set bounded (`RoundInv.pdeg`), which is what the
absorbers attached later need.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.RefineDown
  RefinedAbsorption.FlatDown RefinedAbsorption.FlatOmni

variable {n h : ℕ} {E : Type} [DecidableEq E]

/-- The span of a piece together with the auxiliary vertices of the gadgets of its new copies of
colour `< j`. -/
def roundSpan (ends : E → Finset (Fin n)) (R : Finset E) (col : E → ℕ) (Φ : E → Fin h → Fin n)
    (j : ℕ) (W : Finset E) : Finset (Fin n) :=
  W.biUnion ends ∪ (W.filter fun c => c ∈ R ∧ col c < j).biUnion fun c => auxImage (Φ c)

/-- The invariant after the rounds `< j`. -/
structure RoundInv (k : ℕ) (P : Finset (Fin n)) (ends : E → Finset (Fin n)) (R : Finset E)
    (𝒲 : Finset (Finset E)) (col : E → ℕ) (Tt : E → Finset (Finset (Fin n ⊕ Fin h)))
    (j A : ℕ) (Φ : E → Fin h → Fin n) : Prop where
  valid : ∀ c ∈ R, col c < j → ValidPlacement (ends c) (Φ c)
  range : ∀ c ∈ R, col c < j → ∀ p, Φ c p ∈ P
  disj : ∀ c ∈ R, ∀ c' ∈ R, col c < j → col c' < j → c ≠ c' →
    Disjoint (newEdges (Tt c) (Φ c)) (newEdges (Tt c') (Φ c'))
  deg : ∀ S : Finset (Fin n), S.card = k - 1 →
    deg ((R.filter fun c => col c < j).biUnion fun c => newEdges (Tt c) (Φ c)) S ≤ A
  pdeg : ∀ S : Finset (Fin n), S.card = k - 1 →
    (𝒲.filter fun W => S ⊆ roundSpan ends R col Φ j W).card ≤ A

theorem card_auxImage_le (φ : Fin h → Fin n) : (auxImage φ).card ≤ h :=
  card_image_le.trans (by simp)

theorem roundSpan_card_le {ends : E → Finset (Fin n)} {R : Finset E} {col : E → ℕ}
    {Φ : E → Fin h → Fin n} {j k : ℕ} {W : Finset E} (hk : ∀ c ∈ W, (ends c).card = k) :
    (roundSpan ends R col Φ j W).card ≤ W.card * (k + h) := by
  unfold roundSpan
  refine (card_union_le _ _).trans ?_
  have h1 : (W.biUnion ends).card ≤ W.card * k := by
    refine card_biUnion_le.trans ?_
    rw [← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun c hc => (hk c hc).le
  have h2 : ((W.filter fun c => c ∈ R ∧ col c < j).biUnion fun c => auxImage (Φ c)).card ≤
      W.card * h := by
    refine card_biUnion_le.trans ?_
    refine (sum_le_sum fun c _ => card_auxImage_le (Φ c)).trans ?_
    rw [sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))
  rw [mul_add]; omega

theorem roundSpan_subset {ends : E → Finset (Fin n)} {R : Finset E} {col : E → ℕ}
    {Φ : E → Fin h → Fin n} {j : ℕ} {W : Finset E} {U P : Finset (Fin n)} (hPU : P ⊆ U)
    (hW : ∀ c ∈ W, ends c ⊆ U) (hrange : ∀ c ∈ R, col c < j → ∀ p, Φ c p ∈ P) :
    roundSpan ends R col Φ j W ⊆ U := by
  unfold roundSpan
  refine union_subset (biUnion_subset.2 hW) (biUnion_subset.2 fun c hc => ?_)
  obtain ⟨-, hcR, hcj⟩ := mem_filter.1 hc
  intro v hv
  obtain ⟨p, -, rfl⟩ := mem_image.1 hv
  exact hPU (hrange c hcR hcj p)

/-- The root density of the tracked root sets of round `j`. -/
theorem round_rootDensity {k K B A : ℕ} {ends : E → Finset (Fin n)} {R : Finset E}
    {𝒲 : Finset (Finset E)} {col : E → ℕ} {Φ : E → Fin h → Fin n} {j : ℕ}
    {U P : Finset (Fin n)} (hPU : P ⊆ U) (hU : U.card ≤ (K + 1) * P.card)
    (hRr : ∀ c ∈ R, (ends c).card = k) (hspanU : ∀ W ∈ 𝒲, ∀ c ∈ W, ends c ⊆ U)
    (hRU : ∀ c ∈ R, ends c ⊆ U)
    (hcol : ∀ W ∈ 𝒲, ∀ c ∈ W, ∀ c' ∈ W, c ∈ R → c' ∈ R → col c = col c' → c = c')
    (hrange : ∀ c ∈ R, col c < j → ∀ p, Φ c p ∈ P)
    (hdegR : ∀ S : Finset (Fin n), S.card = k - 1 → mdeg ends R S ≤ B)
    (hpd : ∀ S : Finset (Fin n), S.card = k - 1 →
      (𝒲.filter fun W => S ⊆ roundSpan ends R col Φ j W).card ≤ A)
    (J : Finset (Fin n)) (hJ : J.card ≤ k - 1) :
    ∑ c ∈ R.filter (fun c => col c = j),
      ((insert (ends c) ((𝒲.filter fun W => c ∈ W).image (roundSpan ends R col Φ j))).filter
        fun R' => J ⊆ R').card ≤ ((K + 1) ^ (k - 1) * (B + A)) * P.card ^ (k - 1 - J.card) := by
  classical
  set I := R.filter (fun c => col c = j) with hI
  set Vj := roundSpan ends R col Φ j with hVj
  set 𝒲' := 𝒲.filter fun W => ∃ c ∈ W, c ∈ I with h𝒲'
  -- per copy
  have hper : ∀ c ∈ I, ((insert (ends c) ((𝒲.filter fun W => c ∈ W).image Vj)).filter
      fun R' => J ⊆ R').card ≤ (if J ⊆ ends c then 1 else 0) +
        (𝒲.filter fun W => c ∈ W ∧ J ⊆ Vj W).card := by
    intro c _
    rw [filter_insert]
    have h2 : (((𝒲.filter fun W => c ∈ W).image Vj).filter fun R' => J ⊆ R').card ≤
        (𝒲.filter fun W => c ∈ W ∧ J ⊆ Vj W).card := by
      rw [filter_image]
      refine card_image_le.trans (le_of_eq ?_)
      rw [filter_filter]
    split_ifs with hJc
    · exact (card_insert_le _ _).trans (by omega)
    · omega
  refine (sum_le_sum hper).trans ?_
  rw [sum_add_distrib]
  -- the copies
  have hA1 : ∑ c ∈ I, (if J ⊆ ends c then 1 else 0) ≤ B * U.card ^ (k - 1 - J.card) := by
    rw [← card_filter]
    refine rootIncidence_of_subset (r := k) I ends U B (fun c hc => hRU c (mem_filter.1 hc).1)
      (fun c hc => by rw [hRr c (mem_filter.1 hc).1]; omega) (fun S hS => ?_) J hJ
    exact (card_le_card (filter_subset_filter _ (filter_subset _ R))).trans (hdegR S hS)
  -- the pieces
  have hA2 : ∑ c ∈ I, (𝒲.filter fun W => c ∈ W ∧ J ⊆ Vj W).card ≤
      (𝒲'.filter fun W => J ⊆ Vj W).card := by
    simp only [card_filter]
    rw [sum_comm, h𝒲', sum_filter]
    refine sum_le_sum fun W hW => ?_
    by_cases hex : ∃ c ∈ W, c ∈ I
    · rw [if_pos hex]
      by_cases hWJ : J ⊆ Vj W
      · rw [if_pos hWJ]
        simp only [hWJ, and_true]
        rw [← card_filter]
        refine card_le_one.2 fun c₁ h₁ c₂ h₂ => ?_
        obtain ⟨hc₁I, hc₁W⟩ := mem_filter.1 h₁
        obtain ⟨hc₂I, hc₂W⟩ := mem_filter.1 h₂
        obtain ⟨hc₁R, hc₁j⟩ := mem_filter.1 hc₁I
        obtain ⟨hc₂R, hc₂j⟩ := mem_filter.1 hc₂I
        exact hcol W hW c₁ hc₁W c₂ hc₂W hc₁R hc₂R (hc₁j.trans hc₂j.symm)
      · rw [if_neg hWJ]; simp [hWJ]
    · rw [if_neg hex]
      refine le_of_eq (sum_eq_zero fun c hc => if_neg fun h' => hex ⟨c, h'.1, hc⟩)
  have hA3 : (𝒲'.filter fun W => J ⊆ Vj W).card ≤ A * U.card ^ (k - 1 - J.card) := by
    refine rootIncidence_of_subset (r := k) 𝒲' Vj U A
      (fun W hW => roundSpan_subset hPU (hspanU W (mem_filter.1 hW).1) hrange)
      (fun W hW => ?_) (fun S hS => (card_le_card (filter_subset_filter _ (filter_subset _ 𝒲))).trans
        (hpd S hS)) J hJ
    obtain ⟨-, c, hcW, hcI⟩ := mem_filter.1 hW
    have h1 : ends c ⊆ Vj W := (subset_biUnion_of_mem ends hcW).trans subset_union_left
    have := card_le_card h1
    rw [hRr c (mem_filter.1 hcI).1] at this
    omega
  have hUp : U.card ^ (k - 1 - J.card) ≤ (K + 1) ^ (k - 1) * P.card ^ (k - 1 - J.card) := by
    calc U.card ^ (k - 1 - J.card) ≤ ((K + 1) * P.card) ^ (k - 1 - J.card) :=
          Nat.pow_le_pow_left hU _
      _ = (K + 1) ^ (k - 1 - J.card) * P.card ^ (k - 1 - J.card) := by rw [mul_pow]
      _ ≤ (K + 1) ^ (k - 1) * P.card ^ (k - 1 - J.card) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
  calc ∑ c ∈ I, (if J ⊆ ends c then 1 else 0) + ∑ c ∈ I, (𝒲.filter fun W => c ∈ W ∧ J ⊆ Vj W).card
      ≤ B * U.card ^ (k - 1 - J.card) + A * U.card ^ (k - 1 - J.card) :=
        Nat.add_le_add hA1 (hA2.trans hA3)
    _ = (B + A) * U.card ^ (k - 1 - J.card) := by ring
    _ ≤ (B + A) * ((K + 1) ^ (k - 1) * P.card ^ (k - 1 - J.card)) := Nat.mul_le_mul_left _ hUp
    _ = ((K + 1) ^ (k - 1) * (B + A)) * P.card ^ (k - 1 - J.card) := by ring

/-- **One round of the placement of the fake gadgets.** -/
theorem roundInv_step (k h C K : ℕ) : ∃ Ce : ℕ, 0 < Ce ∧ ∀ (n : ℕ) {E : Type} [DecidableEq E]
    (ends : E → Finset (Fin n)) (X R : Finset E) (𝒲 : Finset (Finset E)) (col : E → ℕ)
    (Tt : E → Finset (Finset (Fin n ⊕ Fin h))) (U P : Finset (Fin n)) (B A j : ℕ)
    (Φ : E → Fin h → Fin n),
    P ⊆ U → U.card ≤ (K + 1) * P.card → 0 < P.card →
    (∀ c ∈ X ∪ R, (ends c).card = k) → (∀ c ∈ X ∪ R, ends c ⊆ U) →
    (∀ W ∈ 𝒲, W ⊆ X ∪ R) → (∀ c ∈ R, (𝒲.filter fun W => c ∈ W).card ≤ C) →
    (∀ W ∈ 𝒲, W.card ≤ C) → (∀ c ∈ R, GadgetWF k k (ends c) (Tt c)) →
    (∀ W ∈ 𝒲, ∀ c ∈ W, ∀ c' ∈ W, c ∈ R → c' ∈ R → col c = col c' → c = c') →
    (∀ S : Finset (Fin n), S.card = k - 1 → mdeg ends R S ≤ B) →
    Ce * A ≤ P.card → Ce * ((K + 1) ^ (k - 1) * (B + A)) ≤ P.card →
    RoundInv k P ends R 𝒲 col Tt j A Φ →
    ∃ Φ', RoundInv k P ends R 𝒲 col Tt (j + 1)
      (A + (C + 1) * (Ce * ((K + 1) ^ (k - 1) * (B + A)))) Φ' := by
  classical
  set kk := C * (k + h) + k with hkk
  obtain ⟨Ce, hCe, hemb⟩ := reserveMultiRootEmbedding k h kk (C + 1)
  refine ⟨Ce, hCe, ?_⟩
  intro n E _ ends X R 𝒲 col Tt U P B A j Φ hPU hU hP hr hXRU hsub hmult hcard hTt hcol hdegR
    hCA hCD hinv
  set D := (K + 1) ^ (k - 1) * (B + A) with hD
  set I := R.filter (fun c => col c = j) with hI
  set Vj := roundSpan ends R col Φ j with hVj
  set 𝓡 : E → Finset (Finset (Fin n)) := fun c =>
    insert (ends c) ((𝒲.filter fun W => c ∈ W).image Vj) with h𝓡
  set G := (R.filter fun c => col c < j).biUnion fun c => newEdges (Tt c) (Φ c) with hG
  have hIR : ∀ c ∈ I, c ∈ R := fun c hc => (mem_filter.1 hc).1
  have hRr : ∀ c ∈ R, (ends c).card = k := fun c hc => hr c (mem_union_right _ hc)
  have hw : ∀ c ∈ I, GadgetWF k kk (ends c) (Tt c) := by
    intro c hc
    have hw0 := hTt c (hIR c hc)
    exact ⟨hw0.roots_le.trans (Nat.le_add_left _ _), hw0.roots_ge, hw0.edge_card,
      hw0.edge_roots, hw0.edge_aux⟩
  have hRc : ∀ c ∈ I, ends c ∈ 𝓡 c := fun c _ => mem_insert_self _ _
  have hm : ∀ c ∈ I, (𝓡 c).card ≤ C + 1 := by
    intro c hc
    refine (card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
    exact card_image_le.trans (hmult c (hIR c hc))
  have hk : ∀ c ∈ I, ∀ R' ∈ 𝓡 c, R'.card ≤ kk := by
    intro c hc R' hR'
    rcases mem_insert.1 hR' with rfl | hR'
    · rw [hRr c (hIR c hc)]; exact Nat.le_add_left _ _
    · obtain ⟨W, hW, rfl⟩ := mem_image.1 hR'
      have hW𝒲 := (mem_filter.1 hW).1
      refine (roundSpan_card_le (k := k) fun x hx => hr x (hsub W hW𝒲 hx)).trans ?_
      exact (Nat.mul_le_mul_right _ (hcard W hW𝒲)).trans (Nat.le_add_right _ _)
  have hGdeg : ∀ S : Finset (Fin n), S.card = k - 1 → Ce * deg G S ≤ P.card := fun S hS =>
    (Nat.mul_le_mul_left _ (hinv.deg S hS)).trans hCA
  have hroot : ∀ J : Finset (Fin n), J.card ≤ k - 1 →
      ∑ c ∈ I, ((𝓡 c).filter fun R' => J ⊆ R').card ≤ D * P.card ^ (k - 1 - J.card) :=
    fun J hJ => round_rootDensity hPU hU hRr (fun W hW c hc => hXRU c (hsub W hW hc))
      (fun c hc => hXRU c (mem_union_right _ hc)) hcol hinv.range hdegR hinv.pdeg J hJ
  obtain ⟨Φ', hval', hran', hdisj', hhost', hdeg', hcov'⟩ :=
    hemb n I ends 𝓡 Tt G P D hw hRc hm hk hGdeg hCD hroot hP
  set Φn : E → Fin h → Fin n := fun c => if col c = j then Φ' c else Φ c with hΦn
  have hΦn1 : ∀ c, col c = j → Φn c = Φ' c := fun c hc => if_pos hc
  have hΦn2 : ∀ c, col c ≠ j → Φn c = Φ c := fun c hc => if_neg hc
  have hlt : ∀ c, col c < j + 1 → col c = j ∨ col c < j := fun c hc => by omega
  have hGsub : ∀ c ∈ R, col c < j → newEdges (Tt c) (Φ c) ⊆ G := fun c hc hcj =>
    subset_biUnion_of_mem (fun c => newEdges (Tt c) (Φ c)) (mem_filter.2 ⟨hc, hcj⟩)
  refine ⟨Φn, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro c hc hcj
    rcases hlt c hcj with h1 | h1
    · rw [hΦn1 c h1]; exact hval' c (mem_filter.2 ⟨hc, h1⟩)
    · rw [hΦn2 c (by omega)]; exact hinv.valid c hc h1
  · intro c hc hcj p
    rcases hlt c hcj with h1 | h1
    · rw [hΦn1 c h1]; exact hran' c (mem_filter.2 ⟨hc, h1⟩) p
    · rw [hΦn2 c (by omega)]; exact hinv.range c hc h1 p
  · intro c hc c' hc' hcj hc'j hne
    rcases hlt c hcj with h1 | h1 <;> rcases hlt c' hc'j with h2 | h2
    · rw [hΦn1 c h1, hΦn1 c' h2]
      exact hdisj' c (mem_filter.2 ⟨hc, h1⟩) c' (mem_filter.2 ⟨hc', h2⟩) hne
    · rw [hΦn1 c h1, hΦn2 c' (by omega)]
      exact (hhost' c (mem_filter.2 ⟨hc, h1⟩)).mono_right (hGsub c' hc' h2)
    · rw [hΦn2 c (by omega), hΦn1 c' h2]
      exact ((hhost' c' (mem_filter.2 ⟨hc', h2⟩)).mono_right (hGsub c hc h1)).symm
    · rw [hΦn2 c (by omega), hΦn2 c' (by omega)]
      exact hinv.disj c hc c' hc' h1 h2 hne
  · intro S hS
    have hsubU : ((R.filter fun c => col c < j + 1).biUnion fun c => newEdges (Tt c) (Φn c)) ⊆
        G ∪ I.biUnion fun c => newEdges (Tt c) (Φ' c) := by
      intro f hf
      obtain ⟨c, hc, hfc⟩ := mem_biUnion.1 hf
      obtain ⟨hcR, hcj⟩ := mem_filter.1 hc
      rcases hlt c hcj with h1 | h1
      · rw [hΦn1 c h1] at hfc
        exact mem_union_right _ (mem_biUnion.2 ⟨c, mem_filter.2 ⟨hcR, h1⟩, hfc⟩)
      · rw [hΦn2 c (by omega)] at hfc
        exact mem_union_left _ (hGsub c hcR h1 hfc)
    refine (card_le_card (filter_subset_filter _ hsubU)).trans ?_
    rw [filter_union]
    refine (card_union_le _ _).trans ?_
    have h1 : (G.filter fun e => S ⊆ e).card ≤ A := hinv.deg S hS
    have h2 : ((I.biUnion fun c => newEdges (Tt c) (Φ' c)).filter fun e => S ⊆ e).card ≤
      Ce * D := hdeg' S hS
    have : Ce * D ≤ (C + 1) * (Ce * D) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · intro S hS
    -- the round spans grow only by the gadget of the unique copy of colour `j`
    have hgrow : ∀ W ∈ 𝒲, roundSpan ends R col Φn (j + 1) W ⊆
        Vj W ∪ (W.filter (· ∈ I)).biUnion fun c => auxImage (Φ' c) := by
      intro W _ v hv
      rcases mem_union.1 hv with hv | hv
      · exact mem_union_left _ (mem_union_left _ hv)
      · obtain ⟨c, hc, hvc⟩ := mem_biUnion.1 hv
        obtain ⟨hcW, hcR, hcj⟩ := mem_filter.1 hc
        rcases hlt c hcj with h1 | h1
        · rw [hΦn1 c h1] at hvc
          exact mem_union_right _ (mem_biUnion.2 ⟨c, mem_filter.2 ⟨hcW, mem_filter.2 ⟨hcR, h1⟩⟩,
            hvc⟩)
        · rw [hΦn2 c (by omega)] at hvc
          exact mem_union_left _ (mem_union_right _ (mem_biUnion.2 ⟨c, mem_filter.2 ⟨hcW, hcR, h1⟩,
            hvc⟩))
    have hsplit : 𝒲.filter (fun W => S ⊆ roundSpan ends R col Φn (j + 1) W) ⊆
        𝒲.filter (fun W => S ⊆ Vj W) ∪
          I.biUnion fun c => 𝒲.filter fun W => c ∈ W ∧ S ⊆ Vj W ∪ auxImage (Φ' c) := by
      intro W hW
      obtain ⟨hW𝒲, hSW⟩ := mem_filter.1 hW
      by_cases hS0 : S ⊆ Vj W
      · exact mem_union_left _ (mem_filter.2 ⟨hW𝒲, hS0⟩)
      · refine mem_union_right _ ?_
        have hSW' := hSW.trans (hgrow W hW𝒲)
        obtain ⟨v, hvS, hvV⟩ := not_subset.1 hS0
        rcases mem_union.1 (hSW' hvS) with hv | hv
        · exact absurd hv hvV
        · obtain ⟨c, hc, -⟩ := mem_biUnion.1 hv
          obtain ⟨hcW, hcI⟩ := mem_filter.1 hc
          refine mem_biUnion.2 ⟨c, hcI, mem_filter.2 ⟨hW𝒲, hcW, ?_⟩⟩
          intro x hx
          rcases mem_union.1 (hSW' hx) with h1 | h1
          · exact mem_union_left _ h1
          · obtain ⟨c', hc', hxc'⟩ := mem_biUnion.1 h1
            obtain ⟨hc'W, hc'I⟩ := mem_filter.1 hc'
            have : c' = c := hcol W hW𝒲 c' hc'W c hcW (hIR c' hc'I) (hIR c hcI)
              ((mem_filter.1 hc'I).2.trans (mem_filter.1 hcI).2.symm)
            rw [this] at hxc'
            exact mem_union_right _ hxc'
    refine (card_le_card hsplit).trans ((card_union_le _ _).trans ?_)
    have hper : ∀ c ∈ I, (𝒲.filter fun W => c ∈ W ∧ S ⊆ Vj W ∪ auxImage (Φ' c)).card ≤
        C * ((𝓡 c).filter fun R' => S ⊆ R' ∪ auxImage (Φ' c)).card := by
      intro c hc
      set A₀ := 𝒲.filter fun W => c ∈ W ∧ S ⊆ Vj W ∪ auxImage (Φ' c)
      refine (card_le_mul_card_image (f := Vj) A₀ C fun b _ => ?_).trans
        (Nat.mul_le_mul_left _ (card_le_card ?_))
      · refine (card_le_card fun W hW => ?_).trans (hmult c (hIR c hc))
        obtain ⟨hWA, -⟩ := mem_filter.1 hW
        obtain ⟨hW𝒲, hcW, -⟩ := mem_filter.1 hWA
        exact mem_filter.2 ⟨hW𝒲, hcW⟩
      · intro R' hR'
        obtain ⟨W, hW, rfl⟩ := mem_image.1 hR'
        obtain ⟨hW𝒲, hcW, hSW⟩ := mem_filter.1 hW
        exact mem_filter.2 ⟨mem_insert_of_mem (mem_image_of_mem _ (mem_filter.2 ⟨hW𝒲, hcW⟩)),
          hSW⟩
    have hsum : (I.biUnion fun c => 𝒲.filter fun W => c ∈ W ∧ S ⊆ Vj W ∪ auxImage (Φ' c)).card ≤
        C * (Ce * D) := by
      refine card_biUnion_le.trans ((sum_le_sum hper).trans ?_)
      rw [← mul_sum]
      exact Nat.mul_le_mul_left _ (hcov' S hS)
    have h1 : (𝒲.filter fun W => S ⊆ Vj W).card ≤ A := hinv.pdeg S hS
    have : C * (Ce * D) ≤ (C + 1) * (Ce * D) := Nat.mul_le_mul_right _ (Nat.le_succ C)
    omega

/-- The growth of the bound over the rounds. -/
def roundBound (Ce C κ : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => roundBound Ce C κ j + (C + 1) * (Ce * (κ * (1 + roundBound Ce C κ j)))

theorem roundBound_mono (Ce C κ : ℕ) {i j : ℕ} (hij : i ≤ j) :
    roundBound Ce C κ i ≤ roundBound Ce C κ j := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by simp only [roundBound]; exact Nat.le_add_right _ _)

/-- **All rounds of the placement of the fake gadgets.** -/
theorem fakeRoundsAll (k h C K N : ℕ) : ∃ Cs Cr : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E]
    (ends : E → Finset (Fin n)) (X R : Finset E) (𝒲 : Finset (Finset E)) (col : E → ℕ)
    (Tt : E → Finset (Finset (Fin n ⊕ Fin h))) (U P : Finset (Fin n)) (B : ℕ),
    P ⊆ U → U.card ≤ (K + 1) * P.card → 0 < P.card →
    (∀ c ∈ X ∪ R, (ends c).card = k) → (∀ c ∈ X ∪ R, ends c ⊆ U) →
    (∀ W ∈ 𝒲, W ⊆ X ∪ R) → (∀ c ∈ R, (𝒲.filter fun W => c ∈ W).card ≤ C) →
    (∀ W ∈ 𝒲, W.card ≤ C) → (∀ c ∈ R, GadgetWF k k (ends c) (Tt c)) →
    (∀ W ∈ 𝒲, ∀ c ∈ W, ∀ c' ∈ W, c ∈ R → c' ∈ R → col c = col c' → c = c') →
    (∀ c ∈ R, col c < N) →
    (∀ S : Finset (Fin n), S.card = k - 1 → mdeg ends R S ≤ B) →
    (∀ S : Finset (Fin n), S.card = k - 1 → pdeg ends 𝒲 S ≤ B) →
    Cs * B ≤ P.card →
    ∃ Φ, RoundInv k P ends R 𝒲 col Tt N (Cr * B) Φ := by
  classical
  obtain ⟨Ce, hCe, hstep⟩ := roundInv_step k h C K
  set κ := (K + 1) ^ (k - 1) with hκ
  set α := roundBound Ce C κ with hα
  refine ⟨Ce * (κ * (1 + α N)) + Ce * α N, α N, ?_⟩
  intro n E _ ends X R 𝒲 col Tt U P B hPU hU hP hr hXRU hsub hmult hcard hTt hcol hcolN hdegR hpd
    hCs
  obtain ⟨z₀, -⟩ := card_pos.1 hP
  have key : ∀ j ≤ N, ∃ Φ, RoundInv k P ends R 𝒲 col Tt j (α j * B) Φ := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun _ _ => z₀, ⟨by simp, by simp, by simp, fun S _ => ?_, fun S hS => ?_⟩⟩
      · have : (R.filter fun c => col c < 0) = ∅ := by simp
        rw [this, biUnion_empty]
        simp [deg]
      · have hspan : ∀ W, roundSpan ends R col (fun (_ : E) (_ : Fin h) => z₀) 0 W =
            W.biUnion ends := by
          intro W; unfold roundSpan; simp
        simp only [hspan]
        have := hpd S hS
        unfold pdeg at this
        simp only [hα, roundBound, one_mul]
        exact this
    | succ j ih =>
      intro hjN
      obtain ⟨Φ, hΦ⟩ := ih (by omega)
      have hαj : α j ≤ α N := roundBound_mono Ce C κ (by omega)
      have h1 : Ce * (α j * B) ≤ P.card := by
        refine le_trans ?_ hCs
        have : Ce * (α j * B) ≤ Ce * α N * B := by
          rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hαj)
        exact this.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
      have h2 : Ce * (κ * (B + α j * B)) ≤ P.card := by
        refine le_trans ?_ hCs
        have : Ce * (κ * (B + α j * B)) ≤ Ce * (κ * (1 + α N)) * B := by
          have e : Ce * (κ * (B + α j * B)) = Ce * (κ * (1 + α j)) * B := by ring
          rw [e]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega)))
        exact this.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
      obtain ⟨Φ', hΦ'⟩ := hstep n ends X R 𝒲 col Tt U P B (α j * B) j Φ hPU hU hP hr hXRU hsub
        hmult hcard hTt hcol hdegR h1 h2 hΦ
      refine ⟨Φ', ?_⟩
      have e : α j * B + (C + 1) * (Ce * (κ * (B + α j * B))) = α (j + 1) * B := by
        simp only [hα, roundBound]; ring
      rw [← e]
      exact hΦ'
  exact key N le_rfl

end RefinedAbsorption.General
