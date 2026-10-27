module
public import RefinedAbsorption.General.Defs
public import RefinedAbsorption.General.SpreadPerm
public import RefinedAbsorption.General.LocalCountK

/-!
# Random embedding of local refiners for outside parts of any size (Lemma 4.1)

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Lemma 4.1 (random embedding of
the local multi-refiners of Theorem 4.4 by independent random permutations of the new vertices).
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

For every tag `T` the flat clique omni-absorber of Theorem 3.7 (uniformity `r - i`) is built on
the fibre of `T`, inside `Z₁ ∪ P₀` with `P₀ = Zo \ Z₁`; the local refiners are then moved by
independent permutations of `P₀` chosen by `exists_perm_spread`.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement RefinedAbsorption.FlatDown
  RefinedAbsorption.Sharp RefinedAbsorption.RefineDown RefinedAbsorption.LinkSpread
  RefinedAbsorption.Local

/-- In a family of `|U|`-sets, the degree of `U` is its multiplicity. -/
theorem mdeg_le_mult_of_card {V E : Type*} [DecidableEq V] {ends : E → Finset V} {F : Finset E}
    {U : Finset V} (hF : ∀ c ∈ F, (ends c).card = U.card) : mdeg ends F U ≤ mult ends F U := by
  classical
  refine card_le_card fun c hc => ?_
  obtain ⟨hcF, hUc⟩ := mem_filter.1 hc
  exact mem_filter.2 ⟨hcF, (eq_of_subset_of_card_le hUc (hF c hcF).le).symm⟩

set_option maxHeartbeats 4000000 in
/-- **Random embedding of flat local refiners for all tags at once** (Lemma 4.1, outside parts
of size `i`, uniformity `r`). -/
theorem flatEmbedGen {q r i : ℕ} (hi : 1 ≤ i) (hir : i + 2 ≤ r) (a : ℕ → ℕ)
    (hF : FlatOmniK (q - i) (r - i) a) (ha : ∀ m m', m ≤ m' → a m ≤ sharpCost r m')
    (K M : ℕ) :
    ∃ C Ch : ℕ, ∀ (n : ℕ) (Zo Z₁ Ut : Finset (Fin n)) {E₁ : Type} [DecidableEq E₁]
      (tg₁ bd₁ : E₁ → Finset (Fin n)) (X₁ : Finset E₁) (Bd₁ : ℕ),
      Z₁ ⊆ Zo → Ch ≤ (Zo \ Z₁).card → Ch * Bd₁ ≤ (Zo \ Z₁).card →
      Z₁.card ≤ K * (Zo \ Z₁).card → Ut.card ≤ K * Zo.card → (∀ x ∈ X₁, tg₁ x ⊆ Ut) →
      (∀ x, Disjoint (tg₁ x) Zo) → (∀ x, bd₁ x ⊆ Z₁) → (∀ x ∈ X₁, (tg₁ x).card = i) →
      (∀ x ∈ X₁, (bd₁ x).card = r - i) →
      (∀ T e, mult bd₁ (fibre tg₁ X₁ T) e ≤ M) →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg₁ bd₁) X₁ S ≤ Bd₁) →
      ∃ Bd₂, Bd₂ ≤ C * (Bd₁ + sharpCost r Zo.card) ∧
        TRefOut q r i C tg₁ bd₁ Zo X₁ (fun _ => Bd₂) := by
  classical
  obtain ⟨CF, ChF, hloc⟩ := hF (K + M + 1)
  set k := r - i with hk_def
  have hk2 : 2 ≤ k := by omega
  have hri : r = i + k := by omega
  set s := k * CF + k with hs_def
  set μ := CF + CF * (M + CF) + 1 with hμ_def
  set c₁ := (K + 1) * (K + 1) with hc₁
  set c₀ := (1 + CF) * (1 + CF) with hc₀
  set B := 2 * c₁ * s + 1 with hB
  set C₂ := CF + CF * (1 + CF) + 2 * (c₀ * B ^ r) + μ * (r * (K + 1 + 1)) with hC₂
  refine ⟨C₂ + CF, ChF + 2 * r + 1, ?_⟩
  intro n Zo Z₁ Ut E₁ _ tg₁ bd₁ X₁ Bd₁ hZ hCh hChB hZ1K hUt htU htg hbd htgc hbdc hmult hdeg
  set P₀ := Zo \ Z₁ with hP₀
  set p := P₀.card with hp
  set sc := sharpCost r Zo.card with hsc
  set D := Bd₁ + sc with hD
  have hdisj : Disjoint Z₁ P₀ := disjoint_sdiff
  have hZoU : Z₁ ∪ P₀ = Zo := union_sdiff_of_subset hZ
  have hZoc : Zo.card = Z₁.card + p := by
    rw [hp, card_sdiff_of_subset hZ]; have := card_le_card hZ; omega
  have hZoK : Zo.card ≤ (K + 1) * p := by rw [hZoc]; nlinarith
  have hpZo : p ≤ Zo.card := by omega
  have hZo1 : 1 ≤ Zo.card := by omega
  have hap : a p ≤ sc := ha p Zo.card hpZo
  have hUtp : Ut.card ≤ c₁ * p := by
    calc Ut.card ≤ K * Zo.card := hUt
      _ ≤ (K + 1) * ((K + 1) * p) := Nat.mul_le_mul (by omega) hZoK
      _ = c₁ * p := by rw [hc₁]; ring
  have hZop : Zo.card ≤ c₁ * p :=
    hZoK.trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega)))
  -- the fibres
  have hfdeg : ∀ T ∈ X₁.image tg₁, ∀ U : Finset (Fin n), U.card = k - 1 →
      mdeg bd₁ (fibre tg₁ X₁ T) U ≤ Bd₁ := fun T hT U hU =>
    mdeg_fibre_le_gen (by omega) htg (fun x => (hbd x).trans hZ) hT htgc hdeg U hU
  -- the local refiners
  have hloc' := fun T : X₁.image tg₁ =>
    hloc n bd₁ Z₁ P₀ (fibre tg₁ X₁ T.1) Bd₁ hdisj
      (hZ1K.trans (Nat.mul_le_mul_right _ (by omega)))
      (by omega)
      ((Nat.mul_le_mul_right _ (by omega)).trans hChB)
      (fun x hx => hbdc x (fibre_subset _ _ _ hx))
      (fun x _ => hbd x)
      (hfdeg T.1 T.2)
      (fun e => (hmult T.1 e).trans (by omega))
  choose E' inst g ends' R 𝒲 hg hge hfr href hflat hdegR hmultR hcl htr using hloc'
  letI : ∀ T, DecidableEq (E' T) := inst
  set G : ∀ T : X₁.image tg₁, Finset (E' T) := fun T => (fibre tg₁ X₁ T.1).image (g T) with hG
  -- basic facts on one local refiner
  have hcopy : ∀ T : X₁.image tg₁, ∀ c ∈ G T ∪ R T, ends' T c ⊆ Z₁ ∪ P₀ := by
    intro T c hc
    rcases mem_union.1 hc with hc | hc
    · obtain ⟨x, -, rfl⟩ := mem_image.1 hc
      rw [hge T x]; exact (hbd x).trans subset_union_left
    · exact (hflat T c hc).1
  have hspan : ∀ T : X₁.image tg₁, ∀ W ∈ 𝒲 T, W.biUnion (ends' T) ⊆ Z₁ ∪ P₀ :=
    fun T => span_subset (href T) (hcopy T)
  have hdegG : ∀ (T : X₁.image tg₁) (U : Finset (Fin n)),
      mdeg (ends' T) (G T) U = mdeg bd₁ (fibre tg₁ X₁ T.1) U := fun T U =>
    mdeg_image_eq (fun c _ => hge T c) (hg T).injOn subset_rfl U
  have hdegR' : ∀ (T : X₁.image tg₁) (U : Finset (Fin n)), U.card = k - 1 →
      mdeg (ends' T) (R T) U ≤ CF * D := fun T U hU =>
    (hdegR T U hU).trans (Nat.mul_le_mul_left _ (by have : a P₀.card ≤ sc := hap; omega))
  have hdegGR : ∀ (T : X₁.image tg₁) (U : Finset (Fin n)), U.card = k - 1 →
      mdeg (ends' T) (G T ∪ R T) U ≤ Bd₁ + CF * D := by
    intro T U hU
    rw [mdeg_union_of_disjoint _ (href T).disjoint, hdegG]
    exact Nat.add_le_add (hfdeg T.1 T.2 U hU) (hdegR' T U hU)
  -- the set systems
  set A : ∀ T : X₁.image tg₁, ({c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T}) → Finset (Fin n) :=
    fun T => Sum.elim (fun c => ends' T c.1) (fun W => W.1.biUnion (ends' T)) with hA
  have hAU : ∀ T, ∀ x ∈ (univ : Finset ({c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T})), A T x ⊆ Z₁ ∪ P₀ := by
    rintro T (c | W) -
    · exact hcopy T c.1 (mem_union_right _ c.2)
    · exact hspan T W.1 W.2
  have hAs : ∀ T, ∀ x ∈ (univ : Finset ({c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T})), (A T x).card ≤ s := by
    rintro T (c | W) -
    · show (ends' T c.1).card ≤ s
      rw [(href T).rgraph c.1 (mem_union_right _ c.2)]; rw [hs_def]; omega
    · show (W.1.biUnion (ends' T)).card ≤ s
      refine (card_biUnion_ends_le (r := k) (ends' T) W.1
        fun x hx => (href T).rgraph x ((href T).subset W.1 W.2 hx)).trans ?_
      have := (href T).card_le W.1 W.2
      rw [hs_def]; nlinarith
  set Δ := CF * D + CF * (Bd₁ + CF * D) with hΔ
  have hΔb : ∀ T (U : Finset (Fin n)), U.card = k - 1 →
      ((univ : Finset ({c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T})).filter fun x => U ⊆ A T x).card ≤ Δ := by
    intro T U hU
    have hsum := card_univ_filter_sum (R T) (𝒲 T) (ends' T) (fun W => W.biUnion (ends' T))
      (fun B => U ⊆ B)
    refine le_of_eq_of_le hsum ?_
    have hUne : U.Nonempty := card_pos.1 (by omega)
    have h1 : ((R T).filter fun c => U ⊆ ends' T c).card ≤ CF * D := hdegR' T U hU
    have h2 : ((𝒲 T).filter fun W => U ⊆ W.biUnion (ends' T)).card ≤
        CF * mdeg (ends' T) (G T ∪ R T) U :=
      le_trans (card_le_card fun W hW => mem_filter.2 ⟨(mem_filter.1 hW).1, (mem_filter.1 hW).2,
        hUne.mono (mem_filter.1 hW).2⟩) (card_pieces_sub_le (href T) (hcl T) U (by omega))
    have h3 := Nat.mul_le_mul_left CF (hdegGR T U hU)
    rw [hΔ]; omega
  have hμb : ∀ T (U : Finset (Fin n)), U.card = k →
      ((univ : Finset ({c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T})).filter fun x => U ⊆ A T x).card ≤ μ := by
    intro T U hU
    have hsum := card_univ_filter_sum (R T) (𝒲 T) (ends' T) (fun W => W.biUnion (ends' T))
      (fun B => U ⊆ B)
    refine le_of_eq_of_le hsum ?_
    have hUne : U.Nonempty := card_pos.1 (by omega)
    have hRk : ∀ c ∈ R T, (ends' T c).card = U.card := fun c hc => by
      rw [(href T).rgraph c (mem_union_right _ hc), hU]
    have h1 : ((R T).filter fun c => U ⊆ ends' T c).card ≤ CF :=
      (mdeg_le_mult_of_card hRk).trans (hmultR T U)
    have h2 : ((𝒲 T).filter fun W => U ⊆ W.biUnion (ends' T)).card ≤
        CF * mdeg (ends' T) (G T ∪ R T) U :=
      le_trans (card_le_card fun W hW => mem_filter.2 ⟨(mem_filter.1 hW).1, (mem_filter.1 hW).2,
        hUne.mono (mem_filter.1 hW).2⟩) (card_pieces_sub_le (href T) (hcl T) U (by omega))
    have h3 : mdeg (ends' T) (G T ∪ R T) U ≤ M + CF := by
      rw [mdeg_union_of_disjoint _ (href T).disjoint, hdegG]
      refine Nat.add_le_add ?_ ((mdeg_le_mult_of_card hRk).trans (hmultR T U))
      refine (mdeg_le_mult_of_card (fun x hx => ?_)).trans (hmult T.1 U)
      rw [hbdc x (fibre_subset _ _ _ hx), hU]
    have h4 := Nat.mul_le_mul_left CF h3
    rw [hμ_def]; omega
  have hmean : ∀ J Q : Finset (Fin n), Q ⊆ Z₁ → J.card + Q.card ≤ r - 1 →
      ∑ T : X₁.image tg₁, ((univ : Finset ({c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T})).filter
        fun x => J ⊆ T.1 ∧ Q ⊆ A T x ∧ (A T x).Nonempty).card ≤
        c₀ * (c₁ * p) ^ (r - 1 - J.card - Q.card) * D := by
    intro J Q hQZ hJQ
    -- the count of one tag
    have hNT : ∀ T : X₁.image tg₁, ((univ : Finset ({c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T})).filter
        fun x => J ⊆ T.1 ∧ Q ⊆ A T x ∧ (A T x).Nonempty).card ≤
        if J ⊆ T.1 then ((R T).filter fun c => Q ⊆ ends' T c).card +
          ((𝒲 T).filter fun W => Q ⊆ W.biUnion (ends' T) ∧ (W.biUnion (ends' T)).Nonempty).card
        else 0 := by
      intro T
      split_ifs with hJT
      · have hsum := card_univ_filter_sum (R T) (𝒲 T) (ends' T) (fun W => W.biUnion (ends' T))
          (fun B => J ⊆ T.1 ∧ Q ⊆ B ∧ B.Nonempty)
        refine le_of_eq_of_le hsum (Nat.add_le_add (card_le_card fun c hc => ?_)
          (card_le_card fun W hW => ?_))
        · exact mem_filter.2 ⟨(mem_filter.1 hc).1, (mem_filter.1 hc).2.2.1⟩
        · exact mem_filter.2 ⟨(mem_filter.1 hW).1, (mem_filter.1 hW).2.2⟩
      · refine le_of_eq (card_eq_zero.2 (filter_eq_empty_iff.2 fun x _ hx => hJT hx.1))
    -- no new copy lies inside `Z₁`
    have hRZ : ∀ (T : X₁.image tg₁), ∀ c ∈ R T, ends' T c = Q → False := by
      intro T c hc hcQ
      obtain ⟨z, hz⟩ := (hflat T c hc).2
      rw [hcQ] at hz
      exact disjoint_left.1 hdisj (hQZ (mem_inter.1 hz).1) (mem_inter.1 hz).2
    rcases lt_trichotomy Q.card k with hQk | hQk | hQk
    · -- small sets
      have hJi : J.card ≤ i ∨ i < J.card := le_or_gt _ _
      set V := (1 + CF) * (Zo.card ^ (k - 1 - Q.card) * (Bd₁ + CF * D)) with hV
      have hT1 : ∀ T : X₁.image tg₁, ((univ : Finset ({c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T})).filter
          fun x => J ⊆ T.1 ∧ Q ⊆ A T x ∧ (A T x).Nonempty).card ≤ if J ⊆ T.1 then V else 0 := by
        intro T
        refine (hNT T).trans ?_
        split_ifs with hJT
        · have hGRk : ∀ c ∈ G T ∪ R T, ends' T c ⊆ Zo ∧ (ends' T c).card = k := fun c hc =>
            ⟨hZoU ▸ hcopy T c hc, (href T).rgraph c hc⟩
          have hm := mdeg_le_pow_of_deg hGRk (hdegGR T) Q (by omega)
          have h1 : ((R T).filter fun c => Q ⊆ ends' T c).card ≤ mdeg (ends' T) (G T ∪ R T) Q :=
            mdeg_mono _ subset_union_right Q
          have h2 := card_pieces_sub_le (href T) (hcl T) Q (by omega)
          have h3 : (1 + CF) * mdeg (ends' T) (G T ∪ R T) Q ≤ V :=
            Nat.mul_le_mul_left _ hm
          nlinarith
        · exact le_rfl
      refine (sum_le_sum fun T _ => hT1 T).trans ?_
      rw [sum_coe_sort (X₁.image tg₁) (fun T => if J ⊆ T then V else 0), ← sum_filter, sum_const,
        smul_eq_mul]
      rcases hJi with hJi | hJi
      · have hcnt := card_tags_containing_le (X₁.image tg₁) Ut (i := i) (fun T hT => by
          obtain ⟨x, hx, hxT⟩ := mem_image.1 hT
          rw [← hxT]; exact ⟨htU x hx, htgc x hx⟩) J hJi
        have hexp : r - 1 - J.card - Q.card = (i - J.card) + (k - 1 - Q.card) := by omega
        rw [hexp, pow_add]
        have hBd : Bd₁ + CF * D ≤ (1 + CF) * D := by nlinarith
        have e1 : Ut.card ^ (i - J.card) ≤ (c₁ * p) ^ (i - J.card) := Nat.pow_le_pow_left hUtp _
        have e2 : Zo.card ^ (k - 1 - Q.card) ≤ (c₁ * p) ^ (k - 1 - Q.card) :=
          Nat.pow_le_pow_left hZop _
        calc ((X₁.image tg₁).filter fun T => J ⊆ T).card * V
            ≤ Ut.card ^ (i - J.card) * V := Nat.mul_le_mul_right _ hcnt
          _ = (1 + CF) * (Ut.card ^ (i - J.card) * Zo.card ^ (k - 1 - Q.card)) *
                (Bd₁ + CF * D) := by rw [hV]; ring
          _ ≤ (1 + CF) * ((c₁ * p) ^ (i - J.card) * (c₁ * p) ^ (k - 1 - Q.card)) *
                ((1 + CF) * D) := by gcongr
          _ = _ := by rw [hc₀]; ring
      · have h0 : ((X₁.image tg₁).filter fun T => J ⊆ T).card = 0 := by
          refine card_eq_zero.2 (filter_eq_empty_iff.2 fun T hT hJT => ?_)
          obtain ⟨x, hx, hxT⟩ := mem_image.1 hT
          have := card_le_card hJT
          rw [← hxT, htgc x hx] at this
          omega
        rw [h0, zero_mul]; exact Nat.zero_le _
    · -- `k`-sets inside `Z₁`
      have hJi : J.card ≤ i - 1 := by omega
      have hT1 : ∀ T : X₁.image tg₁, ((univ : Finset ({c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T})).filter
          fun x => J ⊆ T.1 ∧ Q ⊆ A T x ∧ (A T x).Nonempty).card ≤
          if J ⊆ T.1 then CF * mult bd₁ (fibre tg₁ X₁ T.1) Q else 0 := by
        intro T
        refine (hNT T).trans ?_
        split_ifs with hJT
        · have h1 : ((R T).filter fun c => Q ⊆ ends' T c).card = 0 := by
            refine card_eq_zero.2 (filter_eq_empty_iff.2 fun c hc hQc => hRZ T c hc ?_)
            exact (eq_of_subset_of_card_le hQc
              (by rw [(href T).rgraph c (mem_union_right _ hc), hQk])).symm
          have h2 := card_pieces_rooted_le (href T)
            (fun W => Q ⊆ W.biUnion (ends' T) ∧ (W.biUnion (ends' T)).Nonempty) Q
            (fun W hW hPW => by
              obtain ⟨c, hcW, hcQ⟩ := hcl T W hW Q hPW.1 hQk
              refine ⟨c, hcW, ?_, hcQ⟩
              rcases mem_union.1 ((href T).subset W hW hcW) with h | h
              · exact h
              · exact (hRZ T c h hcQ).elim)
          have h3 := mult_image_le (fun c _ => hge T c) (G := fibre tg₁ X₁ T.1) Q
          rw [h1, zero_add]
          exact h2.trans (Nat.mul_le_mul_left _ h3)
        · exact le_rfl
      refine (sum_le_sum fun T _ => hT1 T).trans ?_
      rw [sum_coe_sort (X₁.image tg₁)
        (fun T => if J ⊆ T then CF * mult bd₁ (fibre tg₁ X₁ T) Q else 0), ← sum_filter, ← mul_sum]
      have hs := sum_mult_fibre_tags_le (r := r) hi (by omega) htU htg htgc hdeg J Q hJi
        (hQZ.trans hZ) hQk
      have hexp : r - 1 - J.card - Q.card = i - 1 - J.card := by omega
      rw [hexp]
      have e1 : Ut.card ^ (i - 1 - J.card) ≤ (c₁ * p) ^ (i - 1 - J.card) :=
        Nat.pow_le_pow_left hUtp _
      have hCF : CF ≤ c₀ := by rw [hc₀]; nlinarith
      calc CF * ∑ T ∈ (X₁.image tg₁).filter (fun T => J ⊆ T), mult bd₁ (fibre tg₁ X₁ T) Q
          ≤ CF * (Ut.card ^ (i - 1 - J.card) * Bd₁) := Nat.mul_le_mul_left _ hs
        _ ≤ c₀ * ((c₁ * p) ^ (i - 1 - J.card) * D) := by
            gcongr; omega
        _ = _ := by ring
    · -- large sets: no copy and no piece
      have h0 : ∀ T : X₁.image tg₁, ((univ : Finset ({c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T})).filter
          fun x => J ⊆ T.1 ∧ Q ⊆ A T x ∧ (A T x).Nonempty).card = 0 := by
        intro T
        refine Nat.eq_zero_of_le_zero ((hNT T).trans ?_)
        split_ifs
        · have h1 : ((R T).filter fun c => Q ⊆ ends' T c).card = 0 := by
            refine card_eq_zero.2 (filter_eq_empty_iff.2 fun c hc hQc => ?_)
            have := card_le_card hQc
            rw [(href T).rgraph c (mem_union_right _ hc)] at this
            omega
          have h2 : ((𝒲 T).filter fun W => Q ⊆ W.biUnion (ends' T) ∧
              (W.biUnion (ends' T)).Nonempty).card = 0 := by
            refine card_eq_zero.2 (filter_eq_empty_iff.2 fun W hW hQW => ?_)
            have := card_le_card (subset_inter hQW.1 hQZ)
            have := htr T W hW
            omega
          omega
        · exact le_rfl
      rw [sum_congr rfl fun T _ => h0 T, sum_const_zero]
      exact Nat.zero_le _
  have hTU : ∀ T : X₁.image tg₁, T.1 ⊆ Ut := fun T => by
    obtain ⟨x, hx, hxT⟩ := mem_image.1 T.2; rw [← hxT]; exact htU x hx
  have hTc : ∀ T : X₁.image tg₁, T.1.card = i := fun T => by
    obtain ⟨x, hx, hxT⟩ := mem_image.1 T.2; rw [← hxT]; exact htgc x hx
  have hTZ : ∀ T : X₁.image tg₁, Disjoint T.1 (Z₁ ∪ P₀) := fun T => by
    obtain ⟨x, hx, hxT⟩ := mem_image.1 T.2; rw [← hxT, hZoU]; exact htg x
  have hUZ : (Ut ∪ (Z₁ ∪ P₀)).card ≤ (K + 1) * Zo.card := by
    rw [hZoU]; refine (card_union_le _ _).trans ?_; rw [add_mul, one_mul]; omega
  obtain ⟨σ, hσ⟩ := exists_perm_spread hri (by omega) hdisj (fun T : X₁.image tg₁ => T.1)
    Subtype.val_injective hTU hTc hTZ (fun T => univ) A hAU hAs hΔb hμb (by omega) hmean
    (by omega) hZo1 hUZ
  set Bd₂ := Δ + 2 * (c₀ * B ^ r * D) + μ * (r * (K + 1 + 1)) * sc with hBd₂
  have hBd : Bd₂ ≤ (C₂ + CF) * D := by
    have h1 : Δ ≤ (CF + CF * (1 + CF)) * D := by
      have hB1 : Bd₁ ≤ D := by omega
      have : CF * Bd₁ ≤ CF * D := Nat.mul_le_mul_left _ hB1
      rw [hΔ]; nlinarith
    have h2 : μ * (r * (K + 1 + 1)) * sc ≤ μ * (r * (K + 1 + 1)) * D :=
      Nat.mul_le_mul_left _ (by omega)
    rw [hBd₂, hC₂]
    nlinarith
  refine ⟨Bd₂, hBd, ?_⟩
  refine trefOut_of_local E' g (fun T => mapEnds (σ T).1 (ends' T)) R 𝒲 hg
    (fun T c _ => ?_) hfr (fun T => ?_) (fun T y hy => ?_) (fun S hS => ?_) (fun S hS => ?_)
  · show (ends' T (g T c)).image (σ T).1 = bd₁ c
    rw [hge, image_perm_of_disjoint (σ T) (disjoint_of_subset_left (hbd c) hdisj)]
  · exact (residual_mapEnds (href T) (σ T).1 (fun _ _ => (σ T).1.injective.injOn)
      (σ T).1.injective.injOn (empty_subset _)).mono (by omega)
  · rw [← hZoU]
    exact image_perm_subset (σ T) (hcopy T y (mem_union_right _ hy))
  · refine le_trans (sum_le_sum fun T _ => ?_) (hσ S hS)
    have := card_univ_filter_sum (R T) (𝒲 T) (ends' T) (fun W => W.biUnion (ends' T))
      (fun B => S ⊆ T.1 ∪ B.image (σ T).1)
    exact le_of_le_of_eq (Nat.le_add_right _ _) this.symm
  · refine le_trans (sum_le_sum fun T _ => ?_) (hσ S hS)
    have := card_univ_filter_sum (R T) (𝒲 T) (ends' T) (fun W => W.biUnion (ends' T))
      (fun B => S ⊆ T.1 ∪ B.image (σ T).1)
    refine le_of_le_of_eq (le_trans (card_le_card fun W hW => ?_) (Nat.le_add_left _ _)) this.symm
    obtain ⟨hW𝒲, hSW⟩ := mem_filter.1 hW
    refine mem_filter.2 ⟨hW𝒲, hSW.trans (biUnion_subset.2 fun c hc => ?_)⟩
    exact union_subset_union subset_rfl (image_subset_image (subset_biUnion_of_mem _ hc))

end RefinedAbsorption.General
