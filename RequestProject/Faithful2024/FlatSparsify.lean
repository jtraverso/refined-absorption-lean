module
public import RequestProject.Sharp.Sparsify
public import RequestProject.Sharp.Better

/-!
# The Edge Sparsification Lemma with flatness (Lemma 3.12(2) of arXiv:2402.17855v1)

The existing `Sharp.edgeSparsification_holds` proves the window form of Lemma 3.12 without its
flatness output (2): *`R` is `(r-1)`-flat to `Y`*.  This file adds that output, for a prescribed
set `Y` (here `Yset`) of at least a third of the window, exactly as in the article: the special
sets `S_I` of Lemma 3.19 are chosen inside `Y`, so every new copy (an `r`-subset of
`e ∪ S_I` different from `e`, or a parallel copy of one) meets `Y`.

* `sparsify_build_flat`: `Sharp.sparsify_build` with the extra output that every new copy is an
  `r`-subset of a private clique `e ∪ S_I` different from `e` (same proof).
* `EdgeSparsificationFlat`, **`edgeSparsificationFlat_holds`**: the window form of Lemma 3.12 with
  flatness to a prescribed `Yset ⊆ U`, `|U| ≤ 3 |Yset|` (same proof, with the special sets chosen
  in `Yset`; the constants change accordingly).
-/

@[expose] public section

namespace RefinedAbsorption.Faithful2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Window RefinedAbsorption.Sharp
  RefinedAbsorption.FlatDown RefinedAbsorption.Dense RefinedAbsorption.RefineDown

/-- `Sharp.sparsify_build` with the extra output that every new copy is an `r`-subset of a
private clique `e ∪ S_I` different from `e`. -/
theorem sparsify_build_flat (q r : ℕ) (hr : 2 ≤ r) (hrq : r < q) :
    ∃ M' Cm : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (U : Finset (Fin n)) (X : Finset E) {k : ℕ} (φ : Fin n → Fin k)
      (Sp : Multiset (Fin k) → Finset (Fin n)),
      MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) →
      (∀ x ∈ X, (Sp (ptype φ (ends x))).card = q - r ∧
        Sp (ptype φ (ends x)) ⊆ U.filter fun v => φ v ∉ ptype φ (ends x)) →
      ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
        (R Y : Finset E') (𝒲 : Finset (Finset E')),
        Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
        IsResidualMultiRefiner q r (q.choose r + Cm) ends' (X.image g) R Y 𝒲 ∧ Y ⊆ R ∧
        (∀ c ∈ R, ends' c ⊆ U) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' Y S ≤ M' *
          (U.filter fun v => v ∉ S ∧ ∃ x ∈ X, insert v S ⊆ sClique ends φ Sp x ∧
            insert v S ≠ ends x).card) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ (1 + (M' + 2) ^ 2) *
          (fakeModulus q r * (q.choose r * (X.filter fun x => S ⊆ sClique ends φ Sp x).card))) ∧
        (∀ W ∈ 𝒲, (W.filter (· ∈ X.image g)).card ≤ 1) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤
          (X.filter fun x => S ⊆ sClique ends φ Sp x).card + Cm * ((1 + (M' + 2) ^ 2) *
          (fakeModulus q r * (q.choose r * (X.filter fun x => S ⊆ sClique ends φ Sp x).card)))) ∧
        (∀ c ∈ R, ∃ x ∈ X, ends' c ⊆ sClique ends φ Sp x ∧ ends' c ≠ ends x) := by
  obtain ⟨M', Cm, -, hmr⟩ := multiplicityReduction_quant q r hrq.le
  refine ⟨M', Cm, ?_⟩
  intro n E _ ends U X k φ Sp hXr hXU hSp
  set Vx := sClique ends φ Sp with hVx
  set Mf := fakeModulus q r with hMf
  have hsub : ∀ x ∈ X, ends x ⊆ Vx x := fun x _ => subset_union_left
  have hq : ∀ x ∈ X, (Vx x).card = q := by
    intro x hx
    rw [hVx, card_sClique (hXr x hx) (hSp x hx).1 (hSp x hx).2]; omega
  have hVU : ∀ x ∈ X, Vx x ⊆ U := fun x hx => sClique_subset (hXU x hx) (hSp x hx).2
  have h₁ := cliqueRefiner_residual hrq.le hXr hsub hq
  set R₁ := cliqueR ends r Mf Vx X with hR₁
  have hR₁r : MIsRGraph r (cEnds ends) R₁ := fun c hc => h₁.rgraph c (mem_union_right _ hc)
  obtain ⟨N, _, endsN, Rm, Ym, 𝒲m, hRm, hYmR, hm, hmult, hdegm, hparm⟩ :=
    hmr (cEnds ends) R₁ hR₁r
  have hinrfresh : ∀ c ∈ Rm.image (Sum.inr : N → CLab (Fin n) E ⊕ N), ∀ x : CLab (Fin n) E,
      Sum.inl x ≠ c := by
    intro c hc x hx
    obtain ⟨y, -, rfl⟩ := mem_image.1 hc
    exact Sum.inl_ne_inr hx
  have h12 := IsResidualMultiRefiner.compose (Sum.inl : CLab (Fin n) E → CLab (Fin n) E ⊕ N)
    Sum.inl_injective (fun c => rfl) h₁ subset_union_right hm hinrfresh
  have hone := oneX_compose (Sum.inl : CLab (Fin n) E → CLab (Fin n) E ⊕ N) Sum.inl_injective
    h₁.disjoint subset_rfl (cliqueRefiner_oneX (ends := ends) (r := r) (Vx := Vx) (X := X)) hm
    hinrfresh
  rw [image_image] at h12 hone
  set ends' : CLab (Fin n) E ⊕ N → Finset (Fin n) := Sum.elim (cEnds ends) endsN with hends'
  have hmdR₁ : ∀ S, mdeg (cEnds ends) R₁ S ≤
      Mf * (q.choose r * (X.filter fun x => S ⊆ Vx x).card) := fun S => mdeg_cliqueR_le hq S
  have hmdR : ∀ S, mdeg ends' (R₁.image Sum.inl ∪ Rm.image Sum.inr) S ≤ (1 + (M' + 2) ^ 2) *
      (Mf * (q.choose r * (X.filter fun x => S ⊆ Vx x).card)) := by
    intro S
    refine (mdeg_union_le _ _ _ S).trans ?_
    have e1 : mdeg ends' (R₁.image Sum.inl) S = mdeg (cEnds ends) R₁ S :=
      mdeg_image_eq (A := R₁) (fun c _ => rfl) Sum.inl_injective.injOn subset_rfl S
    have e2 : mdeg ends' (Rm.image Sum.inr) S ≤ (M' + 2) ^ 2 * mdeg (cEnds ends) R₁ S :=
      hdegm S
    rw [e1]
    have := hmdR₁ S
    calc mdeg (cEnds ends) R₁ S + mdeg ends' (Rm.image Sum.inr) S
        ≤ mdeg (cEnds ends) R₁ S + (M' + 2) ^ 2 * mdeg (cEnds ends) R₁ S := by omega
      _ = (1 + (M' + 2) ^ 2) * mdeg (cEnds ends) R₁ S := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ this
  refine ⟨CLab (Fin n) E ⊕ N, inferInstance, fun x => Sum.inl (Sum.inl x), ends',
    R₁.image Sum.inl ∪ Rm.image Sum.inr, Ym, _,
    fun x y h => Sum.inl_injective (Sum.inl_injective h), fun c => rfl, ?_, h12,
    hYmR.trans subset_union_right, ?_, ?_, fun S _ => hmdR S, ?_, ?_, ?_⟩
  · intro c hc x hx
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      obtain ⟨_, _, _, _, _, _, _, _, hc₁'⟩ := mem_cliqueR.1 hc₁
      rw [hc₁'] at hx
      exact Sum.inl_ne_inr (Sum.inl_injective hx)
    · obtain ⟨y, -, rfl⟩ := mem_image.1 h
      exact Sum.inl_ne_inr hx
  · intro c hc
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      obtain ⟨x, hx, h1, -, -⟩ := cliqueRefiner_ends hc₁
      exact h1.trans (hVU x hx)
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 h
      obtain ⟨c₁, hc₁, he⟩ := mem_image.1 (hRm y hy)
      show endsN y ⊆ U
      rw [← he]
      obtain ⟨x, hx, h1, -, -⟩ := cliqueRefiner_ends hc₁
      exact h1.trans (hVU x hx)
  · intro S hS
    have hYr : MIsRGraph r ends' Ym := fun c hc => hm.rgraph c (mem_union_right _ (hYmR hc))
    have hYU : ∀ c ∈ Ym, ends' c ⊆ U := by
      intro c hc
      obtain ⟨y, hy, rfl⟩ := mem_image.1 (hYmR hc)
      obtain ⟨c₁, hc₁, he⟩ := mem_image.1 (hRm y hy)
      show endsN y ⊆ U
      rw [← he]
      obtain ⟨x, hx, h1, -, -⟩ := cliqueRefiner_ends hc₁
      exact h1.trans (hVU x hx)
    refine (mdeg_le_mult_link hYr hYU hmult S (by omega)).trans (Nat.mul_le_mul_left _ ?_)
    refine card_le_card (monotone_filter_right _ fun v _ hv => ⟨hv.1, ?_⟩)
    obtain ⟨c, hc, hce⟩ := hv.2
    obtain ⟨y, hy, rfl⟩ := mem_image.1 (hYmR hc)
    obtain ⟨c₁, hc₁, he⟩ := mem_image.1 (hRm y hy)
    obtain ⟨x, hx, h1, -, h3⟩ := cliqueRefiner_ends hc₁
    have : cEnds ends c₁ = insert v S := he.trans hce
    exact ⟨x, hx, this ▸ h1, this ▸ h3⟩
  · exact hone
  · intro S hS
    have hSne : S.Nonempty := by rw [← card_pos, hS]; omega
    have hm1 : pdeg ends' 𝒲m S ≤ Cm * mdeg ends' (R₁.image Sum.inl ∪ Rm.image Sum.inr) S :=
      pdeg_le_of_parallel hm hparm hSne
    refine (pdeg_union_le _ _ _ S).trans (Nat.add_le_add ?_ (hm1.trans
      (Nat.mul_le_mul_left _ (hmdR S))))
    exact (pdeg_image_le Sum.inl (fun c => rfl) _ S).trans (pdeg_cliqueW_le hsub S)
  · intro c hc
    rcases mem_union.1 hc with h | h
    · obtain ⟨c₁, hc₁, rfl⟩ := mem_image.1 h
      obtain ⟨x, hx, h1, -, h3⟩ := cliqueRefiner_ends hc₁
      exact ⟨x, hx, h1, h3⟩
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 h
      obtain ⟨c₁, hc₁, he⟩ := mem_image.1 (hRm y hy)
      obtain ⟨x, hx, h1, -, h3⟩ := cliqueRefiner_ends hc₁
      refine ⟨x, hx, ?_, ?_⟩
      · show endsN y ⊆ _
        rw [← he]; exact h1
      · show endsN y ≠ _
        rw [← he]; exact h3


/-- **Edge Sparsification Lemma with flatness** (Lemma 3.12 of arXiv:2402.17855v1, window form,
including outcome (2)): as `Sharp.EdgeSparsification`, for a prescribed `Yset ⊆ U` with
`|U| ≤ 3 |Yset|`, and moreover every new copy meets `Yset` (so `R` is `(r-1)`-flat to `Yset`). -/
def EdgeSparsificationFlat (q r M₀ Cst m₀ : ℕ) : Prop :=
  ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n)) (U Yset : Finset (Fin n))
    (X : Finset E) (D : ℕ),
    MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ U) → m₀ < U.card → Yset ⊆ U →
    U.card ≤ 3 * Yset.card → (∀ e, mult ends X e ≤ M₀) →
    (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
    ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
      (R Y : Finset E') (𝒲 : Finset (Finset E')),
      Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
      IsResidualMultiRefiner q r Cst ends' (X.image g) R Y 𝒲 ∧ Y ⊆ R ∧
      (∀ c ∈ R, ends' c ⊆ U) ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' Y S ≤ Cst * winCost r U.card) ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends' R S ≤ Cst * (D + sharpCost r U.card)) ∧
      (∀ W ∈ 𝒲, (W.filter (· ∈ X.image g)).card ≤ 1) ∧
      (∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends' 𝒲 S ≤ Cst * (D + sharpCost r U.card)) ∧
      (∀ c ∈ R, (ends' c ∩ Yset).Nonempty)

/-- **Edge Sparsification Lemma with flatness**, for all `q > r ≥ 2`. -/
theorem edgeSparsificationFlat_holds {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) (M₀ : ℕ) :
    ∃ Cst m₀ : ℕ, EdgeSparsificationFlat q r M₀ Cst m₀ := by
  obtain ⟨M', Cm, hbuild⟩ := sparsify_build_flat q r hr hrq
  obtain ⟨s, hs⟩ : ∃ s, s = q - r := ⟨_, rfl⟩
  obtain ⟨M₁, hM₁⟩ : ∃ M₁, M₁ = max M₀ 1 := ⟨_, rfl⟩
  have hM₁1 : 1 ≤ M₁ := hM₁ ▸ le_max_right _ _
  obtain ⟨K₀', hK₀'⟩ : ∃ K₀', K₀' = r * 2 ^ r * (2 ^ s) ^ 2 * 8 ^ r * r.factorial + 1 := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = 4 ^ r * K₀' := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 2 ^ r * ((2 * r) ^ r * K₀) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = 4 * M₁ * (r + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨Mf, hMf⟩ : ∃ Mf, Mf = fakeModulus q r := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (1 + (M' + 2) ^ 2) * (Mf * (q.choose r * (Z * G))) := ⟨_, rfl⟩
  obtain ⟨Cst, hCst⟩ : ∃ Cst, Cst = q.choose r + Cm + A + (Z * G + Cm * A) + M' * (2 ^ r * (K₀ * q + 2 * r * K₀))
    := ⟨_, rfl⟩
  refine ⟨Cst, 4 * 64 ^ r * (2 * r).factorial + (12 * r) ^ r + 24 * r + 6 * q + 12, ?_⟩
  intro n E _ ends U Yset X D hXr hXU hU hYU hY3 hmult hdeg
  set m := U.card with hm
  obtain ⟨w, hw⟩ : ∃ w, w = winCost r m := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Nat.log 2 m + 1 := ⟨_, rfl⟩
  obtain ⟨Dn, hDn⟩ : ∃ Dn, Dn = D + 4 * M₁ * (r + 1) * w * L := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by omega
  have hw1 : 1 ≤ w := hw ▸ one_le_winCost r hm1
  have hwm : w ≤ m := hw ▸ winCost_le_self (by omega) hm1
  have hw12r : 12 * r ≤ w := by
    by_contra h
    push_neg at h
    have h1 : w ^ r < (12 * r) ^ r := Nat.pow_lt_pow_left h (by omega)
    have h2 : m ≤ m ^ (r - 1) := Nat.le_self_pow (by omega) m
    have h3 := pow_le_winCost_pow (r := r) (by omega) m
    rw [← hw] at h3
    omega
  have hw4r : 4 * r ≤ w := by omega
  -- 1. the partition
  obtain ⟨φ, hpartR, hdegR⟩ := exists_partition ends X U (r := r) (k := w) (M₀ := M₁) (D := D)
    (by omega) hw1 hM₁1 hXr hXU (fun e => (hmult e).trans (hM₁ ▸ le_max_left _ _)) hdeg (Dn : ℝ)
    (by rw [hDn]; exact_mod_cast Nat.le_add_right _ _)
    (by rw [hDn, hL, hw]; exact partition_union_bound (by omega) hM₁1 (by omega))
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw1
  obtain ⟨P, hP⟩ : ∃ P, P = 2 * m / w := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 * Dn / w := ⟨_, rfl⟩
  have hpart : ∀ i, (U.filter fun v => φ v = i).card ≤ P := by
    intro i
    rw [hP, Nat.le_div_iff_mul_le hw1]
    have := hpartR i
    rw [le_div_iff₀ hw0] at this
    exact_mod_cast this
  have hDnle : Dn ≤ G * (D + sharpCost r m) := by
    have hsc : sharpCost r m = w * L := by rw [sharpCost, hw, hL]
    rw [hsc, hDn, hG]
    ring_nf
    omega
  have hdegp : ∀ S : Finset (Fin n), S.card = r - 1 → ∀ i,
      (X.filter fun x => S ⊆ ends x ∧ ∀ v ∈ ends x \ S, φ v = i).card ≤ Q := by
    intro S hS i
    rw [hQ, Nat.le_div_iff_mul_le hw1]
    have := hdegR S hS i
    rw [le_div_iff₀ hw0] at this
    norm_cast at this
    convert this using 3
    ext x
    simp
  have hPw : P * w ≤ 2 * m := by rw [hP]; exact Nat.div_mul_le_self _ _
  have hQw : Q * w ≤ 2 * Dn := by rw [hQ]; exact Nat.div_mul_le_self _ _
  -- 2. the special sets
  set Types := X.image fun x => ptype φ (ends x) with hTypesdef
  have hTypes : ∀ I ∈ Types, Multiset.card I = r := by
    intro I hI
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hI
    rw [card_ptype]; exact hXr x hx
  obtain ⟨N, hN⟩ : ∃ N, N = m / 3 / 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℕ, B = fun ℓ => if ℓ = 0 then w else
    r * (2 ^ r * w ^ (ℓ + 1) * s.choose ℓ ^ 2) / N.choose ℓ + 1 := ⟨_, rfl⟩
  have hB1 : ∀ ℓ, 1 ≤ B ℓ := by
    intro ℓ
    rw [hB]
    dsimp only
    split_ifs
    · exact hw1
    · exact Nat.le_add_left 1 _
  have hrP : 6 * (r * P) ≤ m := by
    have h1 : P * (12 * r) ≤ 2 * m := (Nat.mul_le_mul_left _ hw12r).trans hPw
    have h2 : 12 * (r * P) ≤ 2 * m := by linarith [show P * (12 * r) = 12 * (r * P) by ring]
    omega
  have hNI : ∀ I ∈ Types, N ≤ (Yset.filter fun v => φ v ∉ I).card := by
    intro I hI
    have h1 := card_parts_le hpart (hTypes I hI).le
    have h1' : (Yset.filter fun v => φ v ∈ I).card ≤ (U.filter fun v => φ v ∈ I).card :=
      card_le_card (filter_subset_filter _ hYU)
    have h2 := card_filter_add_card_filter_not (s := Yset) (fun v => φ v ∈ I)
    omega
  have hNs : s ≤ N := by rw [hs, hN]; omega
  have hnum : ∀ ℓ, 1 ≤ ℓ → ℓ < r →
      r * (2 ^ r * w ^ (ℓ + 1) * s.choose ℓ ^ 2) < B ℓ * N.choose ℓ := by
    intro ℓ hℓ hℓr
    have hc : 0 < N.choose ℓ := Nat.choose_pos (by omega)
    simp only [hB, if_neg (show ℓ ≠ 0 by omega)]
    rw [add_mul, one_mul]
    exact Nat.lt_div_mul_add hc
  obtain ⟨Sp, hSp, hspr⟩ := exists_special_sets (s := s) (by omega) φ Yset Types hTypes B hB1 N hNI
    hNs hnum
  have hBm : ∀ ℓ, ℓ ≤ r - 1 → B ℓ * m ^ ℓ ≤ K₀ * w ^ (ℓ + 1) := by
    intro ℓ hℓ
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
    · simp only [hB, if_pos rfl, pow_zero, mul_one, zero_add, pow_one]
      exact Nat.le_mul_of_pos_left _ (by rw [hK₀, hK₀']; positivity)
    · simp only [hB, if_neg (show ℓ ≠ 0 by omega)]
      have := pow_le_winCost_pow_succ (r := r) (by omega) hℓ hm1
      rw [← hw] at this
      have hm3 : (m / 3) ^ ℓ ≤ w ^ (ℓ + 1) :=
        le_trans (Nat.pow_le_pow_left (Nat.div_le_self _ _) _) this
      have key := spreadBound_le (s := s) (m := m / 3) (w := w) (by omega : 1 ≤ r) hℓ (by omega) hm3
      rw [← hN, ← hK₀'] at key
      have hm4 : m ^ ℓ ≤ 4 ^ r * (m / 3) ^ ℓ := by
        calc m ^ ℓ ≤ (4 * (m / 3)) ^ ℓ := Nat.pow_le_pow_left (by omega) _
          _ = 4 ^ ℓ * (m / 3) ^ ℓ := by rw [mul_pow]
          _ ≤ 4 ^ r * (m / 3) ^ ℓ :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      calc (r * (2 ^ r * w ^ (ℓ + 1) * s.choose ℓ ^ 2) / N.choose ℓ + 1) * m ^ ℓ
          ≤ (r * (2 ^ r * w ^ (ℓ + 1) * s.choose ℓ ^ 2) / N.choose ℓ + 1) *
            (4 ^ r * (m / 3) ^ ℓ) := Nat.mul_le_mul_left _ hm4
        _ = 4 ^ r * ((r * (2 ^ r * w ^ (ℓ + 1) * s.choose ℓ ^ 2) / N.choose ℓ + 1) *
            (m / 3) ^ ℓ) := by ring
        _ ≤ 4 ^ r * (K₀' * w ^ (ℓ + 1)) := Nat.mul_le_mul_left _ key
        _ = K₀ * w ^ (ℓ + 1) := by rw [hK₀]; ring
  have hspread : ∀ (J : Multiset (Fin w)) (T : Finset (Fin n)),
      Multiset.card J + T.card = r - 1 → (spreadSet ends φ Sp X J T).card ≤ B T.card := by
    intro J T hJT
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · rw [h0]
      simp only [hB, if_pos rfl]
      have h1 := card_types_above_le Types hTypes J
      rw [show r - Multiset.card J = 1 by omega, pow_one] at h1
      exact (card_le_card (monotone_filter_right _ fun I _ h => h.2)).trans h1
    · exact hspr J T hJT h0
  have hSpX : ∀ x ∈ X, (Sp (ptype φ (ends x))).card = s ∧
      Sp (ptype φ (ends x)) ⊆ U.filter fun v => φ v ∉ ptype φ (ends x) :=
    fun x hx => ⟨(hSp _ (mem_image_of_mem _ hx)).1,
      (hSp _ (mem_image_of_mem _ hx)).2.trans (filter_subset_filter _ hYU)⟩
  have hSpY : ∀ x ∈ X, Sp (ptype φ (ends x)) ⊆ Yset :=
    fun x hx => (hSp _ (mem_image_of_mem _ hx)).2.trans (filter_subset _ _)
  -- 3. the refiner
  obtain ⟨E', _, g, ends', R, Y, 𝒲, hg, hends, hfresh, hres, hYR, hRU, hdY, hdR, hone, hpd, hmeet⟩ :=
    hbuild n ends U X φ Sp hXr hXU (by rw [← hs]; exact hSpX)
  -- 4. counting
  have hF : ∀ S : Finset (Fin n), S.card = r - 1 →
      (X.filter fun x => S ⊆ sClique ends φ Sp x).card ≤ Z * Dn := by
    intro S hS
    refine (card_clique_supersets_le (k := w) (P := P) (Q := Q) (B := B) (Sp := Sp) hXr hXU hpart
      ?_ hspread (by omega) hS).trans ?_
    · intro S' hS' i
      convert hdegp S' hS' i using 2
      ext x
      simp
    refine (sum_powerset_le S _ ((2 * r) ^ r * K₀ * Dn) fun T hT => ?_).trans ?_
    · have hTc : T.card ≤ r - 1 := (card_le_card (mem_powerset.1 hT)).trans hS.le
      refine (spread_term_le hw1 (hBm _ hTc) hPw hQw).trans ?_
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by omega) (by omega)))
    · rw [hS, hZ]
      calc 2 ^ (r - 1) * ((2 * r) ^ r * K₀ * Dn) ≤ 2 ^ r * ((2 * r) ^ r * K₀ * Dn) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = 2 ^ r * ((2 * r) ^ r * K₀) * Dn := by ring
  have hlink : ∀ S : Finset (Fin n), S.card = r - 1 →
      (U.filter fun v => v ∉ S ∧ ∃ x ∈ X, insert v S ⊆ sClique ends φ Sp x ∧
        insert v S ≠ ends x).card ≤ 2 ^ r * (K₀ * q + 2 * r * K₀) * w := by
    intro S hS
    refine (card_clique_link_le (q := q) hXr hpart (fun x hx => hs ▸ (hSpX x hx).1.le) hspread hS
      (by omega)).trans ?_
    have hTc : ∀ T ∈ S.powerset, T.card ≤ r - 1 :=
      fun T hT => (card_le_card (mem_powerset.1 hT)).trans hS.le
    have h1 : ∑ T ∈ S.powerset, B T.card * (q - r) ≤ 2 ^ S.card * (K₀ * w * q) := by
      refine sum_powerset_le S _ _ fun T hT => ?_
      exact Nat.mul_le_mul (spread_le hwm hm1 (hBm _ (hTc T hT))) (Nat.sub_le _ _)
    have h2 : ∑ T ∈ S.powerset.filter (fun T => T.Nonempty), B T.card * (r * P) ≤
        2 ^ S.card * (2 * r * K₀ * w) := by
      calc ∑ T ∈ S.powerset.filter (fun T => T.Nonempty), B T.card * (r * P)
          ≤ ∑ _T ∈ S.powerset.filter (fun T => T.Nonempty), 2 * r * K₀ * w := by
            refine sum_le_sum fun T hT => ?_
            obtain ⟨hT1, hT2⟩ := mem_filter.1 hT
            exact link_term_le hw1 hwm (card_pos.2 hT2) (hBm _ (hTc T hT1)) hPw
        _ ≤ 2 ^ S.card * (2 * r * K₀ * w) := by
            rw [sum_const, smul_eq_mul, ← card_powerset]
            exact Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))
    rw [hS] at h1 h2
    calc ∑ T ∈ S.powerset, B T.card * (q - r) +
          ∑ T ∈ S.powerset.filter (fun T => T.Nonempty), B T.card * (r * P)
        ≤ 2 ^ (r - 1) * (K₀ * w * q) + 2 ^ (r - 1) * (2 * r * K₀ * w) := Nat.add_le_add h1 h2
      _ = 2 ^ (r - 1) * (K₀ * q + 2 * r * K₀) * w := by ring
      _ ≤ 2 ^ r * (K₀ * q + 2 * r * K₀) * w :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (Nat.pow_le_pow_right (by norm_num) (by omega)))
  refine ⟨E', inferInstance, g, ends', R, Y, 𝒲, hg, hends, hfresh, hres.mono ?_, hYR, hRU, ?_, ?_,
    hone, ?_, ?_⟩
  · rw [hCst]; omega
  · intro S hS
    refine (hdY S hS).trans ((Nat.mul_le_mul_left _ (hlink S hS)).trans ?_)
    rw [← hw]
    calc M' * (2 ^ r * (K₀ * q + 2 * r * K₀) * w) = M' * (2 ^ r * (K₀ * q + 2 * r * K₀)) * w := by
          ring
      _ ≤ Cst * w := Nat.mul_le_mul_right _ (by rw [hCst]; omega)
  · intro S hS
    have hFG : (X.filter fun x => S ⊆ sClique ends φ Sp x).card ≤ Z * G * (D + sharpCost r m) :=
      (hF S hS).trans (by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hDnle)
    refine (hdR S hS).trans ?_
    calc (1 + (M' + 2) ^ 2) * (fakeModulus q r * (q.choose r *
          (X.filter fun x => S ⊆ sClique ends φ Sp x).card))
        ≤ (1 + (M' + 2) ^ 2) * (fakeModulus q r * (q.choose r * (Z * G * (D + sharpCost r m)))) := by
          gcongr
      _ = A * (D + sharpCost r m) := by rw [hA, hMf]; ring
      _ ≤ Cst * (D + sharpCost r m) := Nat.mul_le_mul_right _ (by rw [hCst]; omega)
  · intro S hS
    have hFG : (X.filter fun x => S ⊆ sClique ends φ Sp x).card ≤ Z * G * (D + sharpCost r m) :=
      (hF S hS).trans (by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hDnle)
    refine (hpd S hS).trans ?_
    calc (X.filter fun x => S ⊆ sClique ends φ Sp x).card + Cm * ((1 + (M' + 2) ^ 2) *
          (fakeModulus q r * (q.choose r * (X.filter fun x => S ⊆ sClique ends φ Sp x).card)))
        ≤ Z * G * (D + sharpCost r m) + Cm * ((1 + (M' + 2) ^ 2) *
          (fakeModulus q r * (q.choose r * (Z * G * (D + sharpCost r m))))) := by
          gcongr
      _ = (Z * G + Cm * A) * (D + sharpCost r m) := by rw [hA, hMf]; ring
      _ ≤ Cst * (D + sharpCost r m) := Nat.mul_le_mul_right _ (by rw [hCst]; omega)
  · intro c hc
    obtain ⟨x, hx, hsub, hne⟩ := hmeet c hc
    have hcr : (ends' c).card = r := hres.rgraph c (mem_union_right _ hc)
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    apply hne
    have hsub' : ends' c ⊆ ends x := by
      intro v hv
      have hv' := hsub hv
      unfold sClique at hv'
      rcases mem_union.1 hv' with h | h
      · exact h
      · have : v ∈ ends' c ∩ Yset := mem_inter.2 ⟨hv, hSpY x hx h⟩
        rw [hemp] at this
        exact absurd this (notMem_empty v)
    exact eq_of_subset_of_card_le hsub' (by rw [hcr, hXr x hx])

end RefinedAbsorption.Faithful2024
