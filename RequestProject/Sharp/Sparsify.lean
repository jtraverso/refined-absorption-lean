module
public import RequestProject.Sharp.SparsBuild
public import RequestProject.Sharp.SparsArith
public import RequestProject.Sharp.Special
public import RequestProject.Sharp.Partition

/-!
# The Edge Sparsification Lemma (Lemma 3.12)

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Lemma 3.12 and its proof (§3.4).

**`edgeSparsification_holds`**: for all `q > r ≥ 2` and every multiplicity bound `M₀` there
are constants `Cst, m₀` with `EdgeSparsification q r M₀ Cst m₀` (the window form of Lemma 3.12
stated in `Sharp/Better.lean`).

Proof, following the paper with `k = w = ⌈m^{1-1/r}⌉` parts, `m = |U|`:
1. a quasi-random partition `φ : V → Fin w` (Proposition 3.17, `exists_partition`) with
   `D* = D + 4 M₀ (r+1) w (⌊log₂ m⌋ + 1)`: parts meet `U` in `P ≤ 2m/w` vertices and the
   `(r-1)`-sets have `Q ≤ 2D*/w` copies towards every part;
2. special sets `Sp I` (Lemma 3.19, `exists_special_sets`) of size `q - r` avoiding the parts
   of `I`, with spread bounds `B ℓ` satisfying `B ℓ · m^ℓ ≤ K₀ · w^{ℓ+1}`;
3. the private-clique refiner and Multiplicity Reduction (`sparsify_build`);
4. the counting of `Sharp/SparsCount.lean` turns the bounds of step 3 into
   `Δ(R), Δ(𝒲) ≤ Cst · (D + sharpCost r m)` and `Δ(residue) ≤ Cst · w`.
-/

@[expose] public section

namespace RefinedAbsorption.Sharp

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Window

lemma sum_powerset_le {V : Type*} [DecidableEq V] (S : Finset V) (f : Finset V → ℕ) (c : ℕ)
    (h : ∀ T ∈ S.powerset, f T ≤ c) : ∑ T ∈ S.powerset, f T ≤ 2 ^ S.card * c := by
  calc ∑ T ∈ S.powerset, f T ≤ ∑ _T ∈ S.powerset, c := sum_le_sum h
    _ = 2 ^ S.card * c := by rw [sum_const, card_powerset, smul_eq_mul]

/-- **Edge Sparsification Lemma** (Delcourt–Postle, Lemma 3.12), window form. -/
theorem edgeSparsification_holds {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) (M₀ : ℕ) :
    ∃ Cst m₀ : ℕ, EdgeSparsification q r M₀ Cst m₀ := by
  obtain ⟨M', Cm, hbuild⟩ := sparsify_build q r hr hrq
  obtain ⟨s, hs⟩ : ∃ s, s = q - r := ⟨_, rfl⟩
  obtain ⟨M₁, hM₁⟩ : ∃ M₁, M₁ = max M₀ 1 := ⟨_, rfl⟩
  have hM₁1 : 1 ≤ M₁ := hM₁ ▸ le_max_right _ _
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = r * 2 ^ r * (2 ^ s) ^ 2 * 8 ^ r * r.factorial + 1 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 2 ^ r * ((2 * r) ^ r * K₀) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = 4 * M₁ * (r + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨Mf, hMf⟩ : ∃ Mf, Mf = fakeModulus q r := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (1 + (M' + 2) ^ 2) * (Mf * (q.choose r * (Z * G))) := ⟨_, rfl⟩
  obtain ⟨Cst, hCst⟩ : ∃ Cst, Cst = q.choose r + Cm + A + (Z * G + Cm * A) + M' * (2 ^ r * (K₀ * q + 2 * r * K₀))
    := ⟨_, rfl⟩
  refine ⟨Cst, 4 * 64 ^ r * (2 * r).factorial + (4 * r) ^ r + 8 * r + 2 * q, ?_⟩
  intro n E _ ends U X D hXr hXU hU hmult hdeg
  set m := U.card with hm
  obtain ⟨w, hw⟩ : ∃ w, w = winCost r m := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Nat.log 2 m + 1 := ⟨_, rfl⟩
  obtain ⟨Dn, hDn⟩ : ∃ Dn, Dn = D + 4 * M₁ * (r + 1) * w * L := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by omega
  have hw1 : 1 ≤ w := hw ▸ one_le_winCost r hm1
  have hwm : w ≤ m := hw ▸ winCost_le_self (by omega) hm1
  have hw4r : 4 * r ≤ w := by
    by_contra h
    push_neg at h
    have h1 : w ^ r < (4 * r) ^ r := Nat.pow_lt_pow_left h (by omega)
    have h2 : m ≤ m ^ (r - 1) := Nat.le_self_pow (by omega) m
    have h3 := pow_le_winCost_pow (r := r) (by omega) m
    rw [← hw] at h3
    omega
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
  obtain ⟨N, hN⟩ : ∃ N, N = m / 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℕ, B = fun ℓ => if ℓ = 0 then w else
    r * (2 ^ r * w ^ (ℓ + 1) * s.choose ℓ ^ 2) / N.choose ℓ + 1 := ⟨_, rfl⟩
  have hB1 : ∀ ℓ, 1 ≤ B ℓ := by
    intro ℓ
    rw [hB]
    dsimp only
    split_ifs
    · exact hw1
    · exact Nat.le_add_left 1 _
  have hrP : r * P ≤ N := by
    have h1 : P * (4 * r) ≤ 2 * m := (Nat.mul_le_mul_left _ hw4r).trans hPw
    have h2 : 4 * (r * P) ≤ 2 * m := by linarith [show P * (4 * r) = 4 * (r * P) by ring]
    omega
  have hNI : ∀ I ∈ Types, N ≤ (U.filter fun v => φ v ∉ I).card := by
    intro I hI
    have h1 := card_parts_le hpart (hTypes I hI).le
    have h2 := card_filter_add_card_filter_not (s := U) (fun v => φ v ∈ I)
    omega
  have hNs : s ≤ N := by rw [hs, hN]; omega
  have hnum : ∀ ℓ, 1 ≤ ℓ → ℓ < r →
      r * (2 ^ r * w ^ (ℓ + 1) * s.choose ℓ ^ 2) < B ℓ * N.choose ℓ := by
    intro ℓ hℓ hℓr
    have hc : 0 < N.choose ℓ := Nat.choose_pos (by omega)
    simp only [hB, if_neg (show ℓ ≠ 0 by omega)]
    rw [add_mul, one_mul]
    exact Nat.lt_div_mul_add hc
  obtain ⟨Sp, hSp, hspr⟩ := exists_special_sets (s := s) (by omega) φ U Types hTypes B hB1 N hNI
    hNs hnum
  have hBm : ∀ ℓ, ℓ ≤ r - 1 → B ℓ * m ^ ℓ ≤ K₀ * w ^ (ℓ + 1) := by
    intro ℓ hℓ
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
    · simp only [hB, if_pos rfl, pow_zero, mul_one, zero_add, pow_one]
      exact Nat.le_mul_of_pos_left _ (by omega)
    · simp only [hB, if_neg (show ℓ ≠ 0 by omega)]
      rw [hN, hK₀]
      have := pow_le_winCost_pow_succ (r := r) (by omega) hℓ hm1
      rw [← hw] at this
      exact spreadBound_le (by omega) hℓ (by omega) this
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
    fun x hx => hSp _ (mem_image_of_mem _ hx)
  -- 3. the refiner
  obtain ⟨E', _, g, ends', R, Y, 𝒲, hg, hends, hfresh, hres, hYR, hRU, hdY, hdR, hone, hpd⟩ :=
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
    hone, ?_⟩
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


/-- **Theorem 3.8 from the link levels alone.**  With the Edge Sparsification Lemma proved,
strong multi-refiners with the exact budget `C · max(D, n^{1-1/r} log n)` exist as soon as
placed link refiners with additive term `sharpCost r |Z|` exist at the levels `1 ≤ i < r - 1`
(for `r = 2` there are no such levels). -/
theorem nativeStrongMultiRefiners_of_levels {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r - 1 →
      RefinedAbsorption.Placement.PlacedLinkLevelA q r i (sharpCost r)) :
    RefinedAbsorption.Placement.NativeStrongMultiRefiners q r :=
  nativeStrongMultiRefiners_of_sparsify_levels hr hrq (edgeSparsification_holds hr hrq) hL

/-- **Theorem 3.8 for graphs (`r = 2`)**, with the exact budget. -/
theorem nativeStrongMultiRefiners_two_sharp {q : ℕ} (hq : 2 < q) :
    RefinedAbsorption.Placement.NativeStrongMultiRefiners q 2 :=
  nativeStrongMultiRefiners_of_levels le_rfl hq fun i hi h => absurd h (by omega)

end RefinedAbsorption.Sharp
