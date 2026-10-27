module
public import RequestProject.Counting

/-!
# Special sets for the types of a partition (Lemma 3.19)

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Proposition 3.18 and Lemma 3.19.

Let `φ : V → Fin k` be a partition of the vertices into `k` parts and let `Types` be a finite set
of `r`-multisets of parts.  For every type `I` we choose a special `s`-set `Sp I` of vertices of
a window `U` avoiding the parts of `I`, so that the special sets are *spread*: for every multiset
`J` of parts and every vertex set `T` with `|J| + |T| = r - 1` and `|T| ≥ 1`, at most `B |T|`
types `I` satisfy `T ⊆ Sp I` and `J ≤ I` (**`exists_special_sets`**).

The proof is the deterministic greedy argument of the paper: the types are treated one at a
time, and the special set of the current type avoids every "saturated" set `T` (one for which the
bound `B |T|` is already attained for some `J ≤ I`).  The number of `s`-sets containing a
saturated set is counted as in Proposition 3.18.

* `card_multisets_le`: there are at most `k^s` multisets of size `s` of parts;
* `card_types_above_le`: at most `k^{r - |J|}` types `I` (of size `r`) satisfy `J ≤ I`.
-/

@[expose] public section

namespace RefinedAbsorption.Sharp

open Finset

/-- At most `k^s` multisets of size `s` over `Fin k`. -/
theorem card_multisets_le {k s : ℕ} (𝒯 : Finset (Multiset (Fin k)))
    (h𝒯 : ∀ M ∈ 𝒯, Multiset.card M = s) : 𝒯.card ≤ k ^ s := by
  have hsub : 𝒯 ⊆ (univ : Finset (Fin s → Fin k)).image fun f => (univ : Finset (Fin s)).val.map f := by
    intro M hM
    rw [mem_image]
    have hl : M.toList.length = s := by rw [Multiset.length_toList]; exact h𝒯 M hM
    refine ⟨fun i => M.toList.get (Fin.cast hl.symm i), mem_univ _, ?_⟩
    rw [Fin.univ_val_map]
    have := List.ofFn_congr hl M.toList.get
    rw [List.ofFn_get] at this
    rw [← this, Multiset.coe_toList]
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  simp

/-- At most `k^{r - |J|}` multisets of size `r` lie above `J`. -/
theorem card_types_above_le {k r : ℕ} (𝒯 : Finset (Multiset (Fin k)))
    (h𝒯 : ∀ M ∈ 𝒯, Multiset.card M = r) (J : Multiset (Fin k)) :
    (𝒯.filter fun I => J ≤ I).card ≤ k ^ (r - Multiset.card J) := by
  rw [← card_image_of_injOn (f := fun I => I - J)]
  · refine card_multisets_le _ fun M hM => ?_
    obtain ⟨I, hI, rfl⟩ := mem_image.1 hM
    rw [mem_filter] at hI
    rw [Multiset.card_sub hI.2, h𝒯 I hI.1]
  · intro I hI I' hI' h
    simp only [coe_filter, Set.mem_setOf_eq] at hI hI'
    have e1 : J + (I - J) = I := add_tsub_cancel_of_le hI.2
    have e2 : J + (I' - J) = I' := add_tsub_cancel_of_le hI'.2
    simp only at h
    rw [← e1, ← e2, h]

/-- The sub-multisets of an `r`-multiset of a given size are at most `2^r`. -/
theorem card_submultisets_le {k r : ℕ} (I : Multiset (Fin k)) (hI : Multiset.card I = r)
    (c : ℕ) :
    ((Multiset.powerset I).toFinset.filter fun J => Multiset.card J = c).card ≤ 2 ^ r := by
  refine (card_filter_le _ _).trans ((Multiset.toFinset_card_le _).trans ?_)
  rw [Multiset.card_powerset, hI]

variable {V : Type*} [DecidableEq V]

/-- Number of `s`-subsets of `Y` containing a fixed `ℓ`-subset `T ⊆ Y`. -/
theorem card_supersets_le_choose {Y T : Finset V} {s : ℕ} (hT : T ⊆ Y) :
    ((Y.powersetCard s).filter fun A => T ⊆ A).card ≤ (Y.card - T.card).choose (s - T.card) := by
  by_cases hTs : T.card ≤ s
  · rw [RefinedAbsorption.card_powersetCard_filter_superset hT hTs]
  · rw [card_eq_zero.2 (filter_eq_empty_iff.2 fun A hA hTA => hTs
      ((card_le_card hTA).trans (mem_powersetCard.1 hA).2.le))]
    exact Nat.zero_le _

/-- Double counting for the saturated sets of a fixed `J`. -/
theorem card_saturated_mul_le {k r s ℓ : ℕ} (P : Finset (Multiset (Fin k)))
    (hP : ∀ I ∈ P, Multiset.card I = r) (Sp : Multiset (Fin k) → Finset V)
    (hSp : ∀ I ∈ P, (Sp I).card = s) (Y : Finset V) (J : Multiset (Fin k))
    (hJ : Multiset.card J + ℓ = r - 1) (hr : 1 ≤ r) (b : ℕ) :
    ((Y.powersetCard ℓ).filter fun T =>
        b ≤ (P.filter fun I => T ⊆ Sp I ∧ J ≤ I).card).card * b ≤
      k ^ (ℓ + 1) * s.choose ℓ := by
  set F := (Y.powersetCard ℓ).filter fun T => b ≤ (P.filter fun I => T ⊆ Sp I ∧ J ≤ I).card
  have h1 : F.card * b ≤ ∑ T ∈ Y.powersetCard ℓ, (P.filter fun I => T ⊆ Sp I ∧ J ≤ I).card := by
    have := card_nsmul_le_sum F (fun T => (P.filter fun I => T ⊆ Sp I ∧ J ≤ I).card) b
      (fun T hT => (mem_filter.1 hT).2)
    rw [smul_eq_mul] at this
    exact this.trans (sum_le_sum_of_subset (filter_subset _ _))
  have h2 : ∑ T ∈ Y.powersetCard ℓ, (P.filter fun I => T ⊆ Sp I ∧ J ≤ I).card =
      ∑ I ∈ P.filter (fun I => J ≤ I), ((Y.powersetCard ℓ).filter fun T => T ⊆ Sp I).card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun I _ => ?_
    by_cases hJI : J ≤ I
    · simp only [hJI, and_true, if_true]
    · simp only [hJI, and_false, if_false, sum_const_zero]
  have h3 : ∀ I ∈ P.filter (fun I => J ≤ I),
      ((Y.powersetCard ℓ).filter fun T => T ⊆ Sp I).card ≤ s.choose ℓ := by
    intro I hI
    have : (Y.powersetCard ℓ).filter (fun T => T ⊆ Sp I) ⊆ (Sp I).powersetCard ℓ := by
      intro T hT
      rw [mem_filter, mem_powersetCard] at hT
      exact mem_powersetCard.2 ⟨hT.2, hT.1.2⟩
    refine (card_le_card this).trans ?_
    rw [card_powersetCard, hSp I (mem_filter.1 hI).1]
  have h4 := card_types_above_le P hP J
  have hexp : r - Multiset.card J = ℓ + 1 := by omega
  rw [hexp] at h4
  calc F.card * b ≤ _ := h1
    _ = _ := h2
    _ ≤ (P.filter fun I => J ≤ I).card * s.choose ℓ := by
        have := sum_le_sum h3
        rwa [sum_const, smul_eq_mul] at this
    _ ≤ k ^ (ℓ + 1) * s.choose ℓ := Nat.mul_le_mul_right _ h4

/-- **Special sets** (Lemma 3.19); see the module docstring. -/
theorem exists_special_sets {k r s : ℕ} (hr : 1 ≤ r) (φ : V → Fin k) (U : Finset V)
    (Types : Finset (Multiset (Fin k))) (hTypes : ∀ I ∈ Types, Multiset.card I = r)
    (B : ℕ → ℕ) (hB1 : ∀ ℓ, 1 ≤ B ℓ) (N : ℕ)
    (hN : ∀ I ∈ Types, N ≤ (U.filter fun v => φ v ∉ I).card) (hNs : s ≤ N)
    (hnum : ∀ ℓ, 1 ≤ ℓ → ℓ < r →
      r * (2 ^ r * k ^ (ℓ + 1) * s.choose ℓ ^ 2) < B ℓ * N.choose ℓ) :
    ∃ Sp : Multiset (Fin k) → Finset V,
      (∀ I ∈ Types, (Sp I).card = s ∧ Sp I ⊆ U.filter fun v => φ v ∉ I) ∧
      ∀ (J : Multiset (Fin k)) (T : Finset V), Multiset.card J + T.card = r - 1 → 1 ≤ T.card →
        (Types.filter fun I => T ⊆ Sp I ∧ J ≤ I).card ≤ B T.card := by
  suffices key : ∀ P ⊆ Types, ∃ Sp : Multiset (Fin k) → Finset V,
      (∀ I ∈ P, (Sp I).card = s ∧ Sp I ⊆ U.filter fun v => φ v ∉ I) ∧
      ∀ (J : Multiset (Fin k)) (T : Finset V), Multiset.card J + T.card = r - 1 → 1 ≤ T.card →
        (P.filter fun I => T ⊆ Sp I ∧ J ≤ I).card ≤ B T.card from key Types subset_rfl
  intro P
  induction P using Finset.induction_on with
  | empty => exact fun _ => ⟨fun _ => ∅, by simp, by simp⟩
  | @insert I₀ P hI₀ ih =>
  intro hsub
  obtain ⟨Sp, hSp, hspread⟩ := ih ((subset_insert _ _).trans hsub)
  have hPT : ∀ I ∈ P, Multiset.card I = r := fun I hI => hTypes I (hsub (mem_insert_of_mem hI))
  have hI₀T : I₀ ∈ Types := hsub (mem_insert_self _ _)
  set Y := U.filter fun v => φ v ∉ I₀ with hY
  have hYN : N ≤ Y.card := hN I₀ hI₀T
  set cnt : Multiset (Fin k) → Finset V → ℕ :=
    fun J T => (P.filter fun I => T ⊆ Sp I ∧ J ≤ I).card with hcnt
  set Js : ℕ → Finset (Multiset (Fin k)) :=
    fun ℓ => (Multiset.powerset I₀).toFinset.filter fun J => Multiset.card J = r - 1 - ℓ with hJs
  set BadJ : Multiset (Fin k) → ℕ → Finset (Finset V) :=
    fun J ℓ => (Y.powersetCard ℓ).filter fun T => B ℓ ≤ cnt J T with hBadJ
  set Ls := (range r).filter fun ℓ => 1 ≤ ℓ with hLs
  -- the covered `s`-sets
  set Cov := (Y.powersetCard s).filter fun A =>
    ∃ ℓ ∈ Ls, ∃ J ∈ Js ℓ, ∃ T ∈ BadJ J ℓ, T ⊆ A with hCov
  have hCov_sub : Cov ⊆ Ls.biUnion fun ℓ => (Js ℓ).biUnion fun J => (BadJ J ℓ).biUnion fun T =>
      (Y.powersetCard s).filter fun A => T ⊆ A := by
    intro A hA
    rw [mem_filter] at hA
    obtain ⟨hAY, ℓ, hℓ, J, hJ, T, hT, hTA⟩ := hA
    exact mem_biUnion.2 ⟨ℓ, hℓ, mem_biUnion.2 ⟨J, hJ, mem_biUnion.2 ⟨T, hT,
      mem_filter.2 ⟨hAY, hTA⟩⟩⟩⟩
  -- the count for one level
  set Xl : ℕ → ℕ := fun ℓ => ∑ J ∈ Js ℓ, (BadJ J ℓ).card * (Y.card - ℓ).choose (s - ℓ) with hXl
  have hcov_le : Cov.card ≤ ∑ ℓ ∈ Ls, Xl ℓ := by
    refine (card_le_card hCov_sub).trans (card_biUnion_le.trans (sum_le_sum fun ℓ hℓ => ?_))
    refine card_biUnion_le.trans (sum_le_sum fun J hJ => ?_)
    refine card_biUnion_le.trans ?_
    have : ∀ T ∈ BadJ J ℓ, ((Y.powersetCard s).filter fun A => T ⊆ A).card ≤
        (Y.card - ℓ).choose (s - ℓ) := by
      intro T hT
      have hT' := mem_powersetCard.1 (mem_filter.1 hT).1
      have := card_supersets_le_choose (s := s) hT'.1
      rwa [hT'.2] at this
    refine (sum_le_sum this).trans ?_
    rw [sum_const, smul_eq_mul]
  have hYs : 0 < Y.card.choose s := Nat.choose_pos (hNs.trans hYN)
  have hXl_lt : ∀ ℓ ∈ Ls, r * Xl ℓ < Y.card.choose s := by
    intro ℓ hℓ
    rw [hLs, mem_filter, mem_range] at hℓ
    obtain ⟨hℓr, hℓ1⟩ := hℓ
    -- each saturated family
    have hbad : ∀ J ∈ Js ℓ, (BadJ J ℓ).card * B ℓ ≤ k ^ (ℓ + 1) * s.choose ℓ := by
      intro J hJ
      have hJc : Multiset.card J + ℓ = r - 1 := by
        rw [hJs, mem_filter] at hJ; omega
      exact card_saturated_mul_le P hPT Sp (fun I hI => (hSp I hI).1) Y J hJc hr (B ℓ)
    have hJs_card : (Js ℓ).card ≤ 2 ^ r := card_submultisets_le I₀ (hTypes I₀ hI₀T) _
    have hX1 : Xl ℓ * B ℓ ≤ 2 ^ r * (k ^ (ℓ + 1) * s.choose ℓ) * (Y.card - ℓ).choose (s - ℓ) := by
      rw [hXl, sum_mul]
      calc ∑ J ∈ Js ℓ, (BadJ J ℓ).card * (Y.card - ℓ).choose (s - ℓ) * B ℓ
          = ∑ J ∈ Js ℓ, (BadJ J ℓ).card * B ℓ * (Y.card - ℓ).choose (s - ℓ) := by
            refine sum_congr rfl fun J _ => by ring
        _ ≤ ∑ J ∈ Js ℓ, k ^ (ℓ + 1) * s.choose ℓ * (Y.card - ℓ).choose (s - ℓ) :=
            sum_le_sum fun J hJ => Nat.mul_le_mul_right _ (hbad J hJ)
        _ = (Js ℓ).card * (k ^ (ℓ + 1) * s.choose ℓ * (Y.card - ℓ).choose (s - ℓ)) := by
            rw [sum_const, smul_eq_mul]
        _ ≤ 2 ^ r * (k ^ (ℓ + 1) * s.choose ℓ * (Y.card - ℓ).choose (s - ℓ)) :=
            Nat.mul_le_mul_right _ hJs_card
        _ = _ := by ring
    -- the binomial identity
    have hNl : N.choose ℓ ≤ Y.card.choose ℓ := Nat.choose_le_choose _ hYN
    have hnum' := hnum ℓ hℓ1 hℓr
    by_cases hls : ℓ ≤ s
    · have hid : Y.card.choose s * s.choose ℓ = Y.card.choose ℓ * (Y.card - ℓ).choose (s - ℓ) :=
        Nat.choose_mul hls
      have hX2 : Xl ℓ * B ℓ * Y.card.choose ℓ ≤
          2 ^ r * k ^ (ℓ + 1) * s.choose ℓ ^ 2 * Y.card.choose s := by
        calc Xl ℓ * B ℓ * Y.card.choose ℓ
            ≤ 2 ^ r * (k ^ (ℓ + 1) * s.choose ℓ) * (Y.card - ℓ).choose (s - ℓ) *
                Y.card.choose ℓ := Nat.mul_le_mul_right _ hX1
          _ = 2 ^ r * k ^ (ℓ + 1) * s.choose ℓ *
                (Y.card.choose ℓ * (Y.card - ℓ).choose (s - ℓ)) := by ring
          _ = 2 ^ r * k ^ (ℓ + 1) * s.choose ℓ ^ 2 * Y.card.choose s := by rw [← hid]; ring
      have hpos : 0 < B ℓ * Y.card.choose ℓ :=
        Nat.mul_pos (hB1 ℓ) (lt_of_lt_of_le (by
          have : 0 < B ℓ * N.choose ℓ := lt_of_le_of_lt (Nat.zero_le _) hnum'
          exact Nat.pos_of_mul_pos_left this) hNl)
      have hlt : r * (2 ^ r * k ^ (ℓ + 1) * s.choose ℓ ^ 2) * Y.card.choose s <
          B ℓ * Y.card.choose ℓ * Y.card.choose s := by
        refine Nat.mul_lt_mul_of_pos_right ?_ hYs
        exact lt_of_lt_of_le hnum' (Nat.mul_le_mul_left _ hNl)
      have : r * Xl ℓ * (B ℓ * Y.card.choose ℓ) < Y.card.choose s * (B ℓ * Y.card.choose ℓ) := by
        calc r * Xl ℓ * (B ℓ * Y.card.choose ℓ) = r * (Xl ℓ * B ℓ * Y.card.choose ℓ) := by ring
          _ ≤ r * (2 ^ r * k ^ (ℓ + 1) * s.choose ℓ ^ 2 * Y.card.choose s) :=
              Nat.mul_le_mul_left _ hX2
          _ = r * (2 ^ r * k ^ (ℓ + 1) * s.choose ℓ ^ 2) * Y.card.choose s := by ring
          _ < B ℓ * Y.card.choose ℓ * Y.card.choose s := hlt
          _ = Y.card.choose s * (B ℓ * Y.card.choose ℓ) := by ring
      exact Nat.lt_of_mul_lt_mul_right this
    · have hsl : s.choose ℓ = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp only [hsl, mul_zero, zero_mul, Nat.le_zero] at hX1
      have hX0 : Xl ℓ = 0 := by
        rcases Nat.mul_eq_zero.1 hX1 with h | h
        · exact h
        · exact absurd h (Nat.one_le_iff_ne_zero.1 (hB1 ℓ))
      rw [hX0, mul_zero]; exact hYs
  have hcov_lt : Cov.card < (Y.powersetCard s).card := by
    rw [card_powersetCard]
    have hLs_card : Ls.card ≤ r - 1 := by
      have : Ls ⊆ (range r).erase 0 := by
        intro ℓ hℓ
        rw [hLs, mem_filter] at hℓ
        exact mem_erase.2 ⟨by omega, hℓ.1⟩
      refine (card_le_card this).trans ?_
      rw [card_erase_of_mem (mem_range.2 (by omega)), card_range]
    have h1 : r * ∑ ℓ ∈ Ls, Xl ℓ ≤ Ls.card * (Y.card.choose s - 1) := by
      rw [mul_sum]
      have : ∀ ℓ ∈ Ls, r * Xl ℓ ≤ Y.card.choose s - 1 := fun ℓ hℓ => by
        have := hXl_lt ℓ hℓ; omega
      refine (sum_le_sum this).trans ?_
      rw [sum_const, smul_eq_mul]
    have h2 : r * ∑ ℓ ∈ Ls, Xl ℓ < r * Y.card.choose s := by
      calc r * ∑ ℓ ∈ Ls, Xl ℓ ≤ Ls.card * (Y.card.choose s - 1) := h1
        _ ≤ (r - 1) * (Y.card.choose s - 1) := Nat.mul_le_mul_right _ hLs_card
        _ < r * Y.card.choose s := by
            have : (r - 1) * (Y.card.choose s - 1) ≤ (r - 1) * Y.card.choose s :=
              Nat.mul_le_mul_left _ (Nat.sub_le _ _)
            have : (r - 1) * Y.card.choose s < r * Y.card.choose s :=
              Nat.mul_lt_mul_of_pos_right (by omega) hYs
            omega
    exact lt_of_le_of_lt hcov_le (Nat.lt_of_mul_lt_mul_left h2)
  obtain ⟨A, hA, hAnot⟩ := exists_mem_notMem_of_card_lt_card hcov_lt
  have hA' := mem_powersetCard.1 hA
  have hAgood : ∀ ℓ ∈ Ls, ∀ J ∈ Js ℓ, ∀ T ∈ BadJ J ℓ, ¬ T ⊆ A := by
    intro ℓ hℓ J hJ T hT hTA
    exact hAnot (mem_filter.2 ⟨hA, ℓ, hℓ, J, hJ, T, hT, hTA⟩)
  refine ⟨Function.update Sp I₀ A, ?_, ?_⟩
  · intro I hI
    rcases mem_insert.1 hI with rfl | hI
    · rw [Function.update_self]; exact ⟨hA'.2, hA'.1⟩
    · have hne : I ≠ I₀ := fun h => hI₀ (h ▸ hI)
      rw [Function.update_of_ne hne]; exact hSp I hI
  · intro J T hJT hT1
    have hfilt : (insert I₀ P).filter (fun I => T ⊆ Function.update Sp I₀ A I ∧ J ≤ I) =
        if T ⊆ A ∧ J ≤ I₀ then insert I₀ (P.filter fun I => T ⊆ Sp I ∧ J ≤ I)
        else P.filter fun I => T ⊆ Sp I ∧ J ≤ I := by
      rw [filter_insert, Function.update_self]
      have : P.filter (fun I => T ⊆ Function.update Sp I₀ A I ∧ J ≤ I) =
          P.filter fun I => T ⊆ Sp I ∧ J ≤ I := by
        refine filter_congr fun I hI => ?_
        have hne : I ≠ I₀ := fun h => hI₀ (h ▸ hI)
        rw [Function.update_of_ne hne]
      rw [this]
    rw [hfilt]
    split_ifs with hc
    · rw [card_insert_of_notMem (fun h => hI₀ (mem_filter.1 h).1)]
      by_contra hcon
      have hge : B T.card ≤ cnt J T := by simp only [hcnt]; omega
      refine hAgood T.card ?_ J ?_ T ?_ hc.1
      · rw [hLs, mem_filter, mem_range]; omega
      · rw [hJs, mem_filter, Multiset.mem_toFinset, Multiset.mem_powerset]
        exact ⟨hc.2, by omega⟩
      · rw [hBadJ, mem_filter, mem_powersetCard]
        exact ⟨⟨hc.1.trans hA'.1, rfl⟩, hge⟩
    · exact hspread J T hJT hT1

end RefinedAbsorption.Sharp
