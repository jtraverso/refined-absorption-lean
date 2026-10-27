module
public import RefinedAbsorption.ExistenceProof

/-!
# Covering a leftover with reserves

Let `L` be an `r`-graph on `[n]` (the *leftover*) whose `(r-1)`-degrees are at most `n^{1-γ}`,
and let `X` be an `r`-graph edge-disjoint from `L` (the *reserves*) such that every edge `e ∈ L`
lies in at least `n^{q-r-α}` copies of `K_q^r` in `X ∪ {e}`.  If `2αr ≤ γ` and `n` is large,
then the edges of `L` can be covered by pairwise edge-disjoint such copies (`reserve_cover`).

The proof is a deterministic greedy algorithm: the edges of `L` are treated one after another,
and for the current edge `e` we choose a clique `Q ∈ K_q^r(X ∪ {e})` containing `e` which
avoids all *heavy* sets, where a set `S ⊄ e` with `|S| ≤ r` is heavy if it already lies in at
least `τ_{|S|} = ⌈n^{(r-|S|)(1-2α)}⌉` chosen cliques.  For `|S| = r` the threshold is `1`, so
avoiding heavy sets makes the chosen cliques edge-disjoint; for `|S| < r` it keeps the number
of chosen cliques through `S` below `deg_L(S) + τ_{|S|}`.  A double counting argument shows
that fewer than `n^{q-r-α}` cliques through `e` contain a heavy set.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset Filter

variable {n : ℕ}

/-! ### Counting lemmas -/

/-- If every set of a family `𝒮` contains `T`, then the cliques of a family `P` of `q`-sets
are counted at most `2^q` times by `∑_{S ∈ 𝒮} cliqueMult P S`. -/
theorem sum_cliqueMult_le_of_superset {V : Type*} [DecidableEq V] {q : ℕ}
    {P : Finset (Finset V)} (hP : ∀ Q ∈ P, Q.card = q) (T : Finset V) (𝒮 : Finset (Finset V))
    (h𝒮 : ∀ S ∈ 𝒮, T ⊆ S) :
    ∑ S ∈ 𝒮, cliqueMult P S ≤ 2 ^ q * cliqueMult P T := by
  unfold cliqueMult
  simp only [card_filter]
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro Q hQ
  split_ifs with hTQ
  · rw [mul_one, ← hP Q hQ, ← card_powerset, ← card_filter]
    exact card_le_card fun S hS => mem_powerset.2 (mem_filter.1 hS).2
  · apply le_of_eq
    rw [mul_zero]
    apply sum_eq_zero
    intro S hS
    rw [if_neg]
    exact fun h => hTQ ((h𝒮 S hS).trans h)

/-- The number of `q`-subsets of `[n]` containing a set `U` is at most `n^{q-|U|}`. -/
theorem card_supersets_mul_pow_le (q : ℕ) (U : Finset (Fin n)) :
    ((univ.powersetCard q).filter (fun Q : Finset (Fin n) => U ⊆ Q)).card * n ^ U.card
      ≤ n ^ q := by
  by_cases hU : U.card ≤ q
  · rw [card_powersetCard_filter_superset (subset_univ U) hU, card_univ, Fintype.card_fin]
    calc (n - U.card).choose (q - U.card) * n ^ U.card ≤ n ^ (q - U.card) * n ^ U.card := by
          gcongr
          exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
      _ = n ^ q := by rw [← pow_add, Nat.sub_add_cancel hU]
  · have : ((univ.powersetCard q).filter (fun Q : Finset (Fin n) => U ⊆ Q)) = ∅ := by
      rw [filter_eq_empty_iff]
      intro Q hQ hUQ
      exact hU ((card_le_card hUQ).trans (mem_powersetCard.1 hQ).2.le)
    simp [this]

/-- From a bound `D` on the `(r-1)`-degrees of an `r`-graph `L` we get the bound
`n^{r-1-|T|} D` on the degree of every set `T` with `|T| < r`. -/
theorem deg_le_pow_mul_of_maxDeg {r : ℕ} {L : Finset (Finset (Fin n))} (hL : IsRGraph r L)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : MaxDegLE r L D) (T : Finset (Fin n)) (hT : T.card < r) :
    (deg L T : ℝ) ≤ (n : ℝ) ^ (r - 1 - T.card) * D := by
  obtain ⟨k, hk⟩ : ∃ k, T.card + 1 + k = r := ⟨r - 1 - T.card, by omega⟩
  induction k generalizing T with
  | zero =>
    have : r - 1 - T.card = 0 := by omega
    rw [this, pow_zero, one_mul]
    exact hD T (by omega)
  | succ k ih =>
    have hsub : L.filter (fun e => T ⊆ e) ⊆
        (univ \ T).biUnion (fun x => L.filter (fun e => insert x T ⊆ e)) := by
      intro e he
      rw [mem_filter] at he
      have hlt : T.card < e.card := by rw [hL e he.1]; omega
      obtain ⟨x, hxe, hxT⟩ := exists_of_ssubset (ssubset_of_subset_of_ne he.2 (fun h => by
        rw [h] at hlt; exact lt_irrefl _ hlt))
      exact mem_biUnion.2 ⟨x, mem_sdiff.2 ⟨mem_univ _, hxT⟩,
        mem_filter.2 ⟨he.1, insert_subset hxe he.2⟩⟩
    have h1 : (deg L T : ℝ) ≤ ∑ x ∈ univ \ T, (deg L (insert x T) : ℝ) := by
      unfold deg
      exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    have h2 : ∀ x ∈ univ \ T,
        (deg L (insert x T) : ℝ) ≤ (n : ℝ) ^ (r - 1 - T.card - 1) * D := by
      intro x hx
      have hxT : x ∉ T := (mem_sdiff.1 hx).2
      have hc : (insert x T).card = T.card + 1 := card_insert_of_notMem hxT
      have := ih (insert x T) (by omega) (by omega)
      rw [hc] at this
      convert this using 3
    calc (deg L T : ℝ) ≤ ∑ x ∈ univ \ T, (n : ℝ) ^ (r - 1 - T.card - 1) * D :=
          h1.trans (sum_le_sum h2)
      _ ≤ (n : ℝ) * ((n : ℝ) ^ (r - 1 - T.card - 1) * D) := by
          rw [sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : (univ \ T).card ≤ n := (card_le_univ _).trans (by simp)
          exact_mod_cast this
      _ = (n : ℝ) ^ (r - 1 - T.card) * D := by
          rw [← mul_assoc, ← pow_succ']
          congr 2; omega

/-! ### The greedy invariant -/

/-- The invariant of the greedy algorithm, after the edges of `D` have been treated: `P` is a
family of `q`-sets whose `r`-subsets lie in `X ∪ D`, which is edge-disjoint, covers `D`, and
such that every set `S` with `|S| < r` is in at most `deg_D(S) + τ_{|S|}` members of `P`. -/
structure CoverInv (q r : ℕ) (X D : Finset (Finset (Fin n))) (τ : ℕ → ℕ)
    (P : Finset (Finset (Fin n))) : Prop where
  card_eq : ∀ Q ∈ P, Q.card = q
  edges : ∀ Q ∈ P, cliqueEdges r Q ⊆ X ∪ D
  mult_le : ∀ f : Finset (Fin n), f.card = r → cliqueMult P f ≤ 1
  cover : ∀ e ∈ D, ∃ Q ∈ P, e ⊆ Q
  load : ∀ S : Finset (Fin n), S.card < r → cliqueMult P S ≤ deg D S + τ S.card

theorem cliqueMult_insert_of_notMem {V : Type*} [DecidableEq V] {P : Finset (Finset V)}
    {Q : Finset V} (hQ : Q ∉ P) (S : Finset V) :
    cliqueMult (insert Q P) S = cliqueMult P S + if S ⊆ Q then 1 else 0 := by
  unfold cliqueMult
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => hQ (mem_filter.1 h').1)]
  · rfl

theorem deg_insert_of_notMem {V : Type*} [DecidableEq V] {D : Finset (Finset V)}
    {e : Finset V} (he : e ∉ D) (S : Finset V) :
    deg (insert e D) S = deg D S + if S ⊆ e then 1 else 0 := cliqueMult_insert_of_notMem he S

theorem coverInv_empty (q r : ℕ) (X : Finset (Finset (Fin n))) (τ : ℕ → ℕ) :
    CoverInv q r X ∅ τ ∅ :=
  ⟨by simp, by simp, fun f _ => by simp [cliqueMult], by simp, fun S _ => by simp [cliqueMult]⟩

/-- One step of the greedy algorithm: adding a reserve clique `Q` for a new edge `e` which
avoids all heavy sets preserves the invariant. -/
theorem CoverInv.insert {q r : ℕ} {X D P : Finset (Finset (Fin n))} {τ : ℕ → ℕ}
    (hτr : τ r = 1) (hinv : CoverInv q r X D τ P) {e : Finset (Fin n)} (he : e.card = r)
    (heX : e ∉ X) (heD : e ∉ D) {Q : Finset (Fin n)} (hQ : Q ∈ reserveCliques q r X e)
    (hgood : ∀ S ⊆ Q, S.card ≤ r → ¬ S ⊆ e → cliqueMult P S < τ S.card) :
    CoverInv q r X (insert e D) τ (insert Q P) := by
  simp only [reserveCliques, mem_filter, mem_powersetCard] at hQ
  obtain ⟨⟨-, hQq⟩, heQ, hQX⟩ := hQ
  have hnot : ∀ Q' ∈ P, ¬ e ⊆ Q' := by
    intro Q' hQ' heQ'
    have := hinv.edges Q' hQ' (mem_powersetCard.2 ⟨heQ', he⟩)
    rcases mem_union.1 this with h | h
    · exact heX h
    · exact heD h
  have hQP : Q ∉ P := fun h => hnot Q h heQ
  have hce : cliqueMult P e = 0 := by
    unfold cliqueMult
    rw [card_eq_zero, filter_eq_empty_iff]
    exact hnot
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Q' hQ'
    rcases mem_insert.1 hQ' with rfl | h
    · exact hQq
    · exact hinv.card_eq Q' h
  · intro Q' hQ' f hf
    rcases mem_insert.1 hQ' with rfl | h
    · by_cases hfe : f = e
      · subst hfe; exact mem_union_right _ (mem_insert_self _ _)
      · exact mem_union_left _ (hQX f hf hfe)
    · rcases mem_union.1 (hinv.edges Q' h hf) with h' | h'
      · exact mem_union_left _ h'
      · exact mem_union_right _ (mem_insert_of_mem h')
  · intro f hf
    rw [cliqueMult_insert_of_notMem hQP]
    split_ifs with hfQ
    · by_cases hfe : f ⊆ e
      · have : f = e := eq_of_subset_of_card_le hfe (by rw [he, hf])
        subst this; rw [hce]
      · have := hgood f hfQ hf.le hfe
        rw [hf, hτr] at this
        omega
    · simpa using hinv.mult_le f hf
  · intro e' he'
    rcases mem_insert.1 he' with rfl | h
    · exact ⟨Q, mem_insert_self _ _, heQ⟩
    · obtain ⟨Q', hQ', h'⟩ := hinv.cover e' h
      exact ⟨Q', mem_insert_of_mem hQ', h'⟩
  · intro S hS
    rw [cliqueMult_insert_of_notMem hQP, deg_insert_of_notMem heD]
    have h0 := hinv.load S hS
    split_ifs with hSQ hSe hSe
    · omega
    · have := hgood S hSQ hS.le hSe
      omega
    · exact absurd (hSe.trans heQ) hSQ
    · omega

/-- The number of reserve cliques of `e` containing a heavy set, bounded by a double sum over
`T = S ∩ e` and `s = |S|`. -/
theorem card_bad_le {q r : ℕ} {X P : Finset (Finset (Fin n))} {τ : ℕ → ℕ}
    (hτ : ∀ s ≤ r, 1 ≤ τ s) (hP : ∀ Q ∈ P, Q.card = q) {e : Finset (Fin n)} (he : e.card = r)
    (hn : 0 < n) :
    ((((reserveCliques q r X e).filter (fun Q => ∃ S ⊆ Q, S.card ≤ r ∧ ¬ S ⊆ e ∧
        τ S.card ≤ cliqueMult P S)).card : ℕ) : ℝ) ≤
      ∑ T ∈ e.powerset, ∑ s ∈ range (r + 1),
        if T.card < s then
          (2 ^ q * (cliqueMult P T : ℝ) / τ s) * ((n : ℝ) ^ q / (n : ℝ) ^ (r + s - T.card))
        else 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set 𝓗 := (univ : Finset (Finset (Fin n))).filter
    (fun S => S.card ≤ r ∧ ¬ S ⊆ e ∧ τ S.card ≤ cliqueMult P S) with h𝓗
  have hsub : (reserveCliques q r X e).filter (fun Q => ∃ S ⊆ Q, S.card ≤ r ∧ ¬ S ⊆ e ∧
      τ S.card ≤ cliqueMult P S) ⊆
      𝓗.biUnion (fun S => (univ.powersetCard q).filter (fun Q => e ∪ S ⊆ Q)) := by
    intro Q hQ
    simp only [reserveCliques, mem_filter] at hQ
    obtain ⟨⟨hQq, heQ, -⟩, S, hSQ, hS⟩ := hQ
    exact mem_biUnion.2 ⟨S, mem_filter.2 ⟨mem_univ _, hS⟩,
      mem_filter.2 ⟨hQq, union_subset heQ hSQ⟩⟩
  have h1 : ((((reserveCliques q r X e).filter (fun Q => ∃ S ⊆ Q, S.card ≤ r ∧ ¬ S ⊆ e ∧
        τ S.card ≤ cliqueMult P S)).card : ℕ) : ℝ) ≤
      ∑ S ∈ 𝓗, (n : ℝ) ^ q / (n : ℝ) ^ (e ∪ S).card := by
    refine (Nat.cast_le.2 ((card_le_card hsub).trans card_biUnion_le)).trans ?_
    push_cast
    apply sum_le_sum
    intro S _
    rw [le_div_iff₀ (by positivity)]
    exact_mod_cast card_supersets_mul_pow_le q (e ∪ S)
  refine h1.trans (le_of_eq_of_le (b := ∑ p ∈ e.powerset ×ˢ range (r + 1),
      ∑ S ∈ 𝓗.filter (fun S => (e ∩ S, S.card) = p),
      (n : ℝ) ^ q / (n : ℝ) ^ (e ∪ S).card) ?_ ?_)
  · rw [sum_fiberwise_of_maps_to]
    intro S hS
    simp only [h𝓗, mem_filter] at hS
    exact mem_product.2 ⟨mem_powerset.2 inter_subset_left, mem_range.2 (by omega)⟩
  rw [sum_product]
  apply sum_le_sum; intro T hT
  apply sum_le_sum; intro s hs
  have hs' : s ≤ r := Nat.lt_succ_iff.1 (mem_range.1 hs)
  have hfib : ∀ S ∈ 𝓗.filter (fun S => (e ∩ S, S.card) = (T, s)),
      e ∩ S = T ∧ S.card = s ∧ ¬ S ⊆ e ∧ τ s ≤ cliqueMult P S := by
    intro S hS
    simp only [h𝓗, mem_filter, Prod.mk.injEq] at hS
    obtain ⟨⟨-, -, hSe, hτS⟩, h1, h2⟩ := hS
    exact ⟨h1, h2, hSe, h2 ▸ hτS⟩
  split_ifs with hts
  · have hval : ∀ S ∈ 𝓗.filter (fun S => (e ∩ S, S.card) = (T, s)),
        (n : ℝ) ^ q / (n : ℝ) ^ (e ∪ S).card = (n : ℝ) ^ q / (n : ℝ) ^ (r + s - T.card) := by
      intro S hS
      obtain ⟨h1, h2, -, -⟩ := hfib S hS
      have := card_union_add_card_inter e S
      rw [h1, h2, he] at this
      congr 2; omega
    rw [sum_congr rfl hval, sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hτ0 : (0 : ℝ) < τ s := by exact_mod_cast hτ s hs'
    rw [le_div_iff₀ hτ0]
    have hA : (𝓗.filter (fun S => (e ∩ S, S.card) = (T, s))).card * τ s ≤
        ∑ S ∈ 𝓗.filter (fun S => (e ∩ S, S.card) = (T, s)), cliqueMult P S := by
      rw [card_eq_sum_ones, sum_mul]
      apply sum_le_sum
      intro S hS
      rw [one_mul]; exact (hfib S hS).2.2.2
    have hB := sum_cliqueMult_le_of_superset hP T
      (𝓗.filter (fun S => (e ∩ S, S.card) = (T, s)))
      (fun S hS => (hfib S hS).1 ▸ inter_subset_right)
    exact_mod_cast hA.trans hB
  · apply le_of_eq
    apply sum_eq_zero
    intro S hS
    exfalso
    obtain ⟨h1, h2, hSe, -⟩ := hfib S hS
    apply hts
    rw [← h1, ← h2]
    apply card_lt_card
    refine ssubset_of_subset_of_ne inter_subset_right ?_
    intro h; exact hSe (h ▸ inter_subset_left)

/-- The analytic estimate for one term of the double sum. -/
theorem bad_term_le {q r s t : ℕ} {α : ℝ} (hα : 0 ≤ α) (hts : t < s)
    (hn : 1 ≤ (n : ℝ)) {c τs : ℝ} (hc : c ≤ 3 * (n : ℝ) ^ (((r : ℝ) - t) * (1 - 2 * α)))
    (hτs : (n : ℝ) ^ (((r : ℝ) - s) * (1 - 2 * α)) ≤ τs) :
    (2 ^ q * c / τs) * ((n : ℝ) ^ q / (n : ℝ) ^ (r + s - t)) ≤
      3 * 2 ^ q * (n : ℝ) ^ ((q : ℝ) - r - 2 * α) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hA : 0 < (n : ℝ) ^ (((r : ℝ) - s) * (1 - 2 * α)) := Real.rpow_pos_of_pos hn0 _
  have hτ0 : 0 < τs := lt_of_lt_of_le hA hτs
  have hB : 0 ≤ (n : ℝ) ^ q / (n : ℝ) ^ (r + s - t) := by positivity
  rcases le_or_gt c 0 with hc0 | hc0
  · have : 2 ^ q * c / τs ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith [pow_pos (two_pos (α := ℝ)) q]) hτ0.le
    have : 0 ≤ 3 * 2 ^ q * (n : ℝ) ^ ((q : ℝ) - r - 2 * α) := by positivity
    nlinarith
  have h1 : 2 ^ q * c / τs ≤ 2 ^ q * (3 * (n : ℝ) ^ (((r : ℝ) - t) * (1 - 2 * α))) /
      (n : ℝ) ^ (((r : ℝ) - s) * (1 - 2 * α)) := by
    apply div_le_div₀ (by positivity) (by gcongr) hA hτs
  have h2 : (n : ℝ) ^ q / (n : ℝ) ^ (r + s - t) = (n : ℝ) ^ ((q : ℝ) - (r + s - t : ℕ)) := by
    rw [Real.rpow_sub hn0, Real.rpow_natCast, Real.rpow_natCast]
  calc (2 ^ q * c / τs) * ((n : ℝ) ^ q / (n : ℝ) ^ (r + s - t))
      ≤ (2 ^ q * (3 * (n : ℝ) ^ (((r : ℝ) - t) * (1 - 2 * α))) /
      (n : ℝ) ^ (((r : ℝ) - s) * (1 - 2 * α))) * ((n : ℝ) ^ q / (n : ℝ) ^ (r + s - t)) :=
        mul_le_mul_of_nonneg_right h1 hB
    _ = 3 * 2 ^ q * (n : ℝ) ^ ((q : ℝ) - r - 2 * α * (s - t)) := by
        rw [h2, mul_div_assoc, mul_div_assoc, ← Real.rpow_sub hn0, mul_assoc,
          mul_assoc 3, ← Real.rpow_add hn0]
        have : ((r + s - t : ℕ) : ℝ) = r + s - t := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this]; ring_nf
    _ ≤ 3 * 2 ^ q * (n : ℝ) ^ ((q : ℝ) - r - 2 * α) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hn
        have : (1 : ℝ) ≤ s - t := by
          have : (t : ℝ) + 1 ≤ s := by exact_mod_cast hts
          linarith
        nlinarith

/-! ### The reserve covering lemma -/

/-- **Covering a leftover with reserves.**  Let `q, r ≥ 1`, `0 < α ≤ 1/2` and `γ ≥ 2αr`.
For all large `n`: if `L ⊆ K_n^r` has `Δ_{r-1}(L) ≤ n^{1-γ}`, and `X` is edge-disjoint from `L`
with every `e ∈ L` in at least `n^{q-r-α}` copies of `K_q^r` in `X ∪ {e}`, then there is a
`K_q^r`-packing of `L ∪ X` covering every edge of `L`. -/
theorem reserve_cover (q r : ℕ) (hr : 1 ≤ r) {α γ : ℝ} (hα : 0 < α)
    (hα2 : α ≤ 1 / 2) (hγ : 2 * α * r ≤ γ) :
    ∀ᶠ n : ℕ in atTop, ∀ L X : Finset (Finset (Fin n)), L ⊆ completeRGraph (Fin n) r →
      Disjoint L X → MaxDegLE r L ((n : ℝ) ^ (1 - γ)) →
      (∀ e ∈ L, (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e).card) →
        ∃ P, IsPacking q r (L ∪ X) P ∧ L ⊆ coveredEdges r P := by
  have hθ : 0 ≤ 1 - 2 * α := by linarith
  set K : ℝ := ((r : ℝ) + 1) * 2 ^ r * (3 * 2 ^ q) with hK
  have hK0 : 0 ≤ K := by positivity
  filter_upwards [eventually_ge_atTop 1,
    ev_rpow_neg_le hα (show (0 : ℝ) < 1 / (K + 1) by positivity)]
    with n hn1 hnα L X hLK hLX hLdeg hres
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  set τ : ℕ → ℕ := fun s => ⌈(n : ℝ) ^ (((r : ℝ) - s) * (1 - 2 * α))⌉₊ with hτdef
  have hτr : τ r = 1 := by simp [τ]
  have hτge : ∀ s : ℕ, (n : ℝ) ^ (((r : ℝ) - s) * (1 - 2 * α)) ≤ τ s := fun s => Nat.le_ceil _
  have hτle : ∀ s : ℕ, (τ s : ℝ) ≤ (n : ℝ) ^ (((r : ℝ) - s) * (1 - 2 * α)) + 1 := fun s =>
    (Nat.ceil_lt_add_one (by positivity)).le
  have hτ1 : ∀ s ≤ r, 1 ≤ τ s := fun s _ =>
    Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hn0 _)).ne'
  have hLr : IsRGraph r L := fun e he => (mem_powersetCard.1 (hLK he)).2
  have hdegL : ∀ T : Finset (Fin n), T.card < r →
      (deg L T : ℝ) ≤ (n : ℝ) ^ (((r : ℝ) - T.card) * (1 - 2 * α)) := by
    intro T hT
    refine (deg_le_pow_mul_of_maxDeg hLr (by positivity) hLdeg T hT).trans ?_
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
    apply Real.rpow_le_rpow_of_exponent_le hn
    have h1 : ((r - 1 - T.card : ℕ) : ℝ) = (r : ℝ) - 1 - T.card := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [h1]
    have : 2 * α * ((r : ℝ) - T.card) ≤ 2 * α * r := by
      have : (0 : ℝ) ≤ T.card := by positivity
      nlinarith
    nlinarith
  have key : ∀ D ⊆ L, ∃ P, CoverInv q r X D τ P := by
    intro D
    induction D using Finset.induction_on with
    | empty => exact fun _ => ⟨∅, coverInv_empty q r X τ⟩
    | insert e D heD ih =>
      intro hsub
      obtain ⟨P, hP⟩ := ih ((subset_insert _ _).trans hsub)
      have heL : e ∈ L := hsub (mem_insert_self _ _)
      have he : e.card = r := hLr e heL
      have heX : e ∉ X := fun h => disjoint_left.1 hLX heL h
      have hc : ∀ T : Finset (Fin n), T.card < r →
          (cliqueMult P T : ℝ) ≤ 3 * (n : ℝ) ^ (((r : ℝ) - T.card) * (1 - 2 * α)) := by
        intro T hT
        have h1 : (cliqueMult P T : ℝ) ≤ deg D T + τ T.card := by
          exact_mod_cast hP.load T hT
        have h2 : (deg D T : ℝ) ≤ deg L T := by
          unfold deg
          exact_mod_cast card_le_card (filter_subset_filter _ ((subset_insert _ _).trans hsub))
        have h3 : (1 : ℝ) ≤ (n : ℝ) ^ (((r : ℝ) - T.card) * (1 - 2 * α)) := by
          apply Real.one_le_rpow hn
          apply mul_nonneg _ hθ
          have : (T.card : ℝ) < r := by exact_mod_cast hT
          linarith
        linarith [hdegL T hT, hτle T.card]
      have hbad := card_bad_le (X := X) hτ1 hP.card_eq he (by omega)
      have hsum : (∑ T ∈ e.powerset, ∑ s ∈ range (r + 1),
          if T.card < s then
            (2 ^ q * (cliqueMult P T : ℝ) / τ s) * ((n : ℝ) ^ q / (n : ℝ) ^ (r + s - T.card))
          else 0) ≤ K * (n : ℝ) ^ ((q : ℝ) - r - 2 * α) := by
        have hterm : ∀ T ∈ e.powerset, ∀ s ∈ range (r + 1),
            (if T.card < s then
              (2 ^ q * (cliqueMult P T : ℝ) / τ s) * ((n : ℝ) ^ q / (n : ℝ) ^ (r + s - T.card))
            else 0) ≤ 3 * 2 ^ q * (n : ℝ) ^ ((q : ℝ) - r - 2 * α) := by
          intro T hT s hs
          have hs' : s ≤ r := Nat.lt_succ_iff.1 (mem_range.1 hs)
          split_ifs with hts
          · exact bad_term_le hα.le hts hn (hc T (by omega)) (hτge s)
          · positivity
        calc _ ≤ ∑ T ∈ e.powerset, ∑ s ∈ range (r + 1),
              3 * 2 ^ q * (n : ℝ) ^ ((q : ℝ) - r - 2 * α) :=
              sum_le_sum fun T hT => sum_le_sum fun s hs => hterm T hT s hs
          _ = K * (n : ℝ) ^ ((q : ℝ) - r - 2 * α) := by
              simp only [sum_const, card_range, card_powerset, he, nsmul_eq_mul, hK]
              push_cast; ring
      have hlt : K * (n : ℝ) ^ ((q : ℝ) - r - 2 * α) < (n : ℝ) ^ ((q : ℝ) - r - α) := by
        have e1 : (n : ℝ) ^ ((q : ℝ) - r - 2 * α) =
            (n : ℝ) ^ (-α) * (n : ℝ) ^ ((q : ℝ) - r - α) := by
          rw [← Real.rpow_add hn0]; ring_nf
        rw [e1, ← mul_assoc]
        have hpos : 0 < (n : ℝ) ^ ((q : ℝ) - r - α) := Real.rpow_pos_of_pos hn0 _
        have : K * (n : ℝ) ^ (-α) < 1 := by
          calc K * (n : ℝ) ^ (-α) ≤ K * (1 / (K + 1)) := mul_le_mul_of_nonneg_left hnα hK0
            _ < 1 := by rw [mul_one_div, div_lt_one (by linarith)]; linarith
        nlinarith
      have hex : ∃ Q ∈ reserveCliques q r X e, ¬ ∃ S ⊆ Q, S.card ≤ r ∧ ¬ S ⊆ e ∧
          τ S.card ≤ cliqueMult P S := by
        by_contra hcon
        push_neg at hcon
        have hfeq : (reserveCliques q r X e).filter (fun Q => ∃ S ⊆ Q, S.card ≤ r ∧
            ¬ S ⊆ e ∧ τ S.card ≤ cliqueMult P S) = reserveCliques q r X e :=
          filter_true_of_mem fun Q hQ => hcon Q hQ
        rw [hfeq] at hbad
        linarith [hres e heL]
      obtain ⟨Q, hQ, hgood⟩ := hex
      push_neg at hgood
      exact ⟨insert Q P, hP.insert hτr he heX heD hQ hgood⟩
  obtain ⟨P, hP⟩ := key L Subset.rfl
  refine ⟨P, ⟨hP.card_eq, fun Q hQ => (hP.edges Q hQ).trans (by rw [union_comm]),
    hP.mult_le⟩, fun e he => ?_⟩
  obtain ⟨Q, hQ, heQ⟩ := hP.cover e he
  exact mem_biUnion.2 ⟨Q, hQ, mem_powersetCard.2 ⟨heQ, hLr e he⟩⟩

end RefinedAbsorption
