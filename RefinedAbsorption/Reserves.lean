module
public import RefinedAbsorption.ExistenceProof
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# An explicit construction of reserves

We prove `WeakReservesLemma` — the form of the reserves lemma (Lemma 2.1) used in the proof of
the Existence Conjecture — by an explicit (deterministic) construction, replacing the random
construction of the paper.

Write each vertex `v < n` in base `s`, with digits `dig s i v = ⌊v / s^i⌋ mod s`, and let `X` be
the set of `r`-sets `T` such that for some coordinate `i < t` the sum of the `i`-th digits of the
vertices of `T` is divisible by `s`.  With `s ≈ n^{1/t}`:

* every `(r-1)`-set `S` lies in at most `2tn/s ≈ n^{1-1/t}` edges of `X` (the digit of the extra
  vertex is determined in the chosen coordinate);
* every `e ∉ X` lies in at least `≈ n^{(q-r)(1 - M/t)}` copies of `K_q^r` in `X ∪ {e}`, where
  `M = binom(q-1, r-1)`: grow `e` vertex by vertex, each new vertex having prescribed digits in
  (at most `M`) coordinates assigned injectively to the `(r-1)`-subsets of the current set.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

/-- The `i`-th digit of `v` in base `s`. -/
def dig {n : ℕ} (s i : ℕ) (v : Fin n) : ℕ := v.val / s ^ i % s

/-- The digit-sum reserve graph: `r`-sets `T` such that in some coordinate `i < t` the digit sum
of `T` is divisible by `s`. -/
def digitReserve (n r t s : ℕ) : Finset (Finset (Fin n)) :=
  (completeRGraph (Fin n) r).filter (fun T => ∃ i ∈ range t, (∑ x ∈ T, dig s i x) % s = 0)

/-! ### Elementary modular arithmetic -/

theorem mod_aux1 {s a x : ℕ} (ha : a < s) (hx : x < s) (h : (a + x) % s = 0) :
    a = (s - x) % s := by
  rcases lt_or_ge (a + x) s with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    rw [show x = 0 by omega, Nat.sub_zero, Nat.mod_self]; omega
  · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at h
    rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem mod_aux2 {s : ℕ} (x : ℕ) (hs : 0 < s) : ((s - x % s) % s + x) % s = 0 := by
  have hx := Nat.mod_lt x hs
  rw [Nat.add_mod, Nat.mod_mod]
  rcases Nat.eq_zero_or_pos (x % s) with h0 | h0
  · rw [h0, Nat.sub_zero, Nat.mod_self]; simp
  · rw [Nat.mod_eq_of_lt (show s - x % s < s by omega), Nat.sub_add_cancel hx.le, Nat.mod_self]

/-! ### Degree bound -/

/-- A digit class has at most `n/s + s^i` elements. -/
theorem card_dig_eq_mul_le (n s i c : ℕ) (hs : 1 ≤ s) :
    (univ.filter (fun v : Fin n => dig s i v = c)).card * s ≤ n + s ^ (i + 1) := by
  have hpos : 0 < s ^ i := pow_pos hs i
  have hinj : Set.InjOn (fun v : Fin n => (v.val / s ^ (i + 1), v.val % s ^ i))
      (univ.filter (fun v : Fin n => dig s i v = c) : Set (Fin n)) := by
    intro v hv w hw h
    have hv' : dig s i v = c := (Finset.mem_filter.mp hv).2
    have hw' : dig s i w = c := (Finset.mem_filter.mp hw).2
    dsimp only [dig] at hv' hw'
    simp only [Prod.mk.injEq] at h
    have key : ∀ x : ℕ,
        x = x / s ^ (i + 1) * s ^ (i + 1) + x / s ^ i % s * s ^ i + x % s ^ i := by
      intro x
      have h1 := Nat.div_add_mod x (s ^ i)
      have h2 := Nat.div_add_mod (x / s ^ i) s
      rw [Nat.div_div_eq_div_mul, ← pow_succ] at h2
      nth_rewrite 1 [← h1, ← h2]
      ring
    apply Fin.ext
    rw [key v.val, key w.val, h.1, h.2, hv', hw']
  have hmaps : Set.MapsTo (fun v : Fin n => (v.val / s ^ (i + 1), v.val % s ^ i))
      (univ.filter (fun v : Fin n => dig s i v = c) : Set (Fin n))
      (range (n / s ^ (i + 1) + 1) ×ˢ range (s ^ i) : Finset (ℕ × ℕ)) := by
    intro v _
    simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
    exact ⟨Nat.lt_succ_of_le (Nat.div_le_div_right v.2.le), Nat.mod_lt _ hpos⟩
  have := card_le_card_of_injOn _ hmaps hinj
  rw [card_product, card_range, card_range] at this
  calc _ ≤ (n / s ^ (i + 1) + 1) * s ^ i * s := Nat.mul_le_mul_right _ this
    _ = n / s ^ (i + 1) * s ^ (i + 1) + s ^ (i + 1) := by ring
    _ ≤ n + s ^ (i + 1) := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

theorem deg_digitReserve_mul_le (n r t s : ℕ) (hs : 1 ≤ s) (hst : s ^ t ≤ n)
    (S : Finset (Fin n)) (hS : S.card + 1 = r) :
    deg (digitReserve n r t s) S * s ≤ 2 * t * n := by
  set c : ℕ → ℕ := fun i => (s - (∑ x ∈ S, dig s i x) % s) % s with hc
  have h1 : (digitReserve n r t s).filter (fun T => S ⊆ T) ⊆
      ((range t).biUnion (fun i => univ.filter (fun v : Fin n => dig s i v = c i))).image
        (fun v => insert v S) := by
    intro T hT
    simp only [digitReserve, completeRGraph, mem_filter, mem_powersetCard] at hT
    obtain ⟨⟨⟨-, hTc⟩, i, hi, hsum⟩, hST⟩ := hT
    obtain ⟨v, hv⟩ : ∃ v, T \ S = {v} :=
      card_eq_one.1 (by rw [card_sdiff_of_subset hST]; omega)
    have hvT : v ∈ T := (mem_sdiff.1 (hv ▸ mem_singleton_self v)).1
    have hvS : v ∉ S := (mem_sdiff.1 (hv ▸ mem_singleton_self v)).2
    have hTeq : T = insert v S := by
      ext x
      constructor
      · intro hx
        by_cases hxS : x ∈ S
        · exact mem_insert_of_mem hxS
        · have : x ∈ T \ S := mem_sdiff.2 ⟨hx, hxS⟩
          rw [hv, mem_singleton] at this
          exact this ▸ mem_insert_self _ _
      · intro hx
        rcases mem_insert.1 hx with rfl | hx
        · exact hvT
        · exact hST hx
    rw [mem_image]
    refine ⟨v, ?_, hTeq.symm⟩
    rw [mem_biUnion]
    refine ⟨i, hi, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    rw [hTeq, sum_insert hvS, Nat.add_mod (dig s i v)] at hsum
    have hd : dig s i v < s := Nat.mod_lt _ hs
    exact mod_aux1 hd (Nat.mod_lt _ hs) (by rwa [Nat.mod_eq_of_lt hd] at hsum)
  have h3 := ((card_le_card h1).trans card_image_le).trans card_biUnion_le
  calc deg (digitReserve n r t s) S * s
      ≤ (∑ i ∈ range t, (univ.filter (fun v : Fin n => dig s i v = c i)).card) * s :=
        Nat.mul_le_mul_right _ h3
    _ = ∑ i ∈ range t, (univ.filter (fun v : Fin n => dig s i v = c i)).card * s :=
        sum_mul _ _ _
    _ ≤ ∑ i ∈ range t, 2 * n := by
        apply sum_le_sum
        intro i hi
        have := card_dig_eq_mul_le n s i (c i) hs
        have : s ^ (i + 1) ≤ n := (Nat.pow_le_pow_right hs (by simpa using hi)).trans hst
        omega
    _ = 2 * t * n := by rw [sum_const, card_range, smul_eq_mul]; ring

/-! ### Counting cliques -/

/-- The sets of size `b` containing `e` all of whose `r`-subsets other than `e` lie in `X`. -/
def goodSets {n : ℕ} (r b : ℕ) (X : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (univ.powersetCard b).filter (fun B => e ⊆ B ∧ ∀ T ∈ B.powersetCard r, T ≠ e → T ∈ X)

/-- One extension step: a set `B` has many good extensions `w`. -/
theorem card_good_extensions (n r t s : ℕ) (hs : 1 ≤ s) (hst : s ^ t ≤ n)
    (B : Finset (Fin n)) (hB : (B.powersetCard (r - 1)).card ≤ t) (hr : 1 ≤ r) :
    s ^ (t - (B.powersetCard (r - 1)).card) - B.card ≤
      ((univ \ B).filter (fun w => ∀ T ∈ B.powersetCard (r - 1),
        insert w T ∈ digitReserve n r t s)).card := by
  classical
  set P := B.powersetCard (r - 1) with hPdef
  set ι : Finset (Fin n) → ℕ :=
    fun T => if h : T ∈ P then (P.equivFin ⟨T, h⟩ : ℕ) else 0 with hι
  have hιlt : ∀ T ∈ P, ι T < t := by
    intro T hT
    simp only [hι, dif_pos hT]
    exact lt_of_lt_of_le (Fin.isLt _) hB
  have hιinj : Set.InjOn ι (P : Set (Finset (Fin n))) := by
    intro T hT T' hT' h
    simp only [hι, dif_pos (mem_coe.1 hT), dif_pos (mem_coe.1 hT')] at h
    have := P.equivFin.injective (Fin.ext h)
    simpa using this
  set c : Finset (Fin n) → ℕ → ℕ := fun T i => (s - (∑ x ∈ T, dig s i x) % s) % s with hc
  set A : Fin t → Finset (Fin s) := fun i =>
    univ.filter (fun d => ∀ T ∈ P, ι T = i.val → (d : ℕ) = c T i) with hA
  set D := P.image ι with hD
  have hDcard : D.card = P.card := card_image_of_injOn hιinj
  -- the number of admissible digit vectors
  have hprod : s ^ (t - P.card) ≤ (Fintype.piFinset A).card := by
    rw [Fintype.card_piFinset]
    have h1 : ∀ i : Fin t, (if (i : ℕ) ∈ D then 1 else s) ≤ (A i).card := by
      intro i
      split_ifs with hi
      · obtain ⟨T, hT, hTi⟩ := mem_image.1 hi
        refine card_pos.2 ⟨⟨c T i, Nat.mod_lt _ hs⟩, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
        intro T' hT' hT'i
        have : T' = T := hιinj hT' hT (hT'i.trans hTi.symm)
        subst this; rfl
      · have : A i = univ := by
          ext d
          simp only [hA, mem_filter, mem_univ, true_and, iff_true]
          intro T hT hTi
          exact absurd (mem_image.2 ⟨T, hT, hTi⟩) hi
        rw [this, card_univ, Fintype.card_fin]
    refine le_trans ?_ (prod_le_prod' fun i _ => h1 i)
    rw [prod_ite, prod_const_one, one_mul, prod_const]
    apply Nat.pow_le_pow_right hs
    have h2 := card_filter_add_card_filter_not (s := (univ : Finset (Fin t)))
      (fun i : Fin t => (i : ℕ) ∈ D)
    have h3 : (univ.filter (fun i : Fin t => (i : ℕ) ∈ D)).card ≤ D.card := by
      apply card_le_card_of_injOn (fun i : Fin t => (i : ℕ))
      · intro i hi; simpa using hi
      · intro i _ j _ h; exact Fin.ext h
    rw [card_univ, Fintype.card_fin] at h2
    omega
  -- digit vectors give (nice) vertices
  set Φ : (Fin t → Fin s) → Fin n := fun g =>
    ⟨finFunctionFinEquiv g, lt_of_lt_of_le (finFunctionFinEquiv g).isLt hst⟩ with hΦ
  have hΦinj : Function.Injective Φ := by
    intro g g' h
    simp only [hΦ, Fin.mk.injEq] at h
    exact finFunctionFinEquiv.injective (Fin.ext h)
  have hdig : ∀ g : Fin t → Fin s, ∀ i : Fin t, dig s i (Φ g) = g i := by
    intro g i
    conv_rhs => rw [← finFunctionFinEquiv.symm_apply_apply g]
    rfl
  have hsub : (Fintype.piFinset A).image Φ \ B ⊆ (univ \ B).filter (fun w => ∀ T ∈ P,
        insert w T ∈ digitReserve n r t s) := by
    intro w hw
    obtain ⟨hw1, hwB⟩ := mem_sdiff.1 hw
    obtain ⟨g, hg, rfl⟩ := mem_image.1 hw1
    refine mem_filter.2 ⟨mem_sdiff.2 ⟨mem_univ _, hwB⟩, fun T hT => ?_⟩
    have hTB : T ⊆ B := (mem_powersetCard.1 hT).1
    have hwT : Φ g ∉ T := fun h => hwB (hTB h)
    simp only [digitReserve, completeRGraph, mem_filter, mem_powersetCard]
    refine ⟨⟨subset_univ _, ?_⟩, ι T, mem_range.2 (hιlt T hT), ?_⟩
    · rw [card_insert_of_notMem hwT, (mem_powersetCard.1 hT).2]; omega
    · rw [sum_insert hwT]
      have hgi := Fintype.mem_piFinset.1 hg ⟨ι T, hιlt T hT⟩
      simp only [hA, mem_filter, mem_univ, true_and] at hgi
      rw [hdig g ⟨ι T, hιlt T hT⟩, hgi T hT rfl]
      exact mod_aux2 _ hs
  calc s ^ (t - P.card) - B.card ≤ (Fintype.piFinset A).card - B.card :=
        Nat.sub_le_sub_right hprod _
    _ = ((Fintype.piFinset A).image Φ).card - B.card := by
        rw [card_image_of_injective _ hΦinj]
    _ ≤ ((Fintype.piFinset A).image Φ \ B).card := le_card_sdiff _ _
    _ ≤ _ := card_le_card hsub

theorem card_goodSets_step (n q r t s b : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hst : s ^ t ≤ n)
    (hM : (q - 1).choose (r - 1) ≤ t) (hbq : b < q) (e : Finset (Fin n))
    (he : e.card = r) :
    (goodSets r b (digitReserve n r t s) e).card * (s ^ (t - (q - 1).choose (r - 1)) - q) ≤
      (goodSets r (b + 1) (digitReserve n r t s) e).card * (b + 1 - r) := by
  set X := digitReserve n r t s
  apply card_mul_le_card_mul (fun B B' : Finset (Fin n) => B ⊆ B')
  · intro B hB
    simp only [goodSets, mem_filter, mem_powersetCard] at hB
    obtain ⟨⟨-, hBc⟩, heB, hBX⟩ := hB
    have hpB : (B.powersetCard (r - 1)).card ≤ (q - 1).choose (r - 1) := by
      rw [card_powersetCard, hBc]; exact Nat.choose_le_choose _ (by omega)
    have hext := card_good_extensions n r t s hs hst B (hpB.trans hM) hr
    have hL : s ^ (t - (q - 1).choose (r - 1)) - q ≤
        s ^ (t - (B.powersetCard (r - 1)).card) - B.card := by
      have := Nat.pow_le_pow_right hs (show t - (q - 1).choose (r - 1) ≤
        t - (B.powersetCard (r - 1)).card by omega)
      omega
    refine (hL.trans hext).trans ?_
    apply card_le_card_of_injOn (fun w => insert w B)
    · intro w hw
      rw [coe_filter, Set.mem_setOf_eq, mem_sdiff] at hw
      obtain ⟨⟨-, hwB⟩, hwX⟩ := hw
      rw [mem_coe, bipartiteAbove, mem_filter, goodSets, mem_filter, mem_powersetCard]
      refine ⟨⟨⟨subset_univ _, by rw [card_insert_of_notMem hwB, hBc]⟩,
        heB.trans (subset_insert _ _), fun T hT hTe => ?_⟩, subset_insert _ _⟩
      rw [mem_powersetCard] at hT
      by_cases hwT : w ∈ T
      · have h1 : T.erase w ∈ B.powersetCard (r - 1) := by
          rw [mem_powersetCard, card_erase_of_mem hwT, hT.2]
          refine ⟨fun x hx => ?_, rfl⟩
          have hx' := mem_erase.1 hx
          rcases mem_insert.1 (hT.1 hx'.2) with h | h
          · exact absurd h hx'.1
          · exact h
        have := hwX _ h1
        rwa [insert_erase hwT] at this
      · exact hBX T ⟨(subset_insert_iff_of_notMem hwT).1 hT.1, hT.2⟩ hTe
    · intro w hw w' hw' h
      have h : insert w B = insert w' B := h
      rw [coe_filter, Set.mem_setOf_eq, mem_sdiff] at hw
      have : w ∈ insert w' B := h ▸ mem_insert_self w B
      rcases mem_insert.1 this with h' | h'
      · exact h'
      · exact absurd h' hw.1.2
  · intro B' hB'
    simp only [goodSets, mem_filter, mem_powersetCard] at hB'
    obtain ⟨⟨-, hB'c⟩, heB', -⟩ := hB'
    calc ((goodSets r b X e).bipartiteBelow (fun B B' : Finset (Fin n) => B ⊆ B') B').card
        ≤ ((B' \ e).image (fun w => B'.erase w)).card := by
          apply card_le_card
          intro B hB
          simp only [bipartiteBelow, goodSets, mem_filter, mem_powersetCard] at hB
          obtain ⟨⟨⟨-, hBc⟩, heB, -⟩, hBB'⟩ := hB
          obtain ⟨w, hw⟩ : ∃ w, B' \ B = {w} :=
            card_eq_one.1 (by rw [card_sdiff_of_subset hBB']; omega)
          have hwB' : w ∈ B' := (mem_sdiff.1 (hw ▸ mem_singleton_self w)).1
          have hwB : w ∉ B := (mem_sdiff.1 (hw ▸ mem_singleton_self w)).2
          rw [mem_image]
          refine ⟨w, mem_sdiff.2 ⟨hwB', fun h => hwB (heB h)⟩, ?_⟩
          ext x
          simp only [mem_erase]
          constructor
          · rintro ⟨hxw, hxB'⟩
            by_contra hxB
            have : x ∈ B' \ B := mem_sdiff.2 ⟨hxB', hxB⟩
            rw [hw, mem_singleton] at this
            exact hxw this
          · intro hxB
            exact ⟨fun h => hwB (h ▸ hxB), hBB' hxB⟩
      _ ≤ (B' \ e).card := card_image_le
      _ = b + 1 - r := by rw [card_sdiff_of_subset heB', hB'c, he]

theorem card_goodSets_ge (n q r t s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hst : s ^ t ≤ n)
    (hM : (q - 1).choose (r - 1) ≤ t) (e : Finset (Fin n)) (he : e.card = r) (j : ℕ) (hj : r + j ≤ q) :
    (s ^ (t - (q - 1).choose (r - 1)) - q) ^ j ≤
      (goodSets r (r + j) (digitReserve n r t s) e).card * j.factorial := by
  induction j with
  | zero =>
    simp only [pow_zero, Nat.add_zero, Nat.factorial_zero, mul_one]
    refine card_pos.2 ⟨e, ?_⟩
    simp only [goodSets, mem_filter, mem_powersetCard]
    refine ⟨⟨subset_univ _, he⟩, subset_rfl, fun T hT hTe => ?_⟩
    exact absurd (eq_of_subset_of_card_le hT.1 (by rw [hT.2, he])) hTe
  | succ j ih =>
    have h1 := ih (by omega)
    have h2 := card_goodSets_step n q r t s (r + j) hr hs hst hM (by omega) e he
    rw [show r + j + 1 - r = j + 1 by omega] at h2
    calc (s ^ (t - (q - 1).choose (r - 1)) - q) ^ (j + 1)
        = (s ^ (t - (q - 1).choose (r - 1)) - q) ^ j * (s ^ (t - (q - 1).choose (r - 1)) - q) :=
          pow_succ _ _
      _ ≤ (goodSets r (r + j) (digitReserve n r t s) e).card * j.factorial *
            (s ^ (t - (q - 1).choose (r - 1)) - q) := Nat.mul_le_mul_right _ h1
      _ = (goodSets r (r + j) (digitReserve n r t s) e).card *
            (s ^ (t - (q - 1).choose (r - 1)) - q) * j.factorial := by ring
      _ ≤ (goodSets r (r + j + 1) (digitReserve n r t s) e).card * (j + 1) * j.factorial :=
          Nat.mul_le_mul_right _ h2
      _ = (goodSets r (r + (j + 1)) (digitReserve n r t s) e).card * (j + 1).factorial := by
          rw [Nat.factorial_succ, ← Nat.add_assoc]; ring

theorem reserveCliques_eq_goodSets {n : ℕ} (q r : ℕ) (X : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) : reserveCliques q r X e = goodSets r q X e := by
  unfold reserveCliques goodSets cliqueEdges
  congr 1

/-! ### The weak reserves lemma -/

/-- The final numerical estimate for the number of reserve cliques. -/
theorem reserve_count_real {q r : ℕ} (hrq : r < q) {α : ℝ} {k M t a : ℕ} (hk : k = q - r)
    (ha : a = t - M) (hMt : M < t) (ht0 : (0 : ℝ) < t) (hkMt : (k * M : ℝ) / t ≤ α / 2)
    {n : ℕ} (hn1 : 1 ≤ n) {x : ℝ} (hxdef : x = (n : ℝ) ^ (1 / (t : ℝ))) (hx0 : 0 ≤ x)
    (hcnt : 2 ^ ((a + 1) * k) * (k.factorial : ℝ) ≤ (n : ℝ) ^ (α / 2)) {c L : ℕ}
    (hcard : L ^ k ≤ c * k.factorial) (hL2 : x ^ a / 2 ^ (a + 1) ≤ L) :
    (n : ℝ) ^ ((q : ℝ) - r - α) ≤ c := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hkq : (q : ℝ) - r = k := by rw [hk, Nat.cast_sub hrq.le]
  have hF : (0 : ℝ) < 2 ^ ((a + 1) * k) * (k.factorial : ℝ) := by positivity
  have hcard' : (L : ℝ) ^ k ≤ c * k.factorial := by exact_mod_cast hcard
  have hxak : x ^ (a * k) = (n : ℝ) ^ ((a * k : ℕ) / (t : ℝ)) := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; ring
  have hexp : (k : ℝ) - α / 2 ≤ (a * k : ℕ) / (t : ℝ) := by
    rw [ha, Nat.cast_mul, Nat.cast_sub hMt.le]
    have : ((t : ℝ) - M) * k / t = k - k * M / t := by field_simp
    rw [this]; linarith
  have h1 : (n : ℝ) ^ ((k : ℝ) - α) * (n : ℝ) ^ (α / 2) = (n : ℝ) ^ ((k : ℝ) - α / 2) := by
    rw [← Real.rpow_add hn0]; ring_nf
  have h2 : (n : ℝ) ^ ((k : ℝ) - α / 2) ≤ x ^ (a * k) := by
    rw [hxak]; exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hexp
  have h3 : x ^ (a * k) = 2 ^ ((a + 1) * k) * (x ^ a / 2 ^ (a + 1)) ^ k := by
    rw [div_pow, ← pow_mul, ← pow_mul]; field_simp
  have h4 : (x ^ a / 2 ^ (a + 1)) ^ k ≤ (L : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hL2 k
  rw [hkq]
  have h5 : (n : ℝ) ^ ((k : ℝ) - α) * (2 ^ ((a + 1) * k) * (k.factorial : ℝ)) ≤
      c * (2 ^ ((a + 1) * k) * (k.factorial : ℝ)) := by
    calc (n : ℝ) ^ ((k : ℝ) - α) * (2 ^ ((a + 1) * k) * (k.factorial : ℝ))
        ≤ (n : ℝ) ^ ((k : ℝ) - α) * (n : ℝ) ^ (α / 2) :=
          mul_le_mul_of_nonneg_left hcnt (by positivity)
      _ ≤ 2 ^ ((a + 1) * k) * (L : ℝ) ^ k := by
          rw [h1]; refine h2.trans ?_; rw [h3]
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ 2 ^ ((a + 1) * k) * (c * k.factorial) :=
          mul_le_mul_of_nonneg_left hcard' (by positivity)
      _ = c * (2 ^ ((a + 1) * k) * (k.factorial : ℝ)) := by ring
  exact le_of_mul_le_mul_right h5 hF

/-- **Weak reserves lemma**, proved by the explicit digit-sum construction. -/
theorem weakReservesLemma : WeakReservesLemma := by
  intro q r hr hrq α hα
  set k := q - r with hk
  set M := (q - 1).choose (r - 1) with hM
  set t := M + ⌈2 * k * M / α⌉₊ + 1 with ht
  set a := t - M with ha
  have hMt : M < t := by omega
  have ht0 : (0 : ℝ) < t := by positivity
  have hkMt : (k * M : ℝ) / t ≤ α / 2 := by
    rw [div_le_iff₀ ht0]
    have h1 : 2 * k * M / α ≤ (⌈2 * k * M / α⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 * k * M / α⌉₊ : ℝ) ≤ t := by
      rw [ht]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) M]
    have h3 : 2 * k * M ≤ t * α := by
      have := h1.trans h2
      rwa [div_le_iff₀ hα] at this
    linarith
  refine ⟨1 / (2 * t), by positivity, ?_⟩
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n ∧ 2 * (2 * q + 1) ≤ (n : ℝ) ^ (1 / (t : ℝ)) ∧
      4 * t ≤ (n : ℝ) ^ (1 / (2 * t : ℝ)) ∧
      2 ^ ((a + 1) * k) * (k.factorial : ℝ) ≤ (n : ℝ) ^ (α / 2) :=
    (Filter.eventually_ge_atTop 1).and <| (ev_le_rpow _ (by positivity)).and <|
      (ev_le_rpow _ (by positivity)).and (ev_le_rpow _ (by positivity))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hn1, hx, hdeg, hcnt⟩ := hn₀ n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  set y := (n : ℝ) ^ (1 / (2 * t : ℝ)) with hy
  set x := (n : ℝ) ^ (1 / (t : ℝ)) with hxdef
  have hxy : x = y ^ 2 := by
    rw [hxdef, hy, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; field_simp; norm_num
  have hxt : x ^ t = n := by
    rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le, one_div_mul_cancel ht0.ne',
      Real.rpow_one]
  have hx0 : 0 ≤ x := by positivity
  set s := ⌊x⌋₊ with hsdef
  have hs_le : (s : ℝ) ≤ x := Nat.floor_le hx0
  have hs_ge : x / 2 ≤ s := by
    have := Nat.lt_floor_add_one x
    linarith
  have hs1 : 1 ≤ s := by
    have : (1 : ℝ) ≤ s := by linarith
    exact_mod_cast this
  have hst : s ^ t ≤ n := by
    have : (s : ℝ) ^ t ≤ n := hxt ▸ pow_le_pow_left₀ (Nat.cast_nonneg s) hs_le t
    exact_mod_cast this
  refine ⟨digitReserve n r t s, filter_subset _ _, ?_, ?_⟩
  · -- the degree bound
    intro S hS
    have h1 := deg_digitReserve_mul_le n r t s hs1 hst S hS
    have h1' : (deg (digitReserve n r t s) S : ℝ) * s ≤ 2 * t * n := by exact_mod_cast h1
    have hy0 : 0 < y := by positivity
    have hd0 : (0 : ℝ) ≤ deg (digitReserve n r t s) S := Nat.cast_nonneg _
    rw [Real.rpow_sub hn0, Real.rpow_one, ← hy, le_div_iff₀ hy0]
    have h2 : (deg (digitReserve n r t s) S : ℝ) * (y ^ 2 / 2) ≤ 2 * t * n := by
      rw [← hxy]; nlinarith
    have h3 : (deg (digitReserve n r t s) S : ℝ) * y * y ≤ n * y := by nlinarith
    nlinarith
  · -- the number of reserve cliques
    intro e he
    have hec : e.card = r := (mem_powersetCard.1 (mem_sdiff.1 he).1).2
    have hqk : q = r + k := by omega
    have hcard := card_goodSets_ge n q r t s hr hs1 hst (hM ▸ hMt.le) e hec k (by omega)
    rw [← hqk, ← reserveCliques_eq_goodSets, ← hM, ← ha] at hcard
    have hLr : (s : ℝ) ^ a - q ≤ (s ^ a - q : ℕ) := by
      have : s ^ a ≤ (s ^ a - q) + q := by omega
      have : ((s ^ a : ℕ) : ℝ) ≤ ((s ^ a - q : ℕ) : ℝ) + q := by exact_mod_cast this
      push_cast at this; linarith
    have hx2 : 1 ≤ x / 2 := by linarith
    have hpa : x / 2 ≤ (x / 2) ^ a := le_self_pow₀ hx2 (by omega)
    have hsa : (x / 2) ^ a ≤ (s : ℝ) ^ a := pow_le_pow_left₀ (by positivity) hs_ge a
    have hz : x ^ a / 2 ^ (a + 1) = (x / 2) ^ a / 2 := by
      rw [div_pow, pow_succ]; field_simp
    exact reserve_count_real hrq hk ha hMt ht0 hkMt hn1 hxdef hx0 hcnt hcard
      (by rw [hz]; linarith)

/-! ### The Existence Conjecture from the three remaining ingredients -/

/-- **The Existence Conjecture via refined absorption, with the reserves lemma proved.**  The
refined efficient omni-absorber theorem (Theorem 1.10), the boost lemma (Lemma 2.2) and the
nibble with reserves (Corollary 2.4, with general polynomial error) imply the existence of
`(n, q, r)`-Steiner systems for all large `n` satisfying the divisibility conditions; the
reserves are provided by the explicit construction `digitReserve`. -/
theorem steinerExistence_of_omniAbsorber_boost_nibble (hOmni : RefinedEfficientOmniAbsorber)
    (hBoost : BoostLemma) (hNib : NibbleWithReservesGen) : SteinerExistenceConjecture :=
  steinerExistence_of_weakReserves weakReservesLemma hOmni hBoost hNib

end RefinedAbsorption
