module
public import RequestProject.Multigraph.ReserveCoverMulti
public import RequestProject.Nibble.Bridge

/-!
# Corollary 2.4 for multigraphs (nibble with reserves for multigraphs)

A multigraph on `[n]` is given here by `m` layers `G 0, …, G (m-1) ⊆ K_n^r`: the multiplicity of
an `r`-set `T` is the number `layerCount m G T` of layers containing it.  The layers may overlap
each other and the reserves `X`.

**Corollary 2.4 for multigraphs** (`NibbleWithReservesMulti`, proved as
`nibbleWithReservesMulti_proved`): if every layer `G j` comes with a family `H j` of cliques in
which every edge of `G j` lies in `(ρ ± n^{-β}) binom(n, q-r)` cliques, and every edge of every
layer has at least `n^{q-r-α}` reserve cliques in `X ∪ {e}`, then there is a *set* of distinct
copies of `K_q^r`, avoiding any prescribed family `Φ` of bounded multiplicity, which covers every
`r`-set `T` exactly `layerCount m G T` times, plus possibly once more if `T ∈ X`.  In other words,
it is a `K_q^r`-packing of the multigraph `G + X` covering all of `G`, without repeated cliques.

For `m = 1`, `Φ = ∅` and `X` disjoint from `G` this is exactly Corollary 2.4 of the survey
(`nibbleWithReservesGen_of_multi`).

The proof runs the nibble (with leftover degree control, packing inside the given family) layer
by layer, removing from the clique family of each layer the forbidden cliques and the cliques
already used, and then covers the union of the leftovers of all layers with the reserves
(`reserve_cover_multi`).
-/

@[expose] public section

namespace RefinedAbsorption

open Finset Filter

/-- **Corollary 2.4 for multigraphs (nibble with reserves, multigraph version).**  For
`q > r ≥ 1`, `ρ ∈ (0,1]`, `β ∈ (0,1)` and `m, c ∈ ℕ` there is `α ∈ (0,1)` such that for all large
`n` the following holds.  Let `G 0, …, G (m-1) ⊆ K_n^r` (the layers of a multigraph) and
`H j ⊆ K_q^r(G j)` be such that every edge of `G j` is in `(ρ ± n^{-β}) binom(n, q-r)` cliques of
`H j`.  Let `Φ` be a family of `q`-sets in which every `r`-set lies in at most `c` members, and
let `X` be such that every edge `e` of every layer is in at least `n^{q-r-α}` copies of `K_q^r` in
`X ∪ {e}`.  Then there is a set `P` of copies of `K_q^r` disjoint from `Φ` such that every
`r`-set `T` lies in at least `#{j < m : T ∈ G j}` and at most `#{j < m : T ∈ G j} + [T ∈ X]`
cliques of `P`. -/
def NibbleWithReservesMulti : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ β : ℝ, 0 < β → β < 1 → ∀ m c : ℕ,
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (G H : ℕ → Finset (Finset (Fin n))) (X Φ : Finset (Finset (Fin n))),
      (∀ j < m, G j ⊆ completeRGraph (Fin n) r) →
      (∀ j < m, H j ⊆ cliquesOf q r (G j)) →
      (∀ j < m, ∀ e ∈ G j, |(cliqueMult (H j) e : ℝ) - ρ * (n.choose (q - r))|
          ≤ (n : ℝ) ^ (-β) * (n.choose (q - r))) →
      (∀ e : Finset (Fin n), e.card = r → cliqueMult Φ e ≤ c) →
      (∀ j < m, ∀ e ∈ G j, (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e).card) →
        ∃ P : Finset (Finset (Fin n)), (∀ Q ∈ P, Q.card = q) ∧ Disjoint P Φ ∧
          ∀ T : Finset (Fin n), T.card = r →
            layerCount m G T ≤ cliqueMult P T ∧
              cliqueMult P T ≤ layerCount m G T + if T ∈ X then 1 else 0

/-! ### Elementary facts -/

theorem cliqueMult_union_of_disjoint {V : Type*} [DecidableEq V] {A B : Finset (Finset V)}
    (h : Disjoint A B) (e : Finset V) :
    cliqueMult (A ∪ B) e = cliqueMult A e + cliqueMult B e := by
  unfold cliqueMult
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

theorem cliqueMult_le_sdiff_add {V : Type*} [DecidableEq V] (A B : Finset (Finset V))
    (e : Finset V) : cliqueMult A e ≤ cliqueMult (A \ B) e + cliqueMult B e := by
  unfold cliqueMult
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro Q hQ
  rw [mem_filter] at hQ
  by_cases hB : Q ∈ B
  · exact mem_union_right _ (mem_filter.2 ⟨hB, hQ.2⟩)
  · exact mem_union_left _ (mem_filter.2 ⟨mem_sdiff.2 ⟨hQ.1, hB⟩, hQ.2⟩)

theorem cliqueMult_sdiff_le {V : Type*} [DecidableEq V] (A B : Finset (Finset V))
    (e : Finset V) : cliqueMult (A \ B) e ≤ cliqueMult A e :=
  card_le_card (filter_subset_filter _ sdiff_subset)

theorem layerCount_zero {V : Type*} [DecidableEq V] (R : ℕ → Finset (Finset V)) (T : Finset V) :
    layerCount 0 R T = 0 := by simp [layerCount]

theorem layerCount_succ {V : Type*} [DecidableEq V] (k : ℕ) (R : ℕ → Finset (Finset V))
    (T : Finset V) : layerCount (k + 1) R T = layerCount k R T + if T ∈ R k then 1 else 0 := by
  unfold layerCount
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem layerCount_congr {V : Type*} [DecidableEq V] {k : ℕ} {R R' : ℕ → Finset (Finset V)}
    (h : ∀ j < k, R j = R' j) (T : Finset V) : layerCount k R T = layerCount k R' T := by
  unfold layerCount
  congr 1
  exact filter_congr fun j hj => by rw [h j (mem_range.1 hj)]

theorem layerCount_le {V : Type*} [DecidableEq V] (k : ℕ) (R : ℕ → Finset (Finset V))
    (T : Finset V) : layerCount k R T ≤ k := by
  unfold layerCount
  exact (card_filter_le _ _).trans (by simp)

/-- In a packing, an `r`-set lies in one clique if it is covered and in none otherwise. -/
theorem IsPacking.cliqueMult_eq {V : Type*} [DecidableEq V] {q r : ℕ} {G P : Finset (Finset V)}
    (hP : IsPacking q r G P) {T : Finset V} (hT : T.card = r) :
    cliqueMult P T = if T ∈ coveredEdges r P then 1 else 0 := by
  have h1 := hP.mult_le T hT
  split_ifs with hc
  · obtain ⟨Q, hQ, hTQ⟩ := mem_biUnion.1 hc
    have : 0 < cliqueMult P T :=
      card_pos.2 ⟨Q, mem_filter.2 ⟨hQ, (mem_powersetCard.1 hTQ).1⟩⟩
    omega
  · rw [cliqueMult, card_eq_zero, filter_eq_empty_iff]
    intro Q hQ hTQ
    exact hc (mem_biUnion.2 ⟨Q, hQ, mem_powersetCard.2 ⟨hTQ, hT⟩⟩)

/-- The number of reserve cliques avoiding a family `Φ'` of bounded multiplicity. -/
theorem card_reserveCliques_sdiff {n q r : ℕ} (X Φ' : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) :
    (reserveCliques q r X e).card ≤ (reserveCliques q r X e \ Φ').card + cliqueMult Φ' e := by
  unfold cliqueMult
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro Q hQ
  by_cases hB : Q ∈ Φ'
  · simp only [reserveCliques, mem_filter] at hQ
    exact mem_union_right _ (mem_filter.2 ⟨hB, hQ.2.1⟩)
  · exact mem_union_left _ (mem_sdiff.2 ⟨hQ, hB⟩)

/-! ### Asymptotic estimates -/

/-- Removing a bounded number of cliques per edge costs less than the change of error from
`n^{-β}` to `n^{-β/2}`. -/
theorem ev_removal {k : ℕ} (hk : 1 ≤ k) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c + (n : ℝ) ^ (-β) * (n.choose k) ≤ (n : ℝ) ^ (-(β / 2)) * (n.choose k) := by
  have hF : (0 : ℝ) < 2 ^ k * (k.factorial : ℝ) := by positivity
  have e1 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-β) ≤ (1 / 2) * (n : ℝ) ^ (-(β / 2)) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_rpow_le_mul_rpow (show -β < -(β / 2) by linarith) (by norm_num))
  have hkβ : 0 < (k : ℝ) - β / 2 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  filter_upwards [eventually_ge_atTop (2 * k), eventually_ge_atTop 1, e1,
    ev_le_rpow (2 * |c| * (2 ^ k * (k.factorial : ℝ))) hkβ] with n hn hn1 h1 h2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hB := choose_lower_bound hn
  have hB0 : (0 : ℝ) ≤ n.choose k := by positivity
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-(β / 2)) := by positivity
  have e2 : (n : ℝ) ^ (-(β / 2)) * ((n : ℝ) ^ k / (2 ^ k * k.factorial)) =
      (n : ℝ) ^ ((k : ℝ) - β / 2) / (2 ^ k * k.factorial) := by
    rw [mul_div_assoc', ← Real.rpow_natCast, ← Real.rpow_add hn0]; ring_nf
  have h3 : c ≤ (1 / 2) * ((n : ℝ) ^ (-(β / 2)) * (n.choose k)) := by
    have h4 : (n : ℝ) ^ (-(β / 2)) * ((n : ℝ) ^ k / (2 ^ k * k.factorial)) ≤
        (n : ℝ) ^ (-(β / 2)) * (n.choose k) := mul_le_mul_of_nonneg_left hB hp
    rw [e2] at h4
    have h5 : 2 * |c| ≤ (n : ℝ) ^ ((k : ℝ) - β / 2) / (2 ^ k * k.factorial) := by
      rw [le_div_iff₀ hF]; linarith
    linarith [le_abs_self c]
  nlinarith [mul_le_mul_of_nonneg_right h1 hB0]

/-- `c + n^{a-s} ≤ n^{a-s/2}` for large `n`, if `a - s/2 > 0` and `s > 0`. -/
theorem ev_reserve_slack {a s : ℝ} (hs : 0 < s) (has : 0 < a - s / 2) (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c + (n : ℝ) ^ (a - s) ≤ (n : ℝ) ^ (a - s / 2) := by
  have e1 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (a - s) ≤ (1 / 2) * (n : ℝ) ^ (a - s / 2) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_rpow_le_mul_rpow (show a - s < a - s / 2 by linarith) (by norm_num))
  filter_upwards [e1, ev_le_rpow (2 * |c|) has] with n h1 h2
  linarith [le_abs_self c]

/-! ### The nibble, layer by layer -/

theorem cliqueMult_union_le {V : Type*} [DecidableEq V] (A B : Finset (Finset V))
    (e : Finset V) : cliqueMult (A ∪ B) e ≤ cliqueMult A e + cliqueMult B e := by
  unfold cliqueMult
  rw [filter_union]
  exact card_union_le _ _

/-- **The nibble applied to the layers one after another.**  Given the nibble (packing inside
the given family) for one fixed `n`, every layer `G j` (for `j < k ≤ m`) gets a packing using
cliques of `H j` that are neither forbidden nor used before; the leftovers `R j` have small
degrees, and every `r`-set is covered by the packings exactly as often as it lies in layers minus
leftovers. -/
theorem layers_exist {n q r : ℕ} {ρ β γ : ℝ} (c m : ℕ)
    (hnib : ∀ G ⊆ completeRGraph (Fin n) r, ∀ H ⊆ cliquesOf q r G,
      (∀ e ∈ G, |(cliqueMult H e : ℝ) - ρ * (n.choose (q - r))|
          ≤ (n : ℝ) ^ (-(β / 2)) * (n.choose (q - r))) →
      ∃ P ⊆ H, IsPacking q r G P ∧ MaxDegLE r (G \ coveredEdges r P) ((n : ℝ) ^ (1 - γ)))
    (hrem : ((c + m : ℕ) : ℝ) + (n : ℝ) ^ (-β) * (n.choose (q - r))
      ≤ (n : ℝ) ^ (-(β / 2)) * (n.choose (q - r)))
    (G H : ℕ → Finset (Finset (Fin n))) (Φ : Finset (Finset (Fin n)))
    (hG : ∀ j < m, G j ⊆ completeRGraph (Fin n) r) (hH : ∀ j < m, H j ⊆ cliquesOf q r (G j))
    (hreg : ∀ j < m, ∀ e ∈ G j, |(cliqueMult (H j) e : ℝ) - ρ * (n.choose (q - r))|
          ≤ (n : ℝ) ^ (-β) * (n.choose (q - r)))
    (hΦ : ∀ e : Finset (Fin n), e.card = r → cliqueMult Φ e ≤ c) :
    ∀ k ≤ m, ∃ Pc : Finset (Finset (Fin n)), ∃ R : ℕ → Finset (Finset (Fin n)),
      (∀ Q ∈ Pc, Q.card = q) ∧ Disjoint Pc Φ ∧
      (∀ j < k, R j ⊆ G j ∧ MaxDegLE r (R j) ((n : ℝ) ^ (1 - γ))) ∧
      ∀ T : Finset (Fin n), T.card = r → cliqueMult Pc T + layerCount k R T = layerCount k G T := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨∅, fun _ => ∅, by simp, by simp, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun T _ => by simp [layerCount_zero, cliqueMult]⟩
  | succ k ih =>
    intro hkm
    obtain ⟨Pc, R, hPcq, hPcΦ, hR, hcount⟩ := ih (by omega)
    have hk : k < m := by omega
    set H' := H k \ (Φ ∪ Pc) with hH'
    have hH'G : H' ⊆ cliquesOf q r (G k) := sdiff_subset.trans (hH k hk)
    have hreg' : ∀ e ∈ G k, |(cliqueMult H' e : ℝ) - ρ * (n.choose (q - r))|
        ≤ (n : ℝ) ^ (-(β / 2)) * (n.choose (q - r)) := by
      intro e he
      have her : e.card = r := (mem_powersetCard.1 (hG k hk he)).2
      have h1 : cliqueMult (H k) e ≤ cliqueMult H' e + cliqueMult (Φ ∪ Pc) e :=
        cliqueMult_le_sdiff_add _ _ e
      have h2 := cliqueMult_union_le Φ Pc e
      have h3 := hΦ e her
      have h4 : cliqueMult Pc e ≤ k := by
        have := hcount e her
        have := layerCount_le k G e
        omega
      have h5 : cliqueMult H' e ≤ cliqueMult (H k) e := cliqueMult_sdiff_le _ _ e
      have hlow : (cliqueMult (H k) e : ℝ) ≤ cliqueMult H' e + ((c + m : ℕ) : ℝ) := by
        have : cliqueMult (H k) e ≤ cliqueMult H' e + (c + m) := by omega
        exact_mod_cast this
      have hup : (cliqueMult H' e : ℝ) ≤ cliqueMult (H k) e := by exact_mod_cast h5
      have hb := abs_le.1 (hreg k hk e he)
      have hc0 : (0 : ℝ) ≤ ((c + m : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [abs_le]; constructor <;> linarith
    obtain ⟨P, hPH, hP, hPdeg⟩ := hnib (G k) (hG k hk) H' hH'G hreg'
    have hPPc : Disjoint Pc P := by
      rw [disjoint_right]; intro Q hQ hQ'
      exact (mem_sdiff.1 (hPH hQ)).2 (mem_union_right _ hQ')
    set R' : ℕ → Finset (Finset (Fin n)) :=
      fun j => if j = k then G k \ coveredEdges r P else R j with hR'
    refine ⟨Pc ∪ P, R', ?_, ?_, ?_, ?_⟩
    · intro Q hQ
      rcases mem_union.1 hQ with h | h
      · exact hPcq Q h
      · exact hP.card_eq Q h
    · rw [disjoint_union_left]
      refine ⟨hPcΦ, ?_⟩
      rw [disjoint_left]; intro Q hQ hQ'
      exact (mem_sdiff.1 (hPH hQ)).2 (mem_union_left _ hQ')
    · intro j hj
      by_cases hjk : j = k
      · subst hjk
        simp only [hR', if_true]
        exact ⟨sdiff_subset, hPdeg⟩
      · simp only [hR', if_neg hjk]
        exact hR j (by omega)
    · intro T hT
      rw [cliqueMult_union_of_disjoint hPPc, layerCount_succ, layerCount_succ,
        layerCount_congr (R := R') (R' := R) (fun j hj => by simp [hR', Nat.ne_of_lt hj]),
        hP.cliqueMult_eq hT]
      have h0 := hcount T hT
      have hRk : R' k = G k \ coveredEdges r P := by simp [hR']
      rw [hRk]
      have hcovG : coveredEdges r P ⊆ G k := hP.coveredEdges_subset
      by_cases hc : T ∈ coveredEdges r P
      · have := hcovG hc
        simp [hc, this]; omega
      · by_cases hTG : T ∈ G k
        · simp [hc, hTG]; omega
        · simp [hc, hTG]; omega

/-! ### Corollary 2.4 for multigraphs -/

/-- **Corollary 2.4 for multigraphs** (proved). -/
theorem nibbleWithReservesMulti_proved : NibbleWithReservesMulti := by
  intro q r hr hrq ρ hρ hρ1 β hβ hβ1 m c
  obtain ⟨γ, hγ, n₁, hnib⟩ :=
    nibbleLeftoverDegreeSub_proved q r hr hrq ρ hρ hρ1 (β / 2) (by positivity) (by linarith)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set α' : ℝ := min (γ / (4 * r)) (1 / 2) with hα'def
  have hα' : 0 < α' := lt_min (by positivity) (by norm_num)
  have hα'2 : α' ≤ 1 / 2 := min_le_right _ _
  have hα'γ : 4 * α' * r ≤ γ := by
    have : α' ≤ γ / (4 * r) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  refine ⟨α' / 2, by positivity, by linarith, ?_⟩
  have hqr : (1 : ℝ) ≤ (q : ℝ) - r := by
    have : ((r + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hrq
    push_cast at this; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((reserve_cover_multi q r hr hrq m hα' hα'2 hα'γ).and
    ((ev_removal (k := q - r) (by omega) hβ hβ1 ((c + m : ℕ) : ℝ)).and
      (ev_reserve_slack (a := (q : ℝ) - r) hα' (by linarith) ((c + m : ℕ) : ℝ))))
  refine ⟨max n₁ N, fun n hn G H X Φ hG hH hreg hΦ hres => ?_⟩
  obtain ⟨hRC, hrem, hslack⟩ := hN n (le_of_max_le_right hn)
  have hnib' := hnib n (le_of_max_le_left hn)
  obtain ⟨Pc, R, hPcq, hPcΦ, hR, hcount⟩ :=
    layers_exist c m hnib' hrem G H Φ hG hH hreg hΦ m le_rfl
  have hPcm : ∀ e : Finset (Fin n), e.card = r → cliqueMult Pc e ≤ m := by
    intro e he
    have := hcount e he
    have := layerCount_le m G e
    omega
  have hresR : ∀ j < m, ∀ e ∈ R j,
      (n : ℝ) ^ ((q : ℝ) - r - α') ≤ (reserveCliques q r X e \ (Φ ∪ Pc)).card := by
    intro j hj e he
    have heG : e ∈ G j := (hR j hj).1 he
    have her : e.card = r := (mem_powersetCard.1 (hG j hj heG)).2
    have h1 := card_reserveCliques_sdiff (q := q) (r := r) X (Φ ∪ Pc) e
    have h2 := cliqueMult_union_le Φ Pc e
    have h3 := hΦ e her
    have h4 := hPcm e her
    have h5 : ((reserveCliques q r X e).card : ℝ) ≤
        (reserveCliques q r X e \ (Φ ∪ Pc)).card + ((c + m : ℕ) : ℝ) := by
      have : (reserveCliques q r X e).card ≤ (reserveCliques q r X e \ (Φ ∪ Pc)).card + (c + m) := by
        omega
      exact_mod_cast this
    have h6 := hres j hj e heG
    linarith
  obtain ⟨P₂, hP₂q, hP₂Φ, hP₂⟩ := hRC R X (Φ ∪ Pc) (fun j hj => (hR j hj).1.trans (hG j hj))
    (fun j hj => (hR j hj).2) hresR
  rw [disjoint_union_right] at hP₂Φ
  have hdisj : Disjoint Pc P₂ := hP₂Φ.2.symm
  refine ⟨Pc ∪ P₂, ?_, ?_, ?_⟩
  · intro Q hQ
    rcases mem_union.1 hQ with h | h
    · exact hPcq Q h
    · exact hP₂q Q h
  · rw [disjoint_union_left]; exact ⟨hPcΦ, hP₂Φ.1⟩
  · intro T hT
    rw [cliqueMult_union_of_disjoint hdisj]
    have h1 := hcount T hT
    obtain ⟨h2, h3⟩ := hP₂ T hT
    constructor <;> omega

/-- For one layer, no forbidden cliques and reserves disjoint from the layer, Corollary 2.4 for
multigraphs is Corollary 2.4 of the survey (with general polynomial error). -/
theorem nibbleWithReservesGen_of_multi (h : NibbleWithReservesMulti) : NibbleWithReservesGen := by
  intro q r hr hrq ρ hρ hρ1 β hβ hβ1
  obtain ⟨α, hα, hα1, n₀, h'⟩ := h q r hr hrq ρ hρ hρ1 β hβ hβ1 1 0
  refine ⟨α, hα, hα1, n₀, fun n hn G hG H hH hreg X hX hres => ?_⟩
  obtain ⟨P, hPq, -, hP⟩ := h' n hn (fun _ => G) (fun _ => H) X ∅ (fun _ _ => hG)
    (fun _ _ => hH) (fun _ _ => hreg) (fun e _ => by simp [cliqueMult])
    (fun _ _ => hres)
  have hGX : ∀ T, T ∈ X → T ∉ G := fun T hT hTG => (mem_sdiff.1 (hX hT)).2 hTG
  have hlc : ∀ T : Finset (Fin n), layerCount 1 (fun _ => G) T = if T ∈ G then 1 else 0 := by
    intro T; rw [layerCount_succ, layerCount_zero, zero_add]
  refine ⟨P, ⟨hPq, fun Q hQ T hT => ?_, fun T hT => ?_⟩, fun T hT => ?_⟩
  · have hTr : T.card = r := (mem_powersetCard.1 hT).2
    have hpos : 0 < cliqueMult P T := card_pos.2 ⟨Q, mem_filter.2 ⟨hQ, (mem_powersetCard.1 hT).1⟩⟩
    have := (hP T hTr).2
    rw [hlc] at this
    by_cases hTG : T ∈ G
    · exact mem_union_left _ hTG
    · by_cases hTX : T ∈ X
      · exact mem_union_right _ hTX
      · simp [hTG, hTX] at this; omega
  · have := (hP T hT).2
    rw [hlc] at this
    by_cases hTX : T ∈ X
    · simp [hTX, hGX T hTX] at this; omega
    · by_cases hTG : T ∈ G <;> simp [hTG, hTX] at this <;> omega
  · have hTr : T.card = r := (mem_powersetCard.1 (hG hT)).2
    have := (hP T hTr).1
    rw [hlc, if_pos hT] at this
    obtain ⟨Q, hQ⟩ := card_pos.1 this
    rw [mem_filter] at hQ
    exact mem_biUnion.2 ⟨Q, hQ.1, mem_powersetCard.2 ⟨hQ.2, hTr⟩⟩

end RefinedAbsorption
