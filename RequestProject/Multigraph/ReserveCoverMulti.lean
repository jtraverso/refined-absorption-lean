module
public import RequestProject.ReserveCover
public import RequestProject.WeightedNibbleBridge

/-!
# Covering a multigraph leftover with reserves, avoiding forbidden cliques

This is the multigraph version of `reserve_cover`.  The leftover is given in `m` layers
`R 0, …, R (m-1)` (simple `r`-graphs, which may overlap each other and the reserves `X`), each
with small `(r-1)`-degrees; every edge of every layer has to be covered once *for each layer it
belongs to*.  We find a set `P` of distinct `q`-sets, avoiding a forbidden family `Φ`, such that
every `r`-set `T` lies in exactly `#{j : T ∈ R j}` cliques of `P`, plus at most one more if
`T ∈ X` (that is, every edge of `X` is used at most once as a reserve edge).

The proof is the same greedy algorithm as for `reserve_cover`, run over the *slots* `(j, e)` with
`e ∈ R j`.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset Filter

variable {n : ℕ}

/-- The number of layers `j < m` containing the `r`-set `T`. -/
def layerCount {V : Type*} [DecidableEq V] (m : ℕ) (R : ℕ → Finset (Finset V)) (T : Finset V) :
    ℕ :=
  ((range m).filter (fun j => T ∈ R j)).card

/-- The slots of a layered leftover: pairs `(j, e)` with `j < m` and `e ∈ R j`. -/
def layerSlots {V : Type*} [DecidableEq V] (m : ℕ) (R : ℕ → Finset (Finset V)) :
    Finset (ℕ × Finset V) :=
  (range m).biUnion (fun j => (R j).image (fun e => (j, e)))

/-- The number of slots with edge `T`. -/
def slotCount {V : Type*} [DecidableEq V] (D : Finset (ℕ × Finset V)) (T : Finset V) : ℕ :=
  (D.filter (fun d => d.2 = T)).card

/-- The number of slots whose edge contains `S`. -/
def slotDeg {V : Type*} [DecidableEq V] (D : Finset (ℕ × Finset V)) (S : Finset V) : ℕ :=
  (D.filter (fun d => S ⊆ d.2)).card

theorem slotCount_layerSlots {V : Type*} [DecidableEq V] (m : ℕ) (R : ℕ → Finset (Finset V))
    (T : Finset V) : slotCount (layerSlots m R) T = layerCount m R T := by
  unfold slotCount layerCount layerSlots
  have : (((range m).biUnion (fun j => (R j).image (fun e => (j, e))))).filter
      (fun d => d.2 = T) = ((range m).filter (fun j => T ∈ R j)).image (fun j => (j, T)) := by
    ext ⟨j, e⟩
    simp only [mem_filter, mem_biUnion, mem_range, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨i, hi, e', he', rfl, rfl⟩, rfl⟩
      exact ⟨i, ⟨hi, he'⟩, rfl, rfl⟩
    · rintro ⟨i, ⟨hi, hT⟩, rfl, rfl⟩
      exact ⟨⟨i, hi, T, hT, rfl, rfl⟩, rfl⟩
  rw [this, card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]

theorem slotDeg_layerSlots_le {V : Type*} [DecidableEq V] (m : ℕ) (R : ℕ → Finset (Finset V))
    (S : Finset V) : slotDeg (layerSlots m R) S ≤ ∑ j ∈ range m, deg (R j) S := by
  unfold slotDeg layerSlots deg
  rw [filter_biUnion]
  refine card_biUnion_le.trans (sum_le_sum fun j _ => ?_)
  rw [filter_image]
  exact card_image_le

theorem mem_layerSlots {V : Type*} [DecidableEq V] {m : ℕ} {R : ℕ → Finset (Finset V)}
    {d : ℕ × Finset V} : d ∈ layerSlots m R ↔ d.1 < m ∧ d.2 ∈ R d.1 := by
  obtain ⟨j, e⟩ := d
  simp only [layerSlots, mem_biUnion, mem_range, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, e', he', rfl, rfl⟩; exact ⟨hi, he'⟩
  · rintro ⟨hi, he⟩; exact ⟨j, hi, e, he, rfl, rfl⟩

theorem slotCount_insert {V : Type*} [DecidableEq V] {D : Finset (ℕ × Finset V)}
    {d : ℕ × Finset V} (hd : d ∉ D) (T : Finset V) :
    slotCount (insert d D) T = slotCount D T + if d.2 = T then 1 else 0 := by
  unfold slotCount
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => hd (mem_filter.1 h').1)]
  · rfl

theorem slotDeg_insert {V : Type*} [DecidableEq V] {D : Finset (ℕ × Finset V)}
    {d : ℕ × Finset V} (hd : d ∉ D) (S : Finset V) :
    slotDeg (insert d D) S = slotDeg D S + if S ⊆ d.2 then 1 else 0 := by
  unfold slotDeg
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => hd (mem_filter.1 h').1)]
  · rfl

theorem slotDeg_mono {V : Type*} [DecidableEq V] {D D' : Finset (ℕ × Finset V)} (h : D ⊆ D')
    (S : Finset V) : slotDeg D S ≤ slotDeg D' S :=
  card_le_card (filter_subset_filter _ h)

/-- The invariant of the multigraph greedy algorithm after the slots of `D` have been treated. -/
structure SlotInv (q r : ℕ) (X Φ : Finset (Finset (Fin n))) (D : Finset (ℕ × Finset (Fin n)))
    (τ : ℕ → ℕ) (P : Finset (Finset (Fin n))) : Prop where
  card_eq : ∀ Q ∈ P, Q.card = q
  disj : Disjoint P Φ
  lower : ∀ T : Finset (Fin n), T.card = r → slotCount D T ≤ cliqueMult P T
  upper : ∀ T : Finset (Fin n), T.card = r →
    cliqueMult P T ≤ slotCount D T + if T ∈ X then 1 else 0
  load : ∀ S : Finset (Fin n), S.card < r → cliqueMult P S ≤ slotDeg D S + τ S.card

theorem slotInv_empty (q r : ℕ) (X Φ : Finset (Finset (Fin n))) (τ : ℕ → ℕ) :
    SlotInv q r X Φ ∅ τ ∅ :=
  ⟨by simp, by simp, fun _ _ => by simp [slotCount], fun _ _ => by simp [cliqueMult],
    fun _ _ => by simp [cliqueMult]⟩

/-- An `r`-subset of a `q`-set different from a given set, when `1 ≤ r < q`. -/
theorem exists_rsubset_ne {V : Type*} [DecidableEq V] {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q)
    {Q : Finset V} (hQ : Q.card = q) (e : Finset V) :
    ∃ T ⊆ Q, T.card = r ∧ T ≠ e := by
  have h2 : 1 < (Q.powersetCard r).card := by
    rw [card_powersetCard, hQ]; have := two_le_choose_of_lt hr hrq; omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 h2
  rw [mem_powersetCard] at ha hb
  by_cases hae : a = e
  · exact ⟨b, hb.1, hb.2, fun h => hab (hae.trans h.symm)⟩
  · exact ⟨a, ha.1, ha.2, hae⟩

/-- One step of the multigraph greedy algorithm. -/
theorem SlotInv.insert {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) {X Φ : Finset (Finset (Fin n))}
    {D : Finset (ℕ × Finset (Fin n))} {τ : ℕ → ℕ} {P : Finset (Finset (Fin n))}
    (hτr : τ r = 1) (hinv : SlotInv q r X Φ D τ P) {d : ℕ × Finset (Fin n)} (hd : d ∉ D)
    (he : d.2.card = r) {Q : Finset (Fin n)} (hQ : Q ∈ reserveCliques q r X d.2 \ Φ)
    (hgood : ∀ S ⊆ Q, S.card ≤ r → ¬ S ⊆ d.2 → cliqueMult P S < τ S.card) :
    SlotInv q r X Φ (insert d D) τ (insert Q P) := by
  obtain ⟨hQ, hQΦ⟩ := mem_sdiff.1 hQ
  simp only [reserveCliques, mem_filter, mem_powersetCard] at hQ
  obtain ⟨⟨-, hQq⟩, heQ, hQX⟩ := hQ
  -- edges of `Q` other than `d.2` are unused and lie in `X`
  have hnew : ∀ T ⊆ Q, T.card = r → T ≠ d.2 → cliqueMult P T = 0 ∧ T ∈ X := by
    intro T hTQ hT hTe
    have hTe' : ¬ T ⊆ d.2 := fun h => hTe (eq_of_subset_of_card_le h (by rw [hT, he]))
    have := hgood T hTQ hT.le hTe'
    rw [hT, hτr] at this
    exact ⟨by omega, hQX T (mem_powersetCard.2 ⟨hTQ, hT⟩) hTe⟩
  have hQP : Q ∉ P := by
    intro hQP
    obtain ⟨T, hTQ, hT, hTe⟩ := exists_rsubset_ne hr hrq hQq d.2
    have h0 := (hnew T hTQ hT hTe).1
    have : 0 < cliqueMult P T := card_pos.2 ⟨Q, mem_filter.2 ⟨hQP, hTQ⟩⟩
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Q' hQ'
    rcases mem_insert.1 hQ' with rfl | h
    · exact hQq
    · exact hinv.card_eq Q' h
  · rw [disjoint_insert_left]; exact ⟨hQΦ, hinv.disj⟩
  · intro T hT
    rw [cliqueMult_insert_of_notMem hQP, slotCount_insert hd]
    have h0 := hinv.lower T hT
    by_cases hTQ : T ⊆ Q
    · by_cases hTe : T = d.2
      · subst hTe; rw [if_pos hTQ, if_pos rfl]; omega
      · rw [if_pos hTQ, if_neg (Ne.symm hTe)]; omega
    · have : ¬ d.2 = T := fun h => hTQ (h ▸ heQ)
      rw [if_neg hTQ, if_neg this]; omega
  · intro T hT
    rw [cliqueMult_insert_of_notMem hQP, slotCount_insert hd]
    have h0 := hinv.upper T hT
    by_cases hTQ : T ⊆ Q
    · by_cases hTe : T = d.2
      · subst hTe; simp only [if_true, hTQ]; omega
      · obtain ⟨h1, h2⟩ := hnew T hTQ hT hTe
        rw [if_pos hTQ, if_neg (Ne.symm hTe), h1, if_pos h2]; omega
    · have : ¬ d.2 = T := fun h => hTQ (h ▸ heQ)
      rw [if_neg hTQ, if_neg this]; omega
  · intro S hS
    rw [cliqueMult_insert_of_notMem hQP, slotDeg_insert hd]
    have h0 := hinv.load S hS
    split_ifs with hSQ hSe hSe
    · omega
    · have := hgood S hSQ hS.le hSe
      omega
    · exact absurd (hSe.trans heQ) hSQ
    · omega

/-- **Covering a layered (multigraph) leftover with reserves, avoiding forbidden cliques.**
Let `1 ≤ r < q`, `m ∈ ℕ`, `0 < α ≤ 1/2` and `γ ≥ 4αr`.  For all large `n`: if
`R 0, …, R (m-1) ⊆ K_n^r` all have `(r-1)`-degrees at most `n^{1-γ}`, and every edge `e` of every
layer lies in at least `n^{q-r-α}` copies of `K_q^r` in `X ∪ {e}` that are not in `Φ`, then there
is a set `P` of `q`-sets disjoint from `Φ` such that every `r`-set `T` lies in at least
`#{j < m : T ∈ R j}` and at most `#{j < m : T ∈ R j} + [T ∈ X]` cliques of `P`. -/
theorem reserve_cover_multi (q r : ℕ) (hr : 1 ≤ r) (hrq : r < q) (m : ℕ) {α γ : ℝ}
    (hα : 0 < α) (hα2 : α ≤ 1 / 2) (hγ : 4 * α * r ≤ γ) :
    ∀ᶠ n : ℕ in atTop, ∀ (R : ℕ → Finset (Finset (Fin n))) (X Φ : Finset (Finset (Fin n))),
      (∀ j < m, R j ⊆ completeRGraph (Fin n) r) →
      (∀ j < m, MaxDegLE r (R j) ((n : ℝ) ^ (1 - γ))) →
      (∀ j < m, ∀ e ∈ R j, (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e \ Φ).card) →
        ∃ P : Finset (Finset (Fin n)), (∀ Q ∈ P, Q.card = q) ∧ Disjoint P Φ ∧
          ∀ T : Finset (Fin n), T.card = r →
            layerCount m R T ≤ cliqueMult P T ∧
              cliqueMult P T ≤ layerCount m R T + if T ∈ X then 1 else 0 := by
  have hθ : 0 ≤ 1 - 2 * α := by linarith
  have hγ0 : 0 < γ := by
    have : (0 : ℝ) < 4 * α * r := by positivity
    linarith
  set K : ℝ := ((r : ℝ) + 1) * 2 ^ r * (3 * 2 ^ q) with hK
  have hK0 : 0 ≤ K := by positivity
  filter_upwards [eventually_ge_atTop 1,
    ev_rpow_neg_le hα (show (0 : ℝ) < 1 / (K + 1) by positivity),
    ev_rpow_neg_le (show 0 < γ / 2 by positivity) (show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity)]
    with n hn1 hnα hnγ R X Φ hRK hRdeg hres
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  set D := layerSlots m R with hDdef
  set τ : ℕ → ℕ := fun s => ⌈(n : ℝ) ^ (((r : ℝ) - s) * (1 - 2 * α))⌉₊ with hτdef
  have hτr : τ r = 1 := by simp [τ]
  have hτge : ∀ s : ℕ, (n : ℝ) ^ (((r : ℝ) - s) * (1 - 2 * α)) ≤ τ s := fun s => Nat.le_ceil _
  have hτle : ∀ s : ℕ, (τ s : ℝ) ≤ (n : ℝ) ^ (((r : ℝ) - s) * (1 - 2 * α)) + 1 := fun s =>
    (Nat.ceil_lt_add_one (by positivity)).le
  have hτ1 : ∀ s ≤ r, 1 ≤ τ s := fun s _ =>
    Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hn0 _)).ne'
  have hDr : ∀ d ∈ D, d.2.card = r := by
    intro d hd
    obtain ⟨h1, h2⟩ := mem_layerSlots.1 hd
    exact (mem_powersetCard.1 (hRK d.1 h1 h2)).2
  have hdegD : ∀ T : Finset (Fin n), T.card < r →
      (slotDeg D T : ℝ) ≤ (n : ℝ) ^ (((r : ℝ) - T.card) * (1 - 2 * α)) := by
    intro T hT
    have h1 : (slotDeg D T : ℝ) ≤ ∑ j ∈ range m, (deg (R j) T : ℝ) := by
      exact_mod_cast slotDeg_layerSlots_le m R T
    have h2 : ∀ j ∈ range m, (deg (R j) T : ℝ) ≤ (n : ℝ) ^ (r - 1 - T.card) * (n : ℝ) ^ (1 - γ) :=
      fun j hj => deg_le_pow_mul_of_maxDeg (fun e he => (mem_powersetCard.1
        (hRK j (mem_range.1 hj) he)).2) (by positivity) (hRdeg j (mem_range.1 hj)) T hT
    have h3 : (n : ℝ) ^ (r - 1 - T.card) * (n : ℝ) ^ (1 - γ) =
        (n : ℝ) ^ (-(γ / 2)) * (n : ℝ) ^ (((r : ℝ) - T.card) - γ / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
      congr 1
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have h4 : (m : ℝ) * (n : ℝ) ^ (-(γ / 2)) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hnγ (show (0 : ℝ) ≤ m by positivity)
      refine this.trans ?_
      rw [mul_one_div, div_le_one (by positivity)]; linarith
    have h5 : (n : ℝ) ^ (((r : ℝ) - T.card) - γ / 2) ≤
        (n : ℝ) ^ (((r : ℝ) - T.card) * (1 - 2 * α)) := by
      apply Real.rpow_le_rpow_of_exponent_le hn
      have : 2 * α * ((r : ℝ) - T.card) ≤ 2 * α * r := by
        have : (0 : ℝ) ≤ T.card := by positivity
        nlinarith
      nlinarith
    calc (slotDeg D T : ℝ) ≤ ∑ j ∈ range m, (deg (R j) T : ℝ) := h1
      _ ≤ ∑ j ∈ range m, (n : ℝ) ^ (r - 1 - T.card) * (n : ℝ) ^ (1 - γ) := sum_le_sum h2
      _ = (m : ℝ) * (n : ℝ) ^ (-(γ / 2)) * (n : ℝ) ^ (((r : ℝ) - T.card) - γ / 2) := by
          rw [sum_const, card_range, nsmul_eq_mul, h3]; ring
      _ ≤ 1 * (n : ℝ) ^ (((r : ℝ) - T.card) - γ / 2) := by gcongr
      _ ≤ _ := by rw [one_mul]; exact h5
  have key : ∀ D' ⊆ D, ∃ P, SlotInv q r X Φ D' τ P := by
    intro D'
    induction D' using Finset.induction_on with
    | empty => exact fun _ => ⟨∅, slotInv_empty q r X Φ τ⟩
    | insert d D' hdD ih =>
      intro hsub
      obtain ⟨P, hP⟩ := ih ((subset_insert _ _).trans hsub)
      have hdD0 : d ∈ D := hsub (mem_insert_self _ _)
      have he : d.2.card = r := hDr d hdD0
      have hc : ∀ T : Finset (Fin n), T.card < r →
          (cliqueMult P T : ℝ) ≤ 3 * (n : ℝ) ^ (((r : ℝ) - T.card) * (1 - 2 * α)) := by
        intro T hT
        have h1 : (cliqueMult P T : ℝ) ≤ slotDeg D' T + τ T.card := by
          exact_mod_cast hP.load T hT
        have h2 : (slotDeg D' T : ℝ) ≤ slotDeg D T := by
          exact_mod_cast slotDeg_mono ((subset_insert _ _).trans hsub) T
        have h3 : (1 : ℝ) ≤ (n : ℝ) ^ (((r : ℝ) - T.card) * (1 - 2 * α)) := by
          apply Real.one_le_rpow hn
          apply mul_nonneg _ hθ
          have : (T.card : ℝ) < r := by exact_mod_cast hT
          linarith
        linarith [hdegD T hT, hτle T.card]
      have hbad := card_bad_le (X := X) hτ1 hP.card_eq he (by omega)
      have hsum : (∑ T ∈ d.2.powerset, ∑ s ∈ range (r + 1),
          if T.card < s then
            (2 ^ q * (cliqueMult P T : ℝ) / τ s) * ((n : ℝ) ^ q / (n : ℝ) ^ (r + s - T.card))
          else 0) ≤ K * (n : ℝ) ^ ((q : ℝ) - r - 2 * α) := by
        have hterm : ∀ T ∈ d.2.powerset, ∀ s ∈ range (r + 1),
            (if T.card < s then
              (2 ^ q * (cliqueMult P T : ℝ) / τ s) * ((n : ℝ) ^ q / (n : ℝ) ^ (r + s - T.card))
            else 0) ≤ 3 * 2 ^ q * (n : ℝ) ^ ((q : ℝ) - r - 2 * α) := by
          intro T hT s hs
          have hs' : s ≤ r := Nat.lt_succ_iff.1 (mem_range.1 hs)
          split_ifs with hts
          · exact bad_term_le hα.le hts hn (hc T (by omega)) (hτge s)
          · positivity
        calc _ ≤ ∑ T ∈ d.2.powerset, ∑ s ∈ range (r + 1),
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
      have hex : ∃ Q ∈ reserveCliques q r X d.2 \ Φ, ¬ ∃ S ⊆ Q, S.card ≤ r ∧ ¬ S ⊆ d.2 ∧
          τ S.card ≤ cliqueMult P S := by
        by_contra hcon
        push_neg at hcon
        have hsub' : (reserveCliques q r X d.2 \ Φ) ⊆
            (reserveCliques q r X d.2).filter (fun Q => ∃ S ⊆ Q, S.card ≤ r ∧
              ¬ S ⊆ d.2 ∧ τ S.card ≤ cliqueMult P S) := by
          intro Q hQ
          exact mem_filter.2 ⟨(mem_sdiff.1 hQ).1, hcon Q hQ⟩
        have hcard : (((reserveCliques q r X d.2 \ Φ).card : ℕ) : ℝ) ≤
            (((reserveCliques q r X d.2).filter (fun Q => ∃ S ⊆ Q, S.card ≤ r ∧
              ¬ S ⊆ d.2 ∧ τ S.card ≤ cliqueMult P S)).card : ℝ) := by
          exact_mod_cast card_le_card hsub'
        obtain ⟨h1, h2⟩ := mem_layerSlots.1 hdD0
        linarith [hres d.1 h1 d.2 h2]
      obtain ⟨Q, hQ, hgood⟩ := hex
      push_neg at hgood
      exact ⟨insert Q P, hP.insert hr hrq hτr hdD he hQ hgood⟩
  obtain ⟨P, hP⟩ := key D Subset.rfl
  refine ⟨P, hP.card_eq, hP.disj, fun T hT => ?_⟩
  have h1 := hP.lower T hT
  have h2 := hP.upper T hT
  rw [hDdef, slotCount_layerSlots] at h1 h2
  exact ⟨h1, h2⟩

end RefinedAbsorption
