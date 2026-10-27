module
public import RequestProject.Placement.Inner

/-!
# Clustered placement: one gadget, vertex by vertex

The clustered version of the Partial Clique Embedding Lemma also controls the vertex sets of
*pieces*: a piece `p` has a base vertex set and a set `Mem p` of member gadgets, and its current
vertex set is the base together with the auxiliary images of its placed members.  We cap the
*piece loads* `pload P pv T = #{p ∈ P : T ⊆ pv p}` by `μ^|T| · D · n^(r-1-|T|)`.  This is the
refinement-degree invariant needed to place absorbers on the pieces afterwards.

`clusterInv_step` adds one auxiliary vertex of the gadget `i` being placed.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset

variable {n h : ℕ} {ι κ : Type*}

/-- Piece load: the number of pieces whose current vertex set contains `T`. -/
def pload (P : Finset κ) (pv : κ → Finset (Fin n)) (T : Finset (Fin n)) : ℕ :=
  (P.filter fun p => T ⊆ pv p).card

/-- The current piece vertex sets while the gadget `i` is being placed (positions `A`). -/
def pvAt [DecidableEq ι] (Mem : κ → Finset ι) (i : ι) (pv₀ : κ → Finset (Fin n))
    (A : Finset (Fin h)) (φ : Fin h → Fin n) : κ → Finset (Fin n) :=
  fun p => if i ∈ Mem p then pv₀ p ∪ A.image φ else pv₀ p

/-- The invariant of the clustered inner placement. -/
structure ClusterInv [DecidableEq ι] (r μ D : ℕ) (P : Finset κ) (Mem : κ → Finset ι) (i : ι)
    (pv₀ : κ → Finset (Fin n)) (R : Finset (Fin n)) (T : Finset (Finset (Fin n ⊕ Fin h)))
    (F : Finset (Finset (Fin n))) (A : Finset (Fin h)) (φ : Fin h → Fin n) : Prop where
  inj : Set.InjOn φ A
  avoid : ∀ p ∈ A, φ p ∉ R
  loads : ∀ U : Finset (Fin n), U.card ≤ r - 1 →
    pload P (pvAt Mem i pv₀ A φ) U ≤ cap r μ D n ∅ U.card
  edges : ∀ t ∈ T, (∀ p, Sum.inr p ∈ t → p ∈ A) → placeEdge φ t ∉ F

theorem sum_pload_insert_le (P : Finset κ) (pv : κ → Finset (Fin n)) (Pmax : ℕ)
    (hP : ∀ p ∈ P, (pv p).card ≤ Pmax) (U : Finset (Fin n)) :
    ∑ v ∈ univ \ U, pload P pv (insert v U) ≤ Pmax * pload P pv U := by
  classical
  unfold pload
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro p hp
  by_cases hU : U ⊆ pv p
  · rw [if_pos hU, mul_one]
    calc ∑ v ∈ univ \ U, (if insert v U ⊆ pv p then 1 else 0)
        ≤ ∑ v ∈ univ \ U, (if v ∈ pv p then 1 else 0) := by
          apply sum_le_sum; intro v _
          split_ifs with h1 h2 <;> simp_all [insert_subset_iff]
      _ ≤ ∑ v, (if v ∈ pv p then 1 else 0) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
      _ = (pv p).card := by rw [← sum_filter, ← card_eq_sum_ones]; simp
      _ ≤ Pmax := hP p hp
  · rw [if_neg hU, mul_zero]
    apply le_of_eq
    apply sum_eq_zero
    intro v _
    rw [if_neg]
    intro h
    exact hU ((subset_insert v U).trans h)

/-- Few vertices push a piece load to within `m` of its cap. -/
theorem card_pheavy_le {r μ D : ℕ} (P : Finset κ) (pv : κ → Finset (Fin n)) (Pmax m : ℕ)
    (hP : ∀ p ∈ P, (pv p).card ≤ Pmax) (U : Finset (Fin n)) (hU : U.card + 1 ≤ r - 1)
    (hD : 0 < D) (hn : 0 < n) (hμ : 2 * m ≤ μ) (hμ0 : 0 < μ)
    (hload : pload P pv U ≤ cap r μ D n ∅ U.card) :
    ((univ \ U).filter fun v =>
        cap r μ D n ∅ (U.card + 1) < pload P pv (insert v U) + m).card * μ ≤ 2 * Pmax * n := by
  set c := cap r μ D n ∅ (U.card + 1)
  set bad := (univ \ U).filter fun v => c < pload P pv (insert v U) + m
  have he : r - 1 - (∅ : Finset (Fin n)).card - U.card =
      (r - 1 - (∅ : Finset (Fin n)).card - (U.card + 1)) + 1 := by simp; omega
  set e := r - 1 - (∅ : Finset (Fin n)).card - (U.card + 1)
  have hX : 0 < μ ^ U.card * D * n ^ e := by positivity
  have hc : c = μ * (μ ^ U.card * D * n ^ e) := by
    simp only [c, cap]; ring
  have hcU : cap r μ D n ∅ U.card = n * (μ ^ U.card * D * n ^ e) := by
    simp only [cap]; rw [he]; ring
  have hcm : 2 * m ≤ c := by
    rw [hc]
    calc 2 * m ≤ μ := hμ
      _ = μ * 1 := (mul_one _).symm
      _ ≤ μ * (μ ^ U.card * D * n ^ e) := Nat.mul_le_mul_left _ hX
  have key : bad.card * c ≤ 2 * (Pmax * pload P pv U) := by
    calc bad.card * c = ∑ _v ∈ bad, c := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ bad, 2 * pload P pv (insert v U) := by
          apply sum_le_sum
          intro v hv
          have := (mem_filter.1 hv).2
          omega
      _ = 2 * ∑ v ∈ bad, pload P pv (insert v U) := (mul_sum _ _ _).symm
      _ ≤ 2 * ∑ v ∈ univ \ U, pload P pv (insert v U) :=
          Nat.mul_le_mul_left _ (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _))
      _ ≤ 2 * (Pmax * pload P pv U) :=
          Nat.mul_le_mul_left _ (sum_pload_insert_le P pv Pmax hP U)
  have : bad.card * μ * (μ ^ U.card * D * n ^ e) ≤ 2 * Pmax * n * (μ ^ U.card * D * n ^ e) := by
    calc bad.card * μ * (μ ^ U.card * D * n ^ e) = bad.card * c := by rw [hc]; ring
      _ ≤ 2 * (Pmax * pload P pv U) := key
      _ ≤ 2 * (Pmax * (n * (μ ^ U.card * D * n ^ e))) := by
          rw [← hcU]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hload)
      _ = 2 * Pmax * n * (μ ^ U.card * D * n ^ e) := by ring
  exact Nat.le_of_mul_le_mul_right this hX

theorem pvAt_insert_update [DecidableEq ι] (Mem : κ → Finset ι) (i : ι)
    (pv₀ : κ → Finset (Fin n)) {A : Finset (Fin h)} {p : Fin h} (hp : p ∉ A)
    (φ : Fin h → Fin n) (v : Fin n) (q : κ) :
    pvAt Mem i pv₀ (insert p A) (Function.update φ p v) q =
      if i ∈ Mem q then insert v (pvAt Mem i pv₀ A φ q) else pvAt Mem i pv₀ A φ q := by
  unfold pvAt
  split_ifs with hq
  · rw [image_update_of_mem (mem_insert_self p A), erase_insert hp]
    ext x; simp only [mem_union, mem_insert]; tauto
  · rfl

/-- **One step of the clustered inner placement.** -/
theorem clusterInv_step [DecidableEq ι] {r k μ D Fdeg m Pmax : ℕ} (P : Finset κ)
    (Mem : κ → Finset ι) (i : ι) (pv₀ : κ → Finset (Fin n)) (R : Finset (Fin n))
    (T : Finset (Finset (Fin n ⊕ Fin h))) (hw : GadgetWF r k R T) (F : Finset (Finset (Fin n)))
    (hmem : (P.filter fun q => i ∈ Mem q).card ≤ m)
    (hsize : ∀ q ∈ P, (pv₀ q).card + h ≤ Pmax)
    (hF : ∀ B : Finset (Fin n), B.card = r - 1 → deg F B ≤ Fdeg)
    (hD : 0 < D) (hμ0 : 0 < μ) (hμ : 2 * m ≤ μ) (hμ2 : 8 * (m * 2 ^ Pmax) * Pmax ≤ μ)
    (hnum : 4 * (k + h + 2 ^ (k + h) * Fdeg) < 3 * n)
    {A : Finset (Fin h)} {φ : Fin h → Fin n}
    (hinv : ClusterInv r μ D P Mem i pv₀ R T F A φ) {p : Fin h} (hp : p ∉ A) :
    ∃ v, ClusterInv r μ D P Mem i pv₀ R T F (insert p A) (Function.update φ p v) := by
  classical
  have hn : 0 < n := by omega
  have hh : 0 < h := Fin.pos p
  have hM : 0 < 2 ^ (k + h) := by positivity
  set pv := pvAt Mem i pv₀ A φ with hpvdef
  have hA : A.card ≤ h := card_le_univ A |>.trans (by simp)
  have hpvP : ∀ q ∈ P, (pv q).card ≤ Pmax := by
    intro q hq
    simp only [pv, pvAt]
    split_ifs
    · have h1 := hsize q hq
      have h2 : (A.image φ).card ≤ h := card_image_le.trans hA
      exact (card_union_le _ _).trans (by omega)
    · have := hsize q hq; omega
  -- the three kinds of excluded vertices
  set Bad1 : Finset (Fin n) := R ∪ A.image φ
  set badU : Finset (Fin n) → Finset (Fin n) := fun U => (univ \ U).filter fun v =>
    cap r μ D n ∅ (U.card + 1) < pload P pv (insert v U) + m
  set Pi := P.filter fun q => i ∈ Mem q
  set Bad2 : Finset (Fin n) := Pi.biUnion fun q =>
    ((pv q).powerset.filter fun U => U.card + 1 ≤ r - 1).biUnion badU
  set edgesP := T.filter (fun t => Sum.inr p ∈ t ∧ ∀ q, Sum.inr q ∈ t → q ∈ insert p A)
  set Bad3 : Finset (Fin n) := edgesP.biUnion (fun t => univ.filter (fun v =>
    v ∉ placeEdge φ (t.erase (Sum.inr p)) ∧ insert v (placeEdge φ (t.erase (Sum.inr p))) ∈ F))
  have h1 : Bad1.card ≤ k + h :=
    (card_union_le _ _).trans (Nat.add_le_add hw.roots_le (card_image_le.trans hA))
  have hbadU : ∀ q ∈ Pi, ∀ U ∈ (pv q).powerset.filter (fun U => U.card + 1 ≤ r - 1),
      (badU U).card * μ ≤ 2 * Pmax * n := by
    intro q hq U hU
    rw [mem_filter, mem_powerset] at hU
    exact card_pheavy_le P pv Pmax m hpvP U hU.2 hD hn hμ hμ0
      (hinv.loads U (by omega))
  have h2 : 4 * Bad2.card ≤ n := by
    have hsum : Bad2.card * μ ≤ (m * 2 ^ Pmax) * (2 * Pmax * n) := by
      calc Bad2.card * μ ≤ (∑ q ∈ Pi, ∑ U ∈ (pv q).powerset.filter
            (fun U => U.card + 1 ≤ r - 1), (badU U).card) * μ := by
            apply Nat.mul_le_mul_right
            refine card_biUnion_le.trans (sum_le_sum fun q _ => card_biUnion_le)
        _ = ∑ q ∈ Pi, ∑ U ∈ (pv q).powerset.filter
            (fun U => U.card + 1 ≤ r - 1), (badU U).card * μ := by
            rw [sum_mul]; exact sum_congr rfl fun q _ => sum_mul _ _ _
        _ ≤ ∑ q ∈ Pi, ∑ _U ∈ (pv q).powerset.filter
            (fun U => U.card + 1 ≤ r - 1), 2 * Pmax * n :=
            sum_le_sum fun q hq => sum_le_sum fun U hU => hbadU q hq U hU
        _ ≤ ∑ _q ∈ Pi, 2 ^ Pmax * (2 * Pmax * n) := by
            apply sum_le_sum
            intro q hq
            rw [sum_const, smul_eq_mul]
            apply Nat.mul_le_mul_right
            refine (card_filter_le _ _).trans ?_
            rw [card_powerset]
            exact Nat.pow_le_pow_right (by norm_num) (hpvP q (mem_filter.1 hq).1)
        _ = Pi.card * (2 ^ Pmax * (2 * Pmax * n)) := by rw [sum_const, smul_eq_mul]
        _ ≤ m * (2 ^ Pmax * (2 * Pmax * n)) := Nat.mul_le_mul_right _ hmem
        _ = (m * 2 ^ Pmax) * (2 * Pmax * n) := by ring
    set X := m * 2 ^ Pmax * Pmax
    rcases Nat.eq_zero_or_pos X with hX | hX
    · have : Bad2.card * μ ≤ 0 := by
        calc Bad2.card * μ ≤ (m * 2 ^ Pmax) * (2 * Pmax * n) := hsum
          _ = 2 * n * X := by simp only [X]; ring
          _ = 0 := by rw [hX, mul_zero]
      have : Bad2.card = 0 := by
        rcases Nat.eq_zero_or_pos Bad2.card with h0 | h0
        · exact h0
        · exact absurd this (Nat.not_le.2 (Nat.mul_pos h0 hμ0))
      omega
    · have : 4 * Bad2.card * (2 * X) ≤ n * (2 * X) := by
        calc 4 * Bad2.card * (2 * X) = Bad2.card * (8 * X) := by ring
          _ ≤ Bad2.card * μ := Nat.mul_le_mul_left _ (by simpa [X, mul_assoc] using hμ2)
          _ ≤ (m * 2 ^ Pmax) * (2 * Pmax * n) := hsum
          _ = n * (2 * X) := by simp only [X]; ring
      exact Nat.le_of_mul_le_mul_right this (by omega)
  have h3 : Bad3.card ≤ 2 ^ (k + h) * Fdeg := by
    calc Bad3.card ≤ ∑ t ∈ edgesP, (univ.filter (fun v =>
          v ∉ placeEdge φ (t.erase (Sum.inr p)) ∧
            insert v (placeEdge φ (t.erase (Sum.inr p))) ∈ F)).card := card_biUnion_le
      _ ≤ ∑ _t ∈ edgesP, Fdeg := by
          apply sum_le_sum
          intro t ht
          simp only [edgesP, mem_filter] at ht
          obtain ⟨htT, hpt, haux⟩ := ht
          refine (card_forbidden_le F _).trans (hF _ ?_)
          unfold placeEdge
          rw [card_image_of_injOn, card_erase_of_mem hpt, hw.edge_card t htT]
          apply emb_injOn φ A hinv.inj hinv.avoid
          · intro a ha; exact hw.edge_roots t htT a (mem_of_mem_erase ha)
          · intro q hq
            have hqp : q ≠ p := fun h => by subst h; simp at hq
            rcases mem_insert.1 (haux q (mem_of_mem_erase hq)) with h | h
            · exact absurd h hqp
            · exact h
      _ = edgesP.card * Fdeg := by rw [sum_const, smul_eq_mul]
      _ ≤ 2 ^ (k + h) * Fdeg :=
          Nat.mul_le_mul_right _ ((card_filter_le _ _).trans (card_template_le hw))
  have hlt : (Bad1 ∪ Bad2 ∪ Bad3).card < (univ : Finset (Fin n)).card := by
    rw [card_univ, Fintype.card_fin]
    have := card_union_le (Bad1 ∪ Bad2) Bad3
    have := card_union_le Bad1 Bad2
    omega
  obtain ⟨v, -, hv⟩ := exists_mem_notMem_of_card_lt_card hlt
  simp only [mem_union, not_or] at hv
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := hv
  have hvR : v ∉ R := fun h => hv1 (mem_union_left _ h)
  have hvA : ∀ q ∈ A, φ q ≠ v := fun q hq h => hv1 (mem_union_right _ (h ▸ mem_image_of_mem φ hq))
  have hφ' : ∀ q ∈ A, Function.update φ p v q = φ q := fun q hq =>
    Function.update_of_ne (by rintro rfl; exact hp hq) _ _
  refine ⟨v, ⟨?_, ?_, ?_, ?_⟩⟩
  · -- injectivity
    rw [coe_insert]
    refine (Set.injOn_insert (by simpa using hp)).2 ⟨?_, ?_⟩
    · intro a ha b hb hab
      rw [hφ' a ha, hφ' b hb] at hab
      exact hinv.inj ha hb hab
    · rintro ⟨q, hq, hqv⟩
      rw [Function.update_self, hφ' q hq] at hqv
      exact hvA q hq hqv
  · -- avoiding roots
    intro q hq
    rcases mem_insert.1 hq with rfl | hq
    · rw [Function.update_self]; exact hvR
    · rw [hφ' q hq]; exact hinv.avoid q hq
  · -- piece loads
    intro U hU
    have hpv' : pvAt Mem i pv₀ (insert p A) (Function.update φ p v) =
        fun q => if i ∈ Mem q then insert v (pv q) else pv q := by
      funext q; exact pvAt_insert_update Mem i pv₀ hp φ v q
    rw [hpv']
    set extra := Pi.filter fun q => U ⊆ insert v (pv q) ∧ ¬ U ⊆ pv q
    have hsplit : pload P (fun q => if i ∈ Mem q then insert v (pv q) else pv q) U ≤
        pload P pv U + extra.card := by
      unfold pload
      refine (card_le_card ?_).trans (card_union_le _ _)
      intro q hq
      rw [mem_filter] at hq
      by_cases hU' : U ⊆ pv q
      · exact mem_union_left _ (mem_filter.2 ⟨hq.1, hU'⟩)
      · apply mem_union_right
        simp only at hq
        split_ifs at hq with hiq
        · exact mem_filter.2 ⟨mem_filter.2 ⟨hq.1, hiq⟩, hq.2, hU'⟩
        · exact absurd hq.2 hU'
    rcases extra.eq_empty_or_nonempty with hE | ⟨q₀, hq₀⟩
    · rw [hE, card_empty, add_zero] at hsplit
      exact hsplit.trans (hinv.loads U hU)
    · obtain ⟨hq₀P, hUq₀, hnU⟩ := mem_filter.1 hq₀
      have hvU : v ∈ U := by
        by_contra hvU
        exact hnU (fun x hx => (mem_insert.1 (hUq₀ hx)).resolve_left
          (by rintro rfl; exact hvU hx))
      set U₁ := U.erase v
      have hU₁ : U₁ ⊆ pv q₀ := by
        intro x hx
        exact (mem_insert.1 (hUq₀ (mem_of_mem_erase hx))).resolve_left (ne_of_mem_erase hx)
      have hcard : U₁.card + 1 = U.card := card_erase_add_one hvU
      have hmemU : U₁ ∈ (pv q₀).powerset.filter (fun U => U.card + 1 ≤ r - 1) :=
        mem_filter.2 ⟨mem_powerset.2 hU₁, by omega⟩
      have hv2' : v ∉ badU U₁ := fun h =>
        hv2 (mem_biUnion.2 ⟨q₀, hq₀P, mem_biUnion.2 ⟨U₁, hmemU, h⟩⟩)
      have hvU₁ : v ∉ U₁ := notMem_erase v U
      have hins : insert v U₁ = U := insert_erase hvU
      have hnb : ¬ cap r μ D n ∅ (U₁.card + 1) < pload P pv (insert v U₁) + m := by
        intro h
        exact hv2' (mem_filter.2 ⟨mem_sdiff.2 ⟨mem_univ _, hvU₁⟩, h⟩)
      rw [hins, hcard] at hnb
      have hex : extra.card ≤ m := (card_le_card (filter_subset _ _)).trans hmem
      omega
  · -- edges
    intro t ht haux
    by_cases hpt : Sum.inr p ∈ t
    · rw [placeEdge_update_of_mem hpt]
      have hmem : t ∈ edgesP := mem_filter.2 ⟨ht, hpt, haux⟩
      have hvB : v ∉ placeEdge φ (t.erase (Sum.inr p)) := by
        intro hvB
        simp only [placeEdge, mem_image] at hvB
        obtain ⟨x, hx, hxv⟩ := hvB
        rcases x with a | q
        · exact hvR (hxv ▸ hw.edge_roots t ht a (mem_of_mem_erase hx))
        · have hqp : q ≠ p := fun h => by subst h; simp at hx
          rcases mem_insert.1 (haux q (mem_of_mem_erase hx)) with h | h
          · exact hqp h
          · exact hvA q h hxv
      intro hF'
      exact hv3 (mem_biUnion.2 ⟨t, hmem, mem_filter.2 ⟨mem_univ _, hvB, hF'⟩⟩)
    · rw [placeEdge_update_of_not_mem hpt]
      apply hinv.edges t ht
      intro q hq
      rcases mem_insert.1 (haux q hq) with h | h
      · exact absurd (h ▸ hq) hpt
      · exact h

end RefinedAbsorption.Placement
