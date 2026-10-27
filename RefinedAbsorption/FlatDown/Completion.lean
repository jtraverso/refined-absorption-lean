module
public import RefinedAbsorption.FlatDown.AntiEdge
public import RefinedAbsorption.GJW.Main

/-!
# Local integral decompositions and completions

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Theorem 3.2 of the survey, used to
lift link pieces).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

* `gjw_local`: a divisible labelled multigraph whose copies lie in a finset `A` with
  `|A| ≥ q + r` is an integer combination of `r`-uniform cliques on `q`-subsets of `A`
  (the theorem of Graver–Jurkat and Wilson, transferred to the subtype of `A`).
-/

@[expose] public section

namespace RefinedAbsorption.FlatDown

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.GJW

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- **Local Graver–Jurkat–Wilson.** -/
theorem gjw_local {q r : ℕ} (hr : r < q) (A : Finset V) (hA : q + r ≤ A.card)
    (lkE : E → Finset V) (W : Finset E) (hW : ∀ w ∈ W, lkE w ⊆ A ∧ (lkE w).card = r)
    (hdiv : MIsDivisible q r lkE W) :
    ∃ c : Finset V → ℤ, ∀ g : Finset V, ((W.filter fun w => lkE w = g).card : ℤ) =
      ∑ Q ∈ A.powersetCard q, c Q * (if g.card = r ∧ g ⊆ Q then 1 else 0) := by
  classical
  let p : V → Prop := fun v => v ∈ A
  let emb := Function.Embedding.subtype p
  let pull : Finset V → Finset {v // p v} := fun g => g.subtype p
  have hpull : ∀ g ⊆ A, (pull g).map emb = g := fun g hg => subtype_map_of_mem hg
  have hpull' : ∀ s : Finset {v // p v}, pull (s.map emb) = s := by
    intro s; ext x; simp [pull, emb]
  have hmapsub : ∀ s t : Finset {v // p v}, s.map emb ⊆ t.map emb ↔ s ⊆ t :=
    fun s t => map_subset_map
  let f' : Finset {v // p v} → ℤ := fun s => ((W.filter fun w => lkE w = s.map emb).card : ℤ)
  have hcardA : Fintype.card {v // p v} = A.card := Fintype.card_coe A
  have hwdeg : ∀ S', wdeg f' S' = (mdeg lkE W (S'.map emb) : ℤ) := by
    intro S'
    rw [wdeg, mdeg]
    rw [card_eq_sum_card_fiberwise (f := fun w => pull (lkE w))
      (t := univ.filter fun s => S' ⊆ s)]
    · push_cast
      refine sum_congr rfl fun s hs => ?_
      have hS's : S' ⊆ s := (mem_filter.1 hs).2
      simp only [f']
      congr 2
      ext w
      simp only [mem_filter]
      constructor
      · rintro ⟨hw, hwe⟩
        refine ⟨⟨hw, ?_⟩, ?_⟩
        · rw [hwe]; exact (hmapsub _ _).2 hS's
        · rw [hwe, hpull']
      · rintro ⟨⟨hw, -⟩, hwe⟩
        refine ⟨hw, ?_⟩
        rw [← hwe, hpull _ (hW w hw).1]
    · intro w hw
      obtain ⟨hw, hS⟩ := mem_filter.1 hw
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      rw [← hmapsub, hpull _ (hW w hw).1]; exact hS
  have hWD : WDiv q r f' := by
    refine ⟨fun s hs => ?_, fun S' hS' => ?_⟩
    · obtain ⟨w, hw⟩ : (W.filter fun w => lkE w = s.map emb).Nonempty := by
        rw [nonempty_iff_ne_empty]; intro h; apply hs; simp [f', h]
      obtain ⟨hw, hwe⟩ := mem_filter.1 hw
      have := (hW w hw).2
      rw [hwe, card_map] at this; exact this
    · rw [hwdeg]
      have := hdiv (S'.map emb) (by rw [card_map]; exact hS')
      rw [card_map] at this
      exact_mod_cast this
  have hmem := wdiv_mem_Lam r hr (by rw [hcardA]; exact hA) f' hWD
  rw [Lam, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c', hc'⟩ := hmem
  refine ⟨fun Q => if h : Q ⊆ A ∧ Q.card = q then
    c' ⟨pull Q, by rw [← card_map emb, hpull Q h.1]; exact h.2⟩ else 0, fun g => ?_⟩
  by_cases hg : g ⊆ A
  · have hL : ((W.filter fun w => lkE w = g).card : ℤ) = f' (pull g) := by
      simp only [f', hpull g hg]
    rw [hL, ← hc', Finset.sum_apply]
    refine sum_bij (fun Q _ => Q.1.map emb) ?_ ?_ ?_ ?_
    · intro Q _
      rw [mem_powersetCard, card_map]
      exact ⟨fun v hv => by
        obtain ⟨x, -, rfl⟩ := mem_map.1 hv; exact x.2, Q.2⟩
    · intro Q _ Q' _ h
      exact Subtype.ext (map_injective emb h)
    · intro Q hQ
      obtain ⟨hQA, hQc⟩ := mem_powersetCard.1 hQ
      refine ⟨⟨pull Q, by rw [← card_map emb, hpull Q hQA]; exact hQc⟩, mem_univ _, ?_⟩
      exact hpull Q hQA
    · intro Q _
      have hQA : Q.1.map emb ⊆ A := fun v hv => by
        obtain ⟨x, -, rfl⟩ := mem_map.1 hv; exact x.2
      have hQc : (Q.1.map emb).card = q := by rw [card_map]; exact Q.2
      simp only [Pi.smul_apply, smul_eq_mul, clq, dif_pos (And.intro hQA hQc)]
      have hc : c' ⟨pull (Q.1.map emb), by rw [← card_map emb, hpull _ hQA]; exact hQc⟩ =
          c' Q := by congr 1; exact Subtype.ext (hpull' Q.1)
      rw [hc]
      congr 1
      have h1 : (pull g).card = g.card := by rw [← card_map emb, hpull g hg]
      have h2 : pull g ⊆ Q.1 ↔ g ⊆ Q.1.map emb := by
        rw [← hmapsub, hpull g hg]
      simp only [h1, h2]
  · have hL : (W.filter fun w => lkE w = g) = ∅ := by
      rw [filter_eq_empty_iff]
      intro w hw hwe
      exact hg (hwe ▸ (hW w hw).1)
    rw [hL, card_empty, Nat.cast_zero]
    symm
    refine sum_eq_zero fun Q hQ => ?_
    have : ¬ (g.card = r ∧ g ⊆ Q) := fun h => hg (h.2.trans (mem_powersetCard.1 hQ).1)
    simp [this]

/-- The completion of `T * Q`: the edges of the clique on `T ∪ Q` that do not contain `T`. -/
def compE (r : ℕ) (T Q : Finset V) : Finset (Finset V) :=
  ((T ∪ Q).powersetCard r).filter fun e => ¬ T ⊆ e

/-- The nonnegative representative of `c` modulo `M`. -/
def resMod (M : ℕ) (c : ℤ) : ℕ := (c % (M : ℤ)).toNat

theorem resMod_modEq {M : ℕ} (hM : 0 < M) (c : ℤ) : (M : ℤ) ∣ (resMod M c : ℤ) - c := by
  have h0 : 0 ≤ c % (M : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hM.ne')
  rw [resMod, Int.toNat_of_nonneg h0, Int.emod_def]
  exact ⟨-(c / M), by ring⟩

/-- The number of edges of the clique on `T ∪ Q` containing `T` and `S`. -/
theorem card_clique_contain_T {r : ℕ} {T Q S : Finset V} (hTQ : Disjoint T Q) (hTr : T.card ≤ r) :
    (((T ∪ Q).powersetCard r).filter fun e => T ⊆ e ∧ S ⊆ e).card =
      ((Q.powersetCard (r - T.card)).filter fun g => S ⊆ T ∪ g).card := by
  refine card_nbij' (fun e => e \ T) (fun g => T ∪ g) ?_ ?_ ?_ ?_
  · intro e he
    simp only [coe_filter, Set.mem_setOf_eq, mem_powersetCard] at he ⊢
    obtain ⟨⟨heTQ, her⟩, hTe, hSe⟩ := he
    refine ⟨⟨fun v hv => ?_, ?_⟩, ?_⟩
    · obtain ⟨hve, hvT⟩ := mem_sdiff.1 hv
      rcases mem_union.1 (heTQ hve) with h | h
      · exact absurd h hvT
      · exact h
    · rw [card_sdiff_of_subset hTe, her]
    · rw [union_sdiff_of_subset hTe]; exact hSe
  · intro g hg
    simp only [coe_filter, Set.mem_setOf_eq, mem_powersetCard] at hg ⊢
    obtain ⟨⟨hgQ, hgr⟩, hSg⟩ := hg
    refine ⟨⟨union_subset_union subset_rfl hgQ, ?_⟩, subset_union_left, hSg⟩
    rw [card_union_of_disjoint (disjoint_of_subset_right hgQ hTQ), hgr]; omega
  · intro e he
    simp only [coe_filter, Set.mem_setOf_eq] at he
    exact union_sdiff_of_subset he.2.1
  · intro g hg
    simp only [coe_filter, Set.mem_setOf_eq, mem_powersetCard] at hg
    exact union_sdiff_cancel_left (disjoint_of_subset_right hg.1.1 hTQ)

/-- **Divisibility of a completed lifted piece.**  If the link multigraph `W` (copies inside
`A`, disjoint from the `i`-set `T`) is the integer combination `∑ c_Q K_Q^{r-i}`, then lifting
`W` by `T` and adding `resMod M (c Q)` copies of the completion `compE r T Q` of every clique
gives a `K_q^r`-divisible multigraph. -/
theorem completion_dvd {E' : Type*} [DecidableEq E'] {q r i M : ℕ} (hir : i ≤ r)
    (hM : 0 < M) (hdvd : ∀ s < r, (q - s).choose (r - s) ∣ M)
    {T A : Finset V} (hTA : Disjoint T A) (hT : T.card = i)
    (lkE : E' → Finset V) (W : Finset E') (hW : ∀ w ∈ W, lkE w ⊆ A)
    (c : Finset V → ℤ) (hc : ∀ g : Finset V, ((W.filter fun w => lkE w = g).card : ℤ) =
      ∑ Q ∈ A.powersetCard (q - i), c Q * (if g.card = r - i ∧ g ⊆ Q then 1 else 0))
    (hq : r ≤ q) (S : Finset V) (hS : S.card < r) :
    (q - S.card).choose (r - S.card) ∣ (W.filter fun w => S ⊆ T ∪ lkE w).card +
      ∑ Q ∈ A.powersetCard (q - i),
        resMod M (c Q) * ((compE r T Q).filter fun e => S ⊆ e).card := by
  set b := (q - S.card).choose (r - S.card)
  -- t_Q, u_Q, d_Q
  set t : Finset V → ℕ := fun Q => ((Q.powersetCard (r - i)).filter fun g => S ⊆ T ∪ g).card
  set u : Finset V → ℕ := fun Q => ((compE r T Q).filter fun e => S ⊆ e).card
  have htud : ∀ Q ∈ A.powersetCard (q - i), (b : ℤ) ∣ (t Q + u Q : ℕ) := by
    intro Q hQ
    obtain ⟨hQA, hQc⟩ := mem_powersetCard.1 hQ
    have hTQ : Disjoint T Q := disjoint_of_subset_right hQA hTA
    have hsplit := card_filter_add_card_filter_not
      (s := ((T ∪ Q).powersetCard r).filter fun e => S ⊆ e) (fun e => T ⊆ e)
    rw [filter_filter, filter_filter] at hsplit
    have h1 : (((T ∪ Q).powersetCard r).filter fun e => S ⊆ e ∧ T ⊆ e).card = t Q := by
      have := card_clique_contain_T (S := S) (r := r) hTQ (by omega)
      rw [hT] at this
      show _ = ((Q.powersetCard (r - i)).filter fun g => S ⊆ T ∪ g).card
      rw [← this]
      congr 1; exact filter_congr fun e _ => and_comm
    have h2 : (((T ∪ Q).powersetCard r).filter fun e => S ⊆ e ∧ ¬ T ⊆ e).card = u Q := by
      simp only [u, compE, filter_filter]
      congr 1; exact filter_congr fun e _ => and_comm
    rw [h1, h2] at hsplit
    have hcl := dvd_deg_cliqueEdges (q := q) (r := r)
      (by rw [card_union_of_disjoint hTQ, hT, hQc]; omega : (T ∪ Q).card = q) hS.le
    rw [deg, cliqueEdges, ← hsplit] at hcl
    exact_mod_cast hcl
  -- the lifted part as a sum over cliques
  have hlift : ((W.filter fun w => S ⊆ T ∪ lkE w).card : ℤ) = ∑ Q ∈ A.powersetCard (q - i),
      c Q * (t Q : ℤ) := by
    have h1 : ((W.filter fun w => S ⊆ T ∪ lkE w).card : ℤ) =
        ∑ g ∈ A.powerset, ((W.filter fun w => lkE w = g).card : ℤ) *
          (if S ⊆ T ∪ g then 1 else 0) := by
      rw [card_eq_sum_card_fiberwise (f := lkE) (t := A.powerset)
        (fun w hw => mem_powerset.2 (hW w (mem_filter.1 hw).1))]
      push_cast
      refine sum_congr rfl fun g _ => ?_
      rw [filter_filter]
      split_ifs with h
      · rw [mul_one]; congr 2
        exact filter_congr fun w _ => ⟨fun h' => h'.2, fun h' => ⟨h' ▸ h, h'⟩⟩
      · rw [mul_zero]
        norm_cast
        rw [card_eq_zero, filter_eq_empty_iff]
        rintro w - ⟨h1, h2⟩
        exact h (h2 ▸ h1)
    rw [h1]
    simp_rw [hc, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun Q hQ => ?_
    have hQA := (mem_powersetCard.1 hQ).1
    simp_rw [mul_assoc, ← mul_sum]
    congr 1
    have hite : ∀ g ∈ A.powerset, ((if g.card = r - i ∧ g ⊆ Q then (1 : ℤ) else 0) *
        if S ⊆ T ∪ g then 1 else 0) = if (g.card = r - i ∧ g ⊆ Q) ∧ S ⊆ T ∪ g then 1 else 0 := by
      intro g _; split_ifs <;> simp_all
    rw [sum_congr rfl hite, sum_boole]
    norm_cast
    congr 1
    ext g
    simp only [mem_filter, mem_powerset, mem_powersetCard]
    constructor
    · rintro ⟨-, ⟨hgr, hgQ⟩, hS'⟩; exact ⟨⟨hgQ, hgr⟩, hS'⟩
    · rintro ⟨⟨hgQ, hgr⟩, hS'⟩; exact ⟨hgQ.trans hQA, ⟨hgr, hgQ⟩, hS'⟩
  -- conclude in ℤ
  have hfin : (b : ℤ) ∣ ((W.filter fun w => S ⊆ T ∪ lkE w).card : ℤ) +
      ∑ Q ∈ A.powersetCard (q - i), (resMod M (c Q) : ℤ) * (u Q : ℤ) := by
    rw [hlift]
    have : ∑ Q ∈ A.powersetCard (q - i), c Q * (t Q : ℤ) +
        ∑ Q ∈ A.powersetCard (q - i), (resMod M (c Q) : ℤ) * (u Q : ℤ) =
        ∑ Q ∈ A.powersetCard (q - i), c Q * ((t Q + u Q : ℕ) : ℤ) +
        ∑ Q ∈ A.powersetCard (q - i), ((resMod M (c Q) : ℤ) - c Q) * (u Q : ℤ) := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun Q _ => ?_
      push_cast; ring
    rw [this]
    refine dvd_add (dvd_sum fun Q hQ => Dvd.dvd.mul_left (htud Q hQ) _)
      (dvd_sum fun Q _ => Dvd.dvd.mul_right ?_ _)
    exact (Int.natCast_dvd_natCast.2 (hdvd _ hS)).trans (resMod_modEq hM _)
  have : ((((W.filter fun w => S ⊆ T ∪ lkE w).card + ∑ Q ∈ A.powersetCard (q - i),
      resMod M (c Q) * u Q : ℕ)) : ℤ) = ((W.filter fun w => S ⊆ T ∪ lkE w).card : ℤ) +
      ∑ Q ∈ A.powersetCard (q - i), (resMod M (c Q) : ℤ) * (u Q : ℤ) := by push_cast; ring
  rw [← this] at hfin
  exact Int.natCast_dvd_natCast.1 hfin

end RefinedAbsorption.FlatDown
