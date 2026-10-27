module
public import RefinedAbsorption.Placement.ReserveLemma52
public import RefinedAbsorption.FlatOmni.CliquePieces

/-!
# The Partial Clique Embedding Lemma with several root sets per gadget

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Lemma 5.2, in the form needed to embed
fake edges whose pieces must stay sparse.  Lean formalization: Juan Pablo Traverso Gianini,
Apache-2.0.

Every gadget `i` has its template `T i` rooted at its core roots `Rc i`, and in addition a family
`𝓡 i` of at most `m` *tracked root sets* (containing `Rc i`), each of at most `k` vertices.  If
the family of all pairs `(i, R)`, `R ∈ 𝓡 i`, is not too dense compared to the reserve `Z`, the
gadgets can be placed inside `Z` exactly as in `reserveCliqueEmbedding`, and moreover every
`(r-1)`-set `S` lies in `R ∪ Φ i (Fin h)` for at most `C · D` pairs `(i, R)`
(**`reserveMultiRootEmbedding`**).

The proof is the greedy placement of `ReserveLemma52.lean`, with the loads counted over pairs
(`mload`); the inner placement of one gadget is run with all its tracked root sets at once.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.Placement

variable {n h : ℕ} {ι : Type*} [DecidableEq ι]

/-- The mixed load counted over the pairs `(i, R)` with `R ∈ 𝓡 i`. -/
def mload (𝓡 : ι → Finset (Finset (Fin n))) (Φ : ι → Fin h → Fin n) (s : Finset ι)
    (J U : Finset (Fin n)) : ℕ :=
  ∑ i ∈ s, ((𝓡 i).filter fun R => J ⊆ R ∧ U ⊆ auxImage (Φ i)).card

/-- The load of the pair family, as a load of a gadget family indexed by pairs. -/
theorem mload_eq_load (𝓡 : ι → Finset (Finset (Fin n))) (Φ : ι → Fin h → Fin n) (s : Finset ι)
    (J U : Finset (Fin n)) :
    mload 𝓡 Φ s J U =
      load (fun p : (Σ _ : ι, Finset (Fin n)) => p.2) (fun p => Φ p.1) (s.sigma 𝓡) J U := by
  unfold mload load
  rw [RefinedAbsorption.FlatOmni.card_filter_sigma]

theorem mload_congr {𝓡 : ι → Finset (Finset (Fin n))} {Φ Ψ : ι → Fin h → Fin n} {s : Finset ι}
    (hΦ : ∀ j ∈ s, Φ j = Ψ j) (J U : Finset (Fin n)) : mload 𝓡 Φ s J U = mload 𝓡 Ψ s J U := by
  unfold mload
  exact sum_congr rfl fun j hj => by rw [hΦ j hj]

theorem mload_insert {𝓡 : ι → Finset (Finset (Fin n))} {Φ : ι → Fin h → Fin n} {s : Finset ι}
    {i : ι} (hi : i ∉ s) (J U : Finset (Fin n)) :
    mload 𝓡 Φ (insert i s) J U =
      mload 𝓡 Φ s J U + ((𝓡 i).filter fun R => J ⊆ R ∧ U ⊆ auxImage (Φ i)).card := by
  unfold mload
  rw [sum_insert hi, add_comm]

theorem mload_le_root {𝓡 : ι → Finset (Finset (Fin n))} {Φ : ι → Fin h → Fin n} {s I : Finset ι}
    (hsI : s ⊆ I) (J U : Finset (Fin n)) :
    mload 𝓡 Φ s J U ≤ ∑ i ∈ I, ((𝓡 i).filter fun R => J ⊆ R).card := by
  unfold mload
  refine (sum_le_sum fun i _ => card_le_card (filter_subset_filter_of_imp ?_)).trans
    (sum_le_sum_of_subset hsI)
  intro R hR; exact hR.1
where
  filter_subset_filter_of_imp {p q : Finset (Fin n) → Prop} [DecidablePred p] [DecidablePred q]
      {t : Finset (Finset (Fin n))} (hpq : ∀ R, p R → q R) : t.filter p ⊆ t.filter q :=
    fun R hR => mem_filter.2 ⟨(mem_filter.1 hR).1, hpq R (mem_filter.1 hR).2⟩

/-- The load of the core roots is at most the pair load. -/
theorem load_le_mload {Rc : ι → Finset (Fin n)} {𝓡 : ι → Finset (Finset (Fin n))}
    {Φ : ι → Fin h → Fin n} {s : Finset ι} (hRc : ∀ i ∈ s, Rc i ∈ 𝓡 i) (J U : Finset (Fin n)) :
    load Rc Φ s J U ≤ mload 𝓡 Φ s J U := by
  unfold load mload
  rw [card_filter]
  refine sum_le_sum fun i hi => ?_
  split_ifs with hc
  · exact card_pos.2 ⟨Rc i, mem_filter.2 ⟨hRc i hi, hc⟩⟩
  · exact Nat.zero_le _

/-- The invariant of the outer placement with tracked root sets. -/
structure MInv (r lam m D : ℕ) (Z : Finset (Fin n)) (Rc : ι → Finset (Fin n))
    (𝓡 : ι → Finset (Finset (Fin n))) (Ts : ι → Finset (Finset (Fin n ⊕ Fin h)))
    (G : Finset (Finset (Fin n))) (s : Finset ι) (Φ : ι → Fin h → Fin n) : Prop where
  valid : ∀ i ∈ s, ValidPlacement (Rc i) (Φ i)
  range : ∀ i ∈ s, ∀ p, Φ i p ∈ Z
  disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
    Disjoint (newEdges (Ts i) (Φ i)) (newEdges (Ts j) (Φ j))
  host : ∀ i ∈ s, Disjoint (newEdges (Ts i) (Φ i)) G
  loads : ∀ J U : Finset (Fin n), U.Nonempty → J.card + U.card ≤ r - 1 →
    mload 𝓡 Φ s J U ≤ capA r lam D Z.card J.card U.card + m

omit [DecidableEq ι] in
/-- At the top level the sum of the pair loads is at most `2^(r-1) (λ^(r-1) D + m)`. -/
theorem sum_mloads_le {r lam m D : ℕ} (Z : Finset (Fin n)) (I : Finset ι)
    (Rc : ι → Finset (Fin n)) (𝓡 : ι → Finset (Finset (Fin n)))
    (Ts : ι → Finset (Finset (Fin n ⊕ Fin h))) (G : Finset (Finset (Fin n))) (s : Finset ι)
    (hsI : s ⊆ I) (Φ : ι → Fin h → Fin n) (hinv : MInv r lam m D Z Rc 𝓡 Ts G s Φ)
    (hlam : 1 ≤ lam)
    (hDeg : ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ i ∈ I, ((𝓡 i).filter fun R => S ⊆ R).card ≤ D)
    (S : Finset (Fin n)) (hS : S.card = r - 1) :
    ∑ J ∈ S.powerset, mload 𝓡 Φ s J (S \ J) ≤ 2 ^ (r - 1) * (lam ^ (r - 1) * D + m) := by
  classical
  calc ∑ J ∈ S.powerset, mload 𝓡 Φ s J (S \ J) ≤ ∑ _J ∈ S.powerset, (lam ^ (r - 1) * D + m) := by
        apply sum_le_sum
        intro J hJ
        rw [mem_powerset] at hJ
        have hcard : J.card + (S \ J).card = r - 1 := by
          rw [card_sdiff_of_subset hJ, ← hS]; have := card_le_card hJ; omega
        rcases (S \ J).eq_empty_or_nonempty with hU | hU
        · have hJS : J = S := by
            apply eq_of_subset_of_card_le hJ
            rw [hU, card_empty] at hcard; omega
          subst hJS
          rw [hU]
          calc mload 𝓡 Φ s J ∅ ≤ ∑ i ∈ I, ((𝓡 i).filter fun R => J ⊆ R).card :=
                mload_le_root hsI J ∅
            _ ≤ D := hDeg J hS
            _ ≤ lam ^ (r - 1) * D + m :=
                (Nat.le_mul_of_pos_left _ (by positivity)).trans (Nat.le_add_right _ _)
        · refine (hinv.loads J _ hU hcard.le).trans ?_
          unfold capA
          rw [show r - 1 - J.card - (S \ J).card = 0 by omega, pow_zero, mul_one]
          apply Nat.add_le_add_right
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_right hlam
          omega
    _ = 2 ^ (r - 1) * (lam ^ (r - 1) * D + m) := by
        rw [sum_const, card_powerset, hS, smul_eq_mul]

/-- The tracked roots of a gadget, all together. -/
def allRoots (𝓡 : ι → Finset (Finset (Fin n))) (i : ι) : Finset (Fin n) := (𝓡 i).biUnion id

omit [DecidableEq ι] in
theorem gadgetWF_allRoots {r k m : ℕ} {Rc : Finset (Fin n)} {𝓡 : Finset (Finset (Fin n))}
    {T : Finset (Finset (Fin n ⊕ Fin h))} (hw : GadgetWF r k Rc T) (hRc : Rc ∈ 𝓡)
    (hm : 𝓡.card ≤ m) (hk : ∀ R ∈ 𝓡, R.card ≤ k) : GadgetWF r (m * k) (𝓡.biUnion id) T where
  roots_le := by
    refine card_biUnion_le.trans ?_
    refine (sum_le_sum fun R hR => hk R hR).trans ?_
    rw [sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hm
  roots_ge := hw.roots_ge.trans (card_le_card (subset_biUnion_of_mem id hRc))
  edge_card := hw.edge_card
  edge_roots := fun t ht a ha => subset_biUnion_of_mem id hRc (hw.edge_roots t ht a ha)
  edge_aux := hw.edge_aux

/-- The constant `K'` bounding the degree of the edges placed so far. -/
def mrK (r h k m : ℕ) : ℕ :=
  placeM h k * 2 ^ (r - 1) * (placeLam h (m * k) ^ (r - 1) + m)

/-- The constant `C(r, h, k, m)` of the multi-root embedding lemma. -/
def mrC (r h k m : ℕ) : ℕ :=
  8 * placeM h (m * k) * (mrK r h k m + 1) * (m * k + h + 1)

theorem mrC_pos (r h k m : ℕ) : 0 < mrC r h k m := by
  unfold mrC; have := placeM_pos h (m * k); positivity

/-- The degree of the edges placed so far is at most `K' · D`. -/
theorem deg_used_le_mr {r k m lam D : ℕ} (Z : Finset (Fin n)) (I : Finset ι)
    (Rc : ι → Finset (Fin n)) (𝓡 : ι → Finset (Finset (Fin n)))
    (Ts : ι → Finset (Finset (Fin n ⊕ Fin h))) (G : Finset (Finset (Fin n))) (s : Finset ι)
    (hsI : s ⊆ I) (Φ : ι → Fin h → Fin n) (hinv : MInv r lam m D Z Rc 𝓡 Ts G s Φ)
    (hw : ∀ i ∈ I, GadgetWF r k (Rc i) (Ts i)) (hRc : ∀ i ∈ I, Rc i ∈ 𝓡 i) (hlam : 1 ≤ lam)
    (hDeg : ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ i ∈ I, ((𝓡 i).filter fun R => S ⊆ R).card ≤ D)
    (S : Finset (Fin n)) (hS : S.card = r - 1) :
    deg (s.biUnion fun i => newEdges (Ts i) (Φ i)) S ≤
      2 ^ (k + h) * (2 ^ (r - 1) * (lam ^ (r - 1) * D + m)) := by
  refine (deg_biUnion_le_loads Rc Ts Φ s (fun i hi => hw i (hsI hi)) S).trans ?_
  apply Nat.mul_le_mul_left
  refine (sum_le_sum fun J _ => load_le_mload (fun i hi => hRc i (hsI hi)) J (S \ J)).trans ?_
  exact sum_mloads_le Z I Rc 𝓡 Ts G s hsI Φ hinv hlam hDeg S hS

/-- **One step of the outer placement with tracked root sets.** -/
theorem mInv_step {r k m : ℕ} (Z : Finset (Fin n)) (I : Finset ι) (Rc : ι → Finset (Fin n))
    (𝓡 : ι → Finset (Finset (Fin n))) (Ts : ι → Finset (Finset (Fin n ⊕ Fin h)))
    (G : Finset (Finset (Fin n))) (D : ℕ)
    (hw : ∀ i ∈ I, GadgetWF r k (Rc i) (Ts i)) (hRc : ∀ i ∈ I, Rc i ∈ 𝓡 i)
    (hm : ∀ i ∈ I, (𝓡 i).card ≤ m) (hk : ∀ i ∈ I, ∀ R ∈ 𝓡 i, R.card ≤ k)
    (hG : ∀ S : Finset (Fin n), S.card = r - 1 → mrC r h k m * deg G S ≤ Z.card)
    (hDn : mrC r h k m * D ≤ Z.card)
    (hRoot : ∀ J : Finset (Fin n), J.card ≤ r - 1 →
      ∑ i ∈ I, ((𝓡 i).filter fun R => J ⊆ R).card ≤ D * Z.card ^ (r - 1 - J.card))
    {s : Finset ι} (hsI : s ⊆ I) {i : ι} (hiI : i ∈ I) (his : i ∉ s) {Φ : ι → Fin h → Fin n}
    (hinv : MInv r (placeLam h (m * k)) m D Z Rc 𝓡 Ts G s Φ) :
    ∃ φ, MInv r (placeLam h (m * k)) m D Z Rc 𝓡 Ts G (insert i s) (Function.update Φ i φ) := by
  classical
  set k' := m * k
  set M := placeM h k'
  set lam := placeLam h k'
  set K := mrK r h k m
  set C := mrC r h k m
  set a := Z.card
  have hlam1 : 1 ≤ lam := Nat.le_add_left _ _
  have hDeg : ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ i ∈ I, ((𝓡 i).filter fun R => S ⊆ R).card ≤ D := by
    intro S hS
    have := hRoot S hS.le
    rwa [hS, Nat.sub_self, pow_zero, mul_one] at this
  have hD : 0 < D := by
    have h0 := hRoot ∅ (by simp)
    have h1 : 0 < ∑ j ∈ I, ((𝓡 j).filter fun R => (∅ : Finset (Fin n)) ⊆ R).card := by
      refine lt_of_lt_of_le ?_ (single_le_sum (fun j _ => Nat.zero_le _) hiI)
      exact card_pos.2 ⟨Rc i, mem_filter.2 ⟨hRc i hiI, empty_subset _⟩⟩
    rcases Nat.eq_zero_or_pos D with hD0 | hD0
    · rw [hD0, zero_mul] at h0; omega
    · exact hD0
  have hM := placeM_pos h k'
  have hCpos : 0 < C := mrC_pos r h k m
  have hCD : C ≤ a := (Nat.le_mul_of_pos_right C hD).trans hDn
  set Gd := a / C
  have hGd : ∀ S : Finset (Fin n), S.card = r - 1 → deg G S ≤ Gd := fun S hS =>
    (Nat.le_div_iff_mul_le hCpos).2 (by rw [mul_comm]; exact hG S hS)
  have hCGd : C * Gd ≤ a := Nat.mul_div_le a C
  set used := s.biUnion fun j => newEdges (Ts j) (Φ j)
  set F := G ∪ used
  have hF : ∀ B : Finset (Fin n), B.card = r - 1 → deg F B ≤ Gd + K * D := by
    intro B hB
    unfold F deg
    rw [filter_union]
    refine (card_union_le _ _).trans (Nat.add_le_add (hGd B hB) ?_)
    have := deg_used_le_mr Z I Rc 𝓡 Ts G s hsI Φ hinv hw hRc hlam1 hDeg B hB
    refine this.trans ?_
    have hmD : m ≤ m * D := Nat.le_mul_of_pos_right _ hD
    calc 2 ^ (k + h) * (2 ^ (r - 1) * (lam ^ (r - 1) * D + m))
        ≤ 2 ^ (k + h) * (2 ^ (r - 1) * (lam ^ (r - 1) * D + m * D)) := by
          apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; omega
      _ = K * D := by
          simp only [K, mrK, placeM, lam, k']; ring
  -- the inner placement, over the pair family
  set Rs : (Σ _ : ι, Finset (Fin n)) → Finset (Fin n) := fun p => p.2
  set Φs : (Σ _ : ι, Finset (Fin n)) → Fin h → Fin n := fun p => Φ p.1
  have hwU : GadgetWF r k' (allRoots 𝓡 i) (Ts i) :=
    gadgetWF_allRoots (hw i hiI) (hRc i hiI) (hm i hiI) (hk i hiI)
  have hroot : ∀ J ⊆ allRoots 𝓡 i, J.card ≤ r - 1 →
      load Rs Φs (s.sigma 𝓡) J ∅ ≤ D * a ^ (r - 1 - J.card) := by
    intro J _ hJ
    rw [← mload_eq_load]
    exact (mload_le_root hsI J ∅).trans (hRoot J hJ)
  have hlam : 4 * 2 ^ (k' + h) * h ≤ lam := Nat.le_succ _
  have hnum : 4 * (k' + h + 2 ^ (k' + h) * (Gd + K * D)) < 3 * a := by
    have e1 : 8 * (M * Gd) ≤ a := by
      refine le_trans ?_ hCGd
      rw [← mul_assoc]
      apply Nat.mul_le_mul_right
      simp only [C, mrC]
      calc 8 * M = 8 * M * 1 * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e2 : 8 * (M * (K * D)) ≤ a := by
      refine le_trans ?_ hDn
      rw [← mul_assoc, ← mul_assoc]
      apply Nat.mul_le_mul_right
      simp only [C, mrC]
      calc 8 * M * K = 8 * M * K * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e3 : 8 * (k' + h + 1) ≤ a := by
      refine le_trans ?_ hCD
      simp only [C, mrC]
      calc 8 * (k' + h + 1) = 8 * 1 * 1 * (k' + h + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) (by omega))
    have : 2 ^ (k' + h) = M := rfl
    have hma : M * (Gd + K * D) = M * Gd + M * (K * D) := mul_add _ _ _
    rw [this, hma]
    omega
  obtain ⟨φ, hφ⟩ :=
    exists_innerInvA_univ Z Rs Φs (s.sigma 𝓡) (allRoots 𝓡 i) (Ts i) hwU F hroot hF hD hlam hnum
  have hΦ : ∀ j ∈ s, Function.update Φ i φ j = Φ j := fun j hj =>
    Function.update_of_ne (by rintro rfl; exact his hj) _ _
  have hφinj : Function.Injective φ := fun a b hab => hφ.inj (mem_univ a) (mem_univ b) hab
  have hnewF : ∀ f ∈ newEdges (Ts i) φ, f ∉ F := by
    intro f hf
    simp only [newEdges, mem_image] at hf
    obtain ⟨t, ht, rfl⟩ := hf
    exact hφ.edges t ht (fun p _ => mem_univ p)
  have hnew : ∀ j ∈ insert i s, newEdges (Ts j) (Function.update Φ i φ j) =
      if j = i then newEdges (Ts i) φ else newEdges (Ts j) (Φ j) := by
    intro j hj
    split_ifs with hji
    · subst hji; rw [Function.update_self]
    · rw [Function.update_of_ne hji]
  refine ⟨φ, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j hj
    rcases mem_insert.1 hj with rfl | hj
    · rw [Function.update_self]
      refine ⟨hφinj, fun p hp => hφ.avoid p (mem_univ p) ?_⟩
      exact subset_biUnion_of_mem id (hRc j hiI) hp
    · rw [hΦ j hj]; exact hinv.valid j hj
  · intro j hj p
    rcases mem_insert.1 hj with rfl | hj
    · rw [Function.update_self]; exact hφ.range p (mem_univ p)
    · rw [hΦ j hj]; exact hinv.range j hj p
  · intro j hj j' hj' hjj'
    rw [hnew j hj, hnew j' hj']
    have side : ∀ b ∈ s, Disjoint (newEdges (Ts i) φ) (newEdges (Ts b) (Φ b)) := by
      intro b hb
      rw [disjoint_left]
      intro f hf hf'
      exact hnewF f hf (mem_union_right _ (mem_biUnion.2 ⟨b, hb, hf'⟩))
    split_ifs with h1 h2 h2
    · exact absurd (h1.trans h2.symm) hjj'
    · subst h1
      exact side j' ((mem_insert.1 hj').resolve_left h2)
    · subst h2
      exact (side j ((mem_insert.1 hj).resolve_left h1)).symm
    · exact hinv.disj j ((mem_insert.1 hj).resolve_left h1) j'
        ((mem_insert.1 hj').resolve_left h2) hjj'
  · intro j hj
    rw [hnew j hj]
    split_ifs with h1
    · rw [disjoint_left]
      intro f hf hfG
      exact hnewF f hf (mem_union_left _ hfG)
    · exact hinv.host j ((mem_insert.1 hj).resolve_left h1)
  · intro J U hU hcard
    rw [mload_insert his, Function.update_self, mload_congr hΦ]
    by_cases hc : U ⊆ auxImage φ ∧ J ⊆ allRoots 𝓡 i
    · obtain ⟨hUφ, hJR⟩ := hc
      set P := univ.filter fun p => φ p ∈ U
      have hPU : P.image φ = U := by
        ext x
        simp only [P, mem_image, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨p, hp, rfl⟩; exact hp
        · intro hx
          obtain ⟨p, -, hp⟩ := mem_image.1 (hUφ hx)
          exact ⟨p, hp ▸ hx, hp⟩
      have hPc : P.card = U.card := by
        rw [← hPU, card_image_of_injective _ hφinj]
      have hPne : P.Nonempty := by
        rw [← card_pos, hPc]; exact card_pos.2 hU
      have h1 := hφ.loads J hJR P (subset_univ _) hPne (by omega)
      rw [hPU, hPc, ← mload_eq_load] at h1
      have h2 : ((𝓡 i).filter fun R => J ⊆ R ∧ U ⊆ auxImage φ).card ≤ m :=
        (card_filter_le _ _).trans (hm i hiI)
      omega
    · have h0 : ((𝓡 i).filter fun R => J ⊆ R ∧ U ⊆ auxImage φ).card = 0 := by
        refine card_eq_zero.2 (filter_eq_empty_iff.2 fun R hR hJU => hc ⟨hJU.2, ?_⟩)
        exact hJU.1.trans (subset_biUnion_of_mem id hR)
      rw [h0, add_zero]
      exact hinv.loads J U hU hcard

/-- **Partial Clique Embedding Lemma with tracked root sets** (see the module docstring). -/
theorem reserveMultiRootEmbedding (r h k m : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ) {ι : Type*} [DecidableEq ι] (I : Finset ι)
      (Rc : ι → Finset (Fin n)) (𝓡 : ι → Finset (Finset (Fin n)))
      (T : ι → Finset (Finset (Fin n ⊕ Fin h)))
      (G : Finset (Finset (Fin n))) (Z : Finset (Fin n)) (D : ℕ),
      (∀ i ∈ I, GadgetWF r k (Rc i) (T i)) → (∀ i ∈ I, Rc i ∈ 𝓡 i) →
      (∀ i ∈ I, (𝓡 i).card ≤ m) → (∀ i ∈ I, ∀ R ∈ 𝓡 i, R.card ≤ k) →
      (∀ S : Finset (Fin n), S.card = r - 1 → C * deg G S ≤ Z.card) →
      C * D ≤ Z.card →
      (∀ J : Finset (Fin n), J.card ≤ r - 1 →
        ∑ i ∈ I, ((𝓡 i).filter fun R => J ⊆ R).card ≤ D * Z.card ^ (r - 1 - J.card)) →
      0 < Z.card →
      ∃ Φ : ι → Fin h → Fin n,
        (∀ i ∈ I, ValidPlacement (Rc i) (Φ i)) ∧
        (∀ i ∈ I, ∀ p, Φ i p ∈ Z) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (newEdges (T i) (Φ i)) (newEdges (T j) (Φ j))) ∧
        (∀ i ∈ I, Disjoint (newEdges (T i) (Φ i)) G) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          deg (I.biUnion fun i => newEdges (T i) (Φ i)) S ≤ C * D) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          ∑ i ∈ I, ((𝓡 i).filter fun R => S ⊆ R ∪ auxImage (Φ i)).card ≤ C * D) := by
  refine ⟨mrC r h k m, mrC_pos r h k m, ?_⟩
  intro n ι _ I Rc 𝓡 T G Z D hw hRc hm hk hG hDn hRoot hZ
  have hDeg : ∀ S : Finset (Fin n), S.card = r - 1 →
      ∑ i ∈ I, ((𝓡 i).filter fun R => S ⊆ R).card ≤ D := by
    intro S hS
    have := hRoot S hS.le
    rwa [hS, Nat.sub_self, pow_zero, mul_one] at this
  obtain ⟨z₀, -⟩ := card_pos.1 hZ
  have key : ∀ s ⊆ I, ∃ Φ, MInv r (placeLam h (m * k)) m D Z Rc 𝓡 T G s Φ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun _ _ => z₀, ⟨by simp, by simp, by simp, by simp, ?_⟩⟩
      intro J U _ _
      simp [mload]
    | insert i s his ih =>
      intro hsI
      obtain ⟨Φ, hΦ⟩ := ih ((subset_insert i s).trans hsI)
      obtain ⟨φ, hφ⟩ := mInv_step Z I Rc 𝓡 T G D hw hRc hm hk hG hDn hRoot
        ((subset_insert i s).trans hsI) (hsI (mem_insert_self i s)) his hΦ
      exact ⟨_, hφ⟩
  obtain ⟨Φ, hΦ⟩ := key I subset_rfl
  have hD1 : m ≤ m * D ∨ I = ∅ := by
    rcases I.eq_empty_or_nonempty with hI | ⟨i, hi⟩
    · exact Or.inr hI
    · left
      have h0 := hRoot ∅ (by simp)
      have h1 : 0 < ∑ j ∈ I, ((𝓡 j).filter fun R => (∅ : Finset (Fin n)) ⊆ R).card := by
        refine lt_of_lt_of_le ?_ (single_le_sum (fun j _ => Nat.zero_le _) hi)
        exact card_pos.2 ⟨Rc i, mem_filter.2 ⟨hRc i hi, empty_subset _⟩⟩
      rcases Nat.eq_zero_or_pos D with hD0 | hD0
      · rw [hD0, zero_mul] at h0; omega
      · exact Nat.le_mul_of_pos_right _ hD0
  have hbound : 2 ^ (r - 1) * (placeLam h (m * k) ^ (r - 1) * D + m) ≤ mrK r h k m * D ∨
      I = ∅ := by
    rcases hD1 with hD1 | hI
    · left
      calc 2 ^ (r - 1) * (placeLam h (m * k) ^ (r - 1) * D + m)
          ≤ 2 ^ (r - 1) * (placeLam h (m * k) ^ (r - 1) * D + m * D) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 1 * 2 ^ (r - 1) * (placeLam h (m * k) ^ (r - 1) + m) * D := by ring
        _ ≤ placeM h k * 2 ^ (r - 1) * (placeLam h (m * k) ^ (r - 1) + m) * D :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
              (placeM_pos h k)))
    · exact Or.inr hI
  have hKC : mrK r h k m ≤ mrC r h k m := by
    unfold mrC
    have := placeM_pos h (m * k)
    calc mrK r h k m ≤ mrK r h k m + 1 := Nat.le_succ _
      _ ≤ 8 * placeM h (m * k) * (mrK r h k m + 1) * (m * k + h + 1) := by
          calc mrK r h k m + 1 = 1 * (mrK r h k m + 1) * 1 := by ring
            _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega)
  refine ⟨Φ, hΦ.valid, hΦ.range, hΦ.disj, hΦ.host, fun S hS => ?_, fun S hS => ?_⟩
  · rcases hbound with hb | hI
    · refine (deg_used_le_mr Z I Rc 𝓡 T G I subset_rfl Φ hΦ hw hRc (Nat.le_add_left _ _) hDeg S
        hS).trans ?_
      have : 2 ^ (k + h) * (2 ^ (r - 1) * (placeLam h (m * k) ^ (r - 1) * D + m)) ≤
          mrK r h k m * D := by
        have h2 : 2 ^ (k + h) * (2 ^ (r - 1) * (placeLam h (m * k) ^ (r - 1) * D + m)) ≤
            2 ^ (k + h) * (2 ^ (r - 1) * (placeLam h (m * k) ^ (r - 1) * D + m * D)) := by
          apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left
          have : 1 * 2 ^ (r - 1) * (placeLam h (m * k) ^ (r - 1) * D + m) ≤
              mrK r h k m * D := by rw [one_mul]; exact hb
          rcases Nat.eq_zero_or_pos D with hD0 | hD0
          · subst hD0
            simp only [mul_zero, zero_add, Nat.mul_zero] at this ⊢
            have h2pos : 0 < 2 ^ (r - 1) := by positivity
            have : m = 0 := by
              rcases Nat.eq_zero_or_pos m with h | h
              · exact h
              · exfalso; nlinarith
            omega
          · exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hD0) _
        refine h2.trans (le_of_eq ?_)
        simp only [mrK, placeM]; ring
      exact this.trans (Nat.mul_le_mul_right _ hKC)
    · subst hI; simp [deg]
  · rcases hbound with hb | hI
    · have h1 := card_cover_le_loads (fun p : (Σ _ : ι, Finset (Fin n)) => p.2)
        (fun p => Φ p.1) (I.sigma 𝓡) S
      rw [RefinedAbsorption.FlatOmni.card_filter_sigma] at h1
      refine h1.trans ?_
      refine (le_of_eq (sum_congr rfl fun J _ => (mload_eq_load 𝓡 Φ I J (S \ J)).symm)).trans ?_
      refine (sum_mloads_le Z I Rc 𝓡 T G I subset_rfl Φ hΦ (Nat.le_add_left _ _) hDeg S hS).trans
        ?_
      exact hb.trans (Nat.mul_le_mul_right _ hKC)
    · subst hI; simp

end RefinedAbsorption.General
