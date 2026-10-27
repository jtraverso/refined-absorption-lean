module
public import RequestProject.Placement.Inner

/-!
# The Partial Clique Embedding Lemma (Delcourt–Postle, Lemma 5.2)

Mathematics: M. Delcourt and L. Postle, *Proof of the Existence Conjecture via Refined
Absorption*, arXiv:2402.17855, Section 5.2.  Lean formalization: Juan Pablo Traverso Gianini
(Apache-2.0).

Fix `r ≥ 1`, the number `h` of auxiliary vertices of a gadget and the bound `k` on the number of
roots.  There is a constant `C = C(r, h, k)` such that the following holds on `Fin n`.  Let `G` be
a host `r`-graph of forbidden edges with `C · deg_G(S) ≤ n` for every `(r-1)`-set `S`, and let
`(R i, T i)`, `i ∈ I`, be gadgets (at most `k` and at least `r - 1` roots, template edges of size
`r` each using an auxiliary vertex).  If every `(r-1)`-set lies in at most `D` root sets and
`C · D ≤ n`, then the gadgets can be placed by injective maps `Φ i : Fin h → Fin n` avoiding their
roots so that
* the new edges of different gadgets are pairwise disjoint,
* no new edge is an edge of `G`,
* every `(r-1)`-set lies in at most `C · D` new edges.

The proof is the greedy argument of the paper.  We maintain the mixed loads
`d(J, U) = #{placed i : J ⊆ R i, U ⊆ Φ i (Fin h)}` capped by `λ^|U| · D · n^(r-1-|J|-|U|)`, and we
extend a partial placement gadget by gadget, and inside each gadget vertex by vertex
(`innerInv_step`): saturated loads, forbidden host/used edges and injectivity exclude fewer than
`n` candidates.  At the top level `|J| + |U| = r - 1` the caps give the final degree bound.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset

variable {n h : ℕ} {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- Running the inner placement over all auxiliary positions. -/
theorem exists_innerInv_univ {r k lam D Fdeg : ℕ} (Rs : ι → Finset (Fin n))
    (Φ : ι → Fin h → Fin n) (s : Finset ι) (R : Finset (Fin n))
    (T : Finset (Finset (Fin n ⊕ Fin h))) (hw : GadgetWF r k R T) (F : Finset (Finset (Fin n)))
    (hroot : ∀ J ⊆ R, J.card ≤ r - 1 → load Rs Φ s J ∅ ≤ D * n ^ (r - 1 - J.card))
    (hF : ∀ B : Finset (Fin n), B.card = r - 1 → deg F B ≤ Fdeg)
    (hD : 0 < D) (hlam : 4 * 2 ^ (k + h) * h ≤ lam)
    (hnum : 4 * (k + h + 2 ^ (k + h) * Fdeg) < 3 * n) :
    ∃ φ, InnerInv r lam D Rs Φ s R T F univ φ := by
  have hn : 0 < n := by omega
  have key : ∀ A : Finset (Fin h), ∃ φ, InnerInv r lam D Rs Φ s R T F A φ := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨fun _ => ⟨0, hn⟩, innerInv_empty r lam D Rs Φ s R T hw F _⟩
    | insert p A hp ih =>
      obtain ⟨φ, hφ⟩ := ih
      exact ⟨_, (innerInv_step Rs Φ s R T hw F hroot hF hD hlam hnum hφ hp).choose_spec⟩
  exact key univ

/-- The invariant of the outer (gadget-by-gadget) placement. -/
structure OuterInv (r lam D : ℕ) (Rs : ι → Finset (Fin n))
    (Ts : ι → Finset (Finset (Fin n ⊕ Fin h))) (G : Finset (Finset (Fin n))) (s : Finset ι)
    (Φ : ι → Fin h → Fin n) : Prop where
  valid : ∀ i ∈ s, ValidPlacement (Rs i) (Φ i)
  disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
    Disjoint (newEdges (Ts i) (Φ i)) (newEdges (Ts j) (Φ j))
  host : ∀ i ∈ s, Disjoint (newEdges (Ts i) (Φ i)) G
  loads : ∀ J U : Finset (Fin n), U.Nonempty → J.card + U.card ≤ r - 1 →
    load Rs Φ s J U ≤ cap r lam D n J U.card

omit [DecidableEq ι] in
theorem load_congr {Rs : ι → Finset (Fin n)} {Φ Ψ : ι → Fin h → Fin n} {s : Finset ι}
    (hΦ : ∀ j ∈ s, Φ j = Ψ j) (J U : Finset (Fin n)) : load Rs Φ s J U = load Rs Ψ s J U := by
  unfold load
  congr 1
  exact filter_congr (fun j hj => by rw [hΦ j hj])

theorem load_insert {Rs : ι → Finset (Fin n)} {Φ : ι → Fin h → Fin n} {s : Finset ι} {i : ι}
    (hi : i ∉ s) (J U : Finset (Fin n)) :
    load Rs Φ (insert i s) J U =
      load Rs Φ s J U + if J ⊆ Rs i ∧ U ⊆ auxImage (Φ i) then 1 else 0 := by
  unfold load
  rw [filter_insert]
  split_ifs with hc
  · rw [card_insert_of_notMem (fun h => hi (mem_filter.1 h).1)]
  · rfl

/-- The degree of the edges placed so far is at most `K · D`, `K = 2^(k+h) · 2^(r-1) · λ^(r-1)`. -/
theorem deg_used_le {r k lam D : ℕ} (I : Finset ι) (Rs : ι → Finset (Fin n))
    (Ts : ι → Finset (Finset (Fin n ⊕ Fin h))) (G : Finset (Finset (Fin n))) (s : Finset ι)
    (hsI : s ⊆ I) (Φ : ι → Fin h → Fin n) (hinv : OuterInv r lam D Rs Ts G s Φ)
    (hw : ∀ i ∈ I, GadgetWF r k (Rs i) (Ts i)) (hlam : 1 ≤ lam)
    (hDeg : ∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ Rs i).card ≤ D)
    (S : Finset (Fin n)) (hS : S.card = r - 1) :
    deg (s.biUnion fun i => newEdges (Ts i) (Φ i)) S ≤
      2 ^ (k + h) * 2 ^ (r - 1) * lam ^ (r - 1) * D := by
  refine (deg_biUnion_le_loads Rs Ts Φ s (fun i hi => hw i (hsI hi)) S).trans ?_
  rw [mul_assoc (2 ^ (k + h)), mul_assoc (2 ^ (k + h))]
  apply Nat.mul_le_mul_left
  calc ∑ J ∈ S.powerset, load Rs Φ s J (S \ J) ≤ ∑ _J ∈ S.powerset, lam ^ (r - 1) * D := by
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
          calc load Rs Φ s J ∅ ≤ (I.filter fun i => J ⊆ Rs i).card := by
                apply card_le_card
                intro i hi
                simp only [mem_filter] at hi ⊢
                exact ⟨hsI hi.1, hi.2.1⟩
            _ ≤ D := hDeg J hS
            _ ≤ lam ^ (r - 1) * D := Nat.le_mul_of_pos_left _ (by positivity)
        · refine (hinv.loads J _ hU hcard.le).trans ?_
          unfold cap
          rw [show r - 1 - J.card - (S \ J).card = 0 by omega, pow_zero, mul_one]
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_right hlam
          omega
    _ = 2 ^ (r - 1) * (lam ^ (r - 1) * D) := by
        rw [sum_const, card_powerset, hS, smul_eq_mul]
    _ = _ := by ring

/-- The constants of the lemma. -/
def placeM (h k : ℕ) : ℕ := 2 ^ (k + h)
def placeLam (h k : ℕ) : ℕ := 4 * placeM h k * h + 1
def placeK (r h k : ℕ) : ℕ := placeM h k * 2 ^ (r - 1) * placeLam h k ^ (r - 1)
/-- The constant `C(r, h, k)` of the Partial Clique Embedding Lemma. -/
def placeC (r h k : ℕ) : ℕ := 8 * placeM h k * (placeK r h k + 1) * (k + h + 1)

theorem placeM_pos (h k : ℕ) : 0 < placeM h k := by unfold placeM; positivity
theorem placeK_le_placeC (r h k : ℕ) : placeK r h k ≤ placeC r h k := by
  unfold placeC
  have := placeM_pos h k
  calc placeK r h k ≤ placeK r h k + 1 := Nat.le_succ _
    _ ≤ 8 * placeM h k * (placeK r h k + 1) * (k + h + 1) := by
        have h1 : 1 ≤ 8 * placeM h k := by omega
        have h2 : 1 ≤ k + h + 1 := by omega
        calc placeK r h k + 1 = 1 * (placeK r h k + 1) * 1 := by ring
          _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ h1) h2

/-- **One step of the outer placement**: one more gadget is placed. -/
theorem outerInv_step {r k : ℕ} (I : Finset ι) (Rs : ι → Finset (Fin n))
    (Ts : ι → Finset (Finset (Fin n ⊕ Fin h))) (G : Finset (Finset (Fin n))) (D : ℕ)
    (hw : ∀ i ∈ I, GadgetWF r k (Rs i) (Ts i))
    (hG : ∀ S : Finset (Fin n), S.card = r - 1 → placeC r h k * deg G S ≤ n)
    (hDn : placeC r h k * D ≤ n)
    (hDeg : ∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ Rs i).card ≤ D)
    {s : Finset ι} (hsI : s ⊆ I) {i : ι} (hiI : i ∈ I) (his : i ∉ s) {Φ : ι → Fin h → Fin n}
    (hinv : OuterInv r (placeLam h k) D Rs Ts G s Φ) :
    ∃ φ, OuterInv r (placeLam h k) D Rs Ts G (insert i s) (Function.update Φ i φ) := by
  classical
  set M := placeM h k
  set lam := placeLam h k
  set K := placeK r h k
  set C := placeC r h k
  have hlam1 : 1 ≤ lam := Nat.le_add_left _ _
  -- the root incidence bound
  have hrootI := rootIncidence I Rs D (fun i hi => (hw i hi).roots_ge) hDeg
  have hD : 0 < D := by
    have := hrootI ∅ (by simp)
    have hmem : i ∈ I.filter fun j => (∅ : Finset (Fin n)) ⊆ Rs j := by simp [hiI]
    have h1 := card_pos.2 ⟨i, hmem⟩
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · rw [h0, zero_mul] at this; omega
    · exact h0
  have hM := placeM_pos h k
  have hCpos : 0 < C := by unfold C placeC; positivity
  have hCD : C ≤ n := (Nat.le_mul_of_pos_right C hD).trans hDn
  set Gd := n / C
  have hGd : ∀ S : Finset (Fin n), S.card = r - 1 → deg G S ≤ Gd := fun S hS =>
    (Nat.le_div_iff_mul_le hCpos).2 (by rw [mul_comm]; exact hG S hS)
  have hCGd : C * Gd ≤ n := Nat.mul_div_le n C
  set used := s.biUnion fun j => newEdges (Ts j) (Φ j)
  set F := G ∪ used
  have hF : ∀ B : Finset (Fin n), B.card = r - 1 → deg F B ≤ Gd + K * D := by
    intro B hB
    unfold F deg
    rw [filter_union]
    refine (card_union_le _ _).trans (Nat.add_le_add (hGd B hB) ?_)
    have := deg_used_le I Rs Ts G s hsI Φ hinv hw hlam1 hDeg B hB
    simpa [K, placeK, M, placeM, lam] using this
  have hroot : ∀ J ⊆ Rs i, J.card ≤ r - 1 → load Rs Φ s J ∅ ≤ D * n ^ (r - 1 - J.card) := by
    intro J _ hJ
    refine le_trans (card_le_card ?_) (hrootI J hJ)
    intro j hj
    simp only [mem_filter] at hj ⊢
    exact ⟨hsI hj.1, hj.2.1⟩
  have hlam : 4 * 2 ^ (k + h) * h ≤ lam := Nat.le_succ _
  have hnum : 4 * (k + h + 2 ^ (k + h) * (Gd + K * D)) < 3 * n := by
    have e1 : 8 * (M * Gd) ≤ n := by
      refine le_trans ?_ hCGd
      rw [← mul_assoc]
      apply Nat.mul_le_mul_right
      unfold C placeC
      calc 8 * M = 8 * M * 1 * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e2 : 8 * (M * (K * D)) ≤ n := by
      refine le_trans ?_ hDn
      rw [← mul_assoc, ← mul_assoc]
      apply Nat.mul_le_mul_right
      unfold C placeC
      calc 8 * M * K = 8 * M * K * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e3 : 8 * (k + h + 1) ≤ n := by
      refine le_trans ?_ hCD
      unfold C placeC
      calc 8 * (k + h + 1) = 8 * 1 * 1 * (k + h + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) (by omega))
    have : 2 ^ (k + h) = M := rfl
    have hma : M * (Gd + K * D) = M * Gd + M * (K * D) := mul_add _ _ _
    rw [this, hma]
    omega
  obtain ⟨φ, hφ⟩ := exists_innerInv_univ Rs Φ s (Rs i) (Ts i) (hw i hiI) F hroot hF hD hlam hnum
  have hΦ : ∀ j ∈ s, Function.update Φ i φ j = Φ j := fun j hj =>
    Function.update_of_ne (by rintro rfl; exact his hj) _ _
  have hφinj : Function.Injective φ := fun a b hab => hφ.inj (mem_univ a) (mem_univ b) hab
  -- new edges of `i` avoid `F`
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
  refine ⟨φ, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro j hj
    rcases mem_insert.1 hj with rfl | hj
    · rw [Function.update_self]
      exact ⟨hφinj, fun p => hφ.avoid p (mem_univ p)⟩
    · rw [hΦ j hj]; exact hinv.valid j hj
  · intro j hj j' hj' hjj'
    rw [hnew j hj, hnew j' hj']
    have side : ∀ a ∈ s, Disjoint (newEdges (Ts i) φ) (newEdges (Ts a) (Φ a)) := by
      intro a ha
      rw [disjoint_left]
      intro f hf hf'
      exact hnewF f hf (mem_union_right _ (mem_biUnion.2 ⟨a, ha, hf'⟩))
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
    rw [load_insert his, Function.update_self, load_congr hΦ]
    split_ifs with hc
    · obtain ⟨hJR, hUφ⟩ := hc
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
      have := hφ.loads J hJR P (subset_univ _) hPne (by omega)
      rw [hPU, hPc] at this
      omega
    · rw [add_zero]; exact hinv.loads J U hU hcard

/-- **Partial Clique Embedding Lemma** (Delcourt–Postle, Lemma 5.2), the actual greedy
construction on `Fin n`.

For fixed `r ≥ 1`, `h`, `k` there is `C` such that any family of gadgets with at most `k` roots
(and at least `r - 1`), `h` auxiliary vertices and template edges of size `r` (each meeting the
auxiliary vertices) can be placed by injective maps avoiding their roots, so that the new edges of
distinct gadgets are pairwise disjoint and disjoint from the host `G`, and the union of all new
edges has maximum `(r-1)`-degree at most `C · D`, where `D` bounds the `(r-1)`-degree of the root
family.  The hypotheses are `C · Δ_{r-1}(G) ≤ n`, `C · D ≤ n` and `0 < n` (the last one only
matters when there is nothing to place). -/
theorem partialCliqueEmbedding (r h k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ) {ι : Type*} [DecidableEq ι] (I : Finset ι)
      (R : ι → Finset (Fin n)) (T : ι → Finset (Finset (Fin n ⊕ Fin h)))
      (G : Finset (Finset (Fin n))) (D : ℕ),
      (∀ i ∈ I, GadgetWF r k (R i) (T i)) →
      (∀ S : Finset (Fin n), S.card = r - 1 → C * deg G S ≤ n) →
      C * D ≤ n →
      (∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ R i).card ≤ D) →
      0 < n →
      ∃ Φ : ι → Fin h → Fin n,
        (∀ i ∈ I, ValidPlacement (R i) (Φ i)) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (newEdges (T i) (Φ i)) (newEdges (T j) (Φ j))) ∧
        (∀ i ∈ I, Disjoint (newEdges (T i) (Φ i)) G) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          deg (I.biUnion fun i => newEdges (T i) (Φ i)) S ≤ C * D) := by
  refine ⟨placeC r h k, by unfold placeC; have := placeM_pos h k; positivity, ?_⟩
  intro n ι _ I R T G D hw hG hDn hDeg hn
  have key : ∀ s ⊆ I, ∃ Φ, OuterInv r (placeLam h k) D R T G s Φ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun _ _ => ⟨0, hn⟩, ⟨by simp, by simp, by simp, ?_⟩⟩
      intro J U _ _
      simp [load]
    | insert i s his ih =>
      intro hsI
      obtain ⟨Φ, hΦ⟩ := ih ((subset_insert i s).trans hsI)
      obtain ⟨φ, hφ⟩ := outerInv_step I R T G D hw hG hDn hDeg ((subset_insert i s).trans hsI)
        (hsI (mem_insert_self i s)) his hΦ
      exact ⟨_, hφ⟩
  obtain ⟨Φ, hΦ⟩ := key I subset_rfl
  refine ⟨Φ, hΦ.valid, hΦ.disj, hΦ.host, fun S hS => ?_⟩
  refine (deg_used_le I R T G I subset_rfl Φ hΦ hw (Nat.le_add_left _ _) hDeg S hS).trans ?_
  exact Nat.mul_le_mul_right _ (placeK_le_placeC r h k)

end RefinedAbsorption.Placement
