module
public import RequestProject.Placement.ReserveInner
public import RequestProject.Placement.Lemma52

/-!
# The Partial Clique Embedding Lemma inside a reserve

Mathematics: M. Delcourt and L. Postle, *Proof of the Existence Conjecture via Refined
Absorption*, arXiv:2402.17855, Section 5.2 (Lemma 5.2), in the form needed by the refine-down
steps, where new vertices have to be placed in a prescribed reserve.  Lean formalization: Juan
Pablo Traverso Gianini (Apache-2.0).

Fix `r ≥ 1`, the number `h` of auxiliary vertices of a gadget and the bound `k` on the number of
roots.  There is `C = C(r, h, k)` such that the following holds for every reserve `Z ⊆ Fin n` of
size `a = |Z|`.  Let `G` be a host `r`-graph of forbidden edges with `C · deg_G(S) ≤ a` for every
`(r-1)`-set `S`, and let `(R i, T i)`, `i ∈ I`, be gadgets whose roots may lie anywhere in
`Fin n`.  Assume the root family is not too dense compared to the reserve: every `j`-set `J`
(`j ≤ r - 1`) lies in at most `D · a^(r-1-j)` root sets, and `C · D ≤ a`.  Then the gadgets can be
placed by injective maps `Φ i : Fin h → Z` avoiding their roots so that
* the new edges of different gadgets are pairwise disjoint,
* no new edge is an edge of `G`,
* every `(r-1)`-set lies in at most `C · D` new edges, and in the vertex sets
  `R i ∪ Φ i (Fin h)` of at most `C · D` gadgets.

For `Z = univ` the density hypothesis follows from the `(r-1)`-degree bound (`rootIncidence`),
and the statement is `partialCliqueEmbedding`.  `rootIncidence_of_subset` gives the density
hypothesis when all roots lie in a set `U` with `|U| ≤ K · a`.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset

variable {n h : ℕ} {ι : Type*} [DecidableEq ι]

/-- The invariant of the outer placement inside the reserve `Z`. -/
structure OuterInvA (r lam D : ℕ) (Z : Finset (Fin n)) (Rs : ι → Finset (Fin n))
    (Ts : ι → Finset (Finset (Fin n ⊕ Fin h))) (G : Finset (Finset (Fin n))) (s : Finset ι)
    (Φ : ι → Fin h → Fin n) : Prop where
  valid : ∀ i ∈ s, ValidPlacement (Rs i) (Φ i)
  range : ∀ i ∈ s, ∀ p, Φ i p ∈ Z
  disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
    Disjoint (newEdges (Ts i) (Φ i)) (newEdges (Ts j) (Φ j))
  host : ∀ i ∈ s, Disjoint (newEdges (Ts i) (Φ i)) G
  loads : ∀ J U : Finset (Fin n), U.Nonempty → J.card + U.card ≤ r - 1 →
    load Rs Φ s J U ≤ capA r lam D Z.card J.card U.card

/-- The gadgets whose vertex set contains `S` are counted by the mixed loads. -/
theorem card_cover_le_loads (R : ι → Finset (Fin n)) (Φ : ι → Fin h → Fin n) (s : Finset ι)
    (S : Finset (Fin n)) :
    (s.filter fun i => S ⊆ R i ∪ auxImage (Φ i)).card ≤
      ∑ J ∈ S.powerset, load R Φ s J (S \ J) := by
  unfold load
  refine (card_le_card ?_).trans card_biUnion_le
  intro i hi
  rw [mem_filter] at hi
  rw [mem_biUnion]
  refine ⟨S ∩ R i, mem_powerset.2 inter_subset_left, mem_filter.2 ⟨hi.1, inter_subset_right,
    ?_⟩⟩
  intro x hx
  rw [mem_sdiff, mem_inter, not_and] at hx
  rcases mem_union.1 (hi.2 hx.1) with h1 | h1
  · exact absurd h1 (hx.2 hx.1)
  · exact h1

omit [DecidableEq ι] in
/-- At the top level the sum of the mixed loads is at most `2^(r-1) λ^(r-1) D`. -/
theorem sum_loads_leA {r lam D : ℕ} (Z : Finset (Fin n)) (I : Finset ι)
    (Rs : ι → Finset (Fin n)) (Ts : ι → Finset (Finset (Fin n ⊕ Fin h)))
    (G : Finset (Finset (Fin n))) (s : Finset ι) (hsI : s ⊆ I) (Φ : ι → Fin h → Fin n)
    (hinv : OuterInvA r lam D Z Rs Ts G s Φ) (hlam : 1 ≤ lam)
    (hDeg : ∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ Rs i).card ≤ D)
    (S : Finset (Fin n)) (hS : S.card = r - 1) :
    ∑ J ∈ S.powerset, load Rs Φ s J (S \ J) ≤ 2 ^ (r - 1) * lam ^ (r - 1) * D := by
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
          unfold capA
          rw [show r - 1 - J.card - (S \ J).card = 0 by omega, pow_zero, mul_one]
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_right hlam
          omega
    _ = 2 ^ (r - 1) * (lam ^ (r - 1) * D) := by
        rw [sum_const, card_powerset, hS, smul_eq_mul]
    _ = _ := by ring

/-- The degree of the edges placed so far inside the reserve is at most `K · D`. -/
theorem deg_used_leA {r k lam D : ℕ} (Z : Finset (Fin n)) (I : Finset ι)
    (Rs : ι → Finset (Fin n)) (Ts : ι → Finset (Finset (Fin n ⊕ Fin h)))
    (G : Finset (Finset (Fin n))) (s : Finset ι) (hsI : s ⊆ I) (Φ : ι → Fin h → Fin n)
    (hinv : OuterInvA r lam D Z Rs Ts G s Φ) (hw : ∀ i ∈ I, GadgetWF r k (Rs i) (Ts i))
    (hlam : 1 ≤ lam)
    (hDeg : ∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ Rs i).card ≤ D)
    (S : Finset (Fin n)) (hS : S.card = r - 1) :
    deg (s.biUnion fun i => newEdges (Ts i) (Φ i)) S ≤
      2 ^ (k + h) * 2 ^ (r - 1) * lam ^ (r - 1) * D := by
  refine (deg_biUnion_le_loads Rs Ts Φ s (fun i hi => hw i (hsI hi)) S).trans ?_
  rw [mul_assoc (2 ^ (k + h)), mul_assoc (2 ^ (k + h))]
  apply Nat.mul_le_mul_left
  exact sum_loads_leA Z I Rs Ts G s hsI Φ hinv hlam hDeg S hS

/-- **One step of the outer placement inside the reserve.** -/
theorem outerInvA_step {r k : ℕ} (Z : Finset (Fin n)) (I : Finset ι) (Rs : ι → Finset (Fin n))
    (Ts : ι → Finset (Finset (Fin n ⊕ Fin h))) (G : Finset (Finset (Fin n))) (D : ℕ)
    (hw : ∀ i ∈ I, GadgetWF r k (Rs i) (Ts i))
    (hG : ∀ S : Finset (Fin n), S.card = r - 1 → placeC r h k * deg G S ≤ Z.card)
    (hDn : placeC r h k * D ≤ Z.card)
    (hRoot : ∀ J : Finset (Fin n), J.card ≤ r - 1 →
      (I.filter fun i => J ⊆ Rs i).card ≤ D * Z.card ^ (r - 1 - J.card))
    {s : Finset ι} (hsI : s ⊆ I) {i : ι} (hiI : i ∈ I) (his : i ∉ s) {Φ : ι → Fin h → Fin n}
    (hinv : OuterInvA r (placeLam h k) D Z Rs Ts G s Φ) :
    ∃ φ, OuterInvA r (placeLam h k) D Z Rs Ts G (insert i s) (Function.update Φ i φ) := by
  classical
  set M := placeM h k
  set lam := placeLam h k
  set K := placeK r h k
  set C := placeC r h k
  set a := Z.card
  have hlam1 : 1 ≤ lam := Nat.le_add_left _ _
  have hDeg : ∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ Rs i).card ≤ D := by
    intro S hS
    have := hRoot S hS.le
    rwa [hS, Nat.sub_self, pow_zero, mul_one] at this
  have hD : 0 < D := by
    have := hRoot ∅ (by simp)
    have hmem : i ∈ I.filter fun j => (∅ : Finset (Fin n)) ⊆ Rs j := by simp [hiI]
    have h1 := card_pos.2 ⟨i, hmem⟩
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · rw [h0, zero_mul] at this; omega
    · exact h0
  have hM := placeM_pos h k
  have hCpos : 0 < C := by unfold C placeC; positivity
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
    have := deg_used_leA Z I Rs Ts G s hsI Φ hinv hw hlam1 hDeg B hB
    simpa [K, placeK, M, placeM, lam] using this
  have hroot : ∀ J ⊆ Rs i, J.card ≤ r - 1 → load Rs Φ s J ∅ ≤ D * a ^ (r - 1 - J.card) := by
    intro J _ hJ
    refine le_trans (card_le_card ?_) (hRoot J hJ)
    intro j hj
    simp only [mem_filter] at hj ⊢
    exact ⟨hsI hj.1, hj.2.1⟩
  have hlam : 4 * 2 ^ (k + h) * h ≤ lam := Nat.le_succ _
  have hnum : 4 * (k + h + 2 ^ (k + h) * (Gd + K * D)) < 3 * a := by
    have e1 : 8 * (M * Gd) ≤ a := by
      refine le_trans ?_ hCGd
      rw [← mul_assoc]
      apply Nat.mul_le_mul_right
      unfold C placeC
      calc 8 * M = 8 * M * 1 * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e2 : 8 * (M * (K * D)) ≤ a := by
      refine le_trans ?_ hDn
      rw [← mul_assoc, ← mul_assoc]
      apply Nat.mul_le_mul_right
      unfold C placeC
      calc 8 * M * K = 8 * M * K * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e3 : 8 * (k + h + 1) ≤ a := by
      refine le_trans ?_ hCD
      unfold C placeC
      calc 8 * (k + h + 1) = 8 * 1 * 1 * (k + h + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) (by omega))
    have : 2 ^ (k + h) = M := rfl
    have hma : M * (Gd + K * D) = M * Gd + M * (K * D) := mul_add _ _ _
    rw [this, hma]
    omega
  obtain ⟨φ, hφ⟩ :=
    exists_innerInvA_univ Z Rs Φ s (Rs i) (Ts i) (hw i hiI) F hroot hF hD hlam hnum
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
      exact ⟨hφinj, fun p => hφ.avoid p (mem_univ p)⟩
    · rw [hΦ j hj]; exact hinv.valid j hj
  · intro j hj p
    rcases mem_insert.1 hj with rfl | hj
    · rw [Function.update_self]; exact hφ.range p (mem_univ p)
    · rw [hΦ j hj]; exact hinv.range j hj p
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

/-- **Partial Clique Embedding Lemma inside a reserve.**  For fixed `r`, `h`, `k` there is `C`
such that gadgets with at most `k` (and at least `r - 1`) roots anywhere in `Fin n` and `h`
auxiliary vertices can be placed with all auxiliary vertices in the reserve `Z`, by injective maps
avoiding their roots, with pairwise disjoint new edges avoiding the host `G`, and with
`Δ_{r-1}` of all new edges at most `C · D`.  Hypotheses: `C · Δ_{r-1}(G) ≤ |Z|`, `C · D ≤ |Z|`,
and every `j`-set (`j ≤ r - 1`) lies in at most `D · |Z|^(r-1-j)` root sets (and `Z ≠ ∅`, which
only matters when there is nothing to place). -/
theorem reserveCliqueEmbedding (r h k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ) {ι : Type*} [DecidableEq ι] (I : Finset ι)
      (R : ι → Finset (Fin n)) (T : ι → Finset (Finset (Fin n ⊕ Fin h)))
      (G : Finset (Finset (Fin n))) (Z : Finset (Fin n)) (D : ℕ),
      (∀ i ∈ I, GadgetWF r k (R i) (T i)) →
      (∀ S : Finset (Fin n), S.card = r - 1 → C * deg G S ≤ Z.card) →
      C * D ≤ Z.card →
      (∀ J : Finset (Fin n), J.card ≤ r - 1 →
        (I.filter fun i => J ⊆ R i).card ≤ D * Z.card ^ (r - 1 - J.card)) →
      0 < Z.card →
      ∃ Φ : ι → Fin h → Fin n,
        (∀ i ∈ I, ValidPlacement (R i) (Φ i)) ∧
        (∀ i ∈ I, ∀ p, Φ i p ∈ Z) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (newEdges (T i) (Φ i)) (newEdges (T j) (Φ j))) ∧
        (∀ i ∈ I, Disjoint (newEdges (T i) (Φ i)) G) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          deg (I.biUnion fun i => newEdges (T i) (Φ i)) S ≤ C * D) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          (I.filter fun i => S ⊆ R i ∪ auxImage (Φ i)).card ≤ C * D) := by
  refine ⟨placeC r h k, by unfold placeC; have := placeM_pos h k; positivity, ?_⟩
  intro n ι _ I R T G Z D hw hG hDn hRoot hZ
  have hDeg : ∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ R i).card ≤ D := by
    intro S hS
    have := hRoot S hS.le
    rwa [hS, Nat.sub_self, pow_zero, mul_one] at this
  obtain ⟨z₀, -⟩ := card_pos.1 hZ
  have key : ∀ s ⊆ I, ∃ Φ, OuterInvA r (placeLam h k) D Z R T G s Φ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun _ _ => z₀, ⟨by simp, by simp, by simp, by simp, ?_⟩⟩
      intro J U _ _
      simp [load]
    | insert i s his ih =>
      intro hsI
      obtain ⟨Φ, hΦ⟩ := ih ((subset_insert i s).trans hsI)
      obtain ⟨φ, hφ⟩ := outerInvA_step Z I R T G D hw hG hDn hRoot
        ((subset_insert i s).trans hsI) (hsI (mem_insert_self i s)) his hΦ
      exact ⟨_, hφ⟩
  obtain ⟨Φ, hΦ⟩ := key I subset_rfl
  refine ⟨Φ, hΦ.valid, hΦ.range, hΦ.disj, hΦ.host, fun S hS => ?_, fun S hS => ?_⟩
  · refine (deg_used_leA Z I R T G I subset_rfl Φ hΦ hw (Nat.le_add_left _ _) hDeg S hS).trans ?_
    exact Nat.mul_le_mul_right _ (placeK_le_placeC r h k)
  · refine (card_cover_le_loads R Φ I S).trans
      ((sum_loads_leA Z I R T G I subset_rfl Φ hΦ (Nat.le_add_left _ _) hDeg S hS).trans ?_)
    apply Nat.mul_le_mul_right
    refine le_trans ?_ (placeK_le_placeC r h k)
    unfold placeK
    calc 2 ^ (r - 1) * placeLam h k ^ (r - 1) = 1 * 2 ^ (r - 1) * placeLam h k ^ (r - 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (placeM_pos h k))

/-- **Root density from a degree bound, for roots inside a set `U`.**  If all root sets lie in
`U`, have at least `r - 1` vertices, and every `(r-1)`-set lies in at most `D` of them, then every
`j`-set (`j ≤ r - 1`) lies in at most `D · |U|^(r-1-j)` root sets. -/
theorem rootIncidence_of_subset {ι : Type*} {r : ℕ} (I : Finset ι) (R : ι → Finset (Fin n))
    (U : Finset (Fin n)) (D : ℕ) (hRU : ∀ i ∈ I, R i ⊆ U) (hR : ∀ i ∈ I, r - 1 ≤ (R i).card)
    (hD : ∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ R i).card ≤ D)
    (J : Finset (Fin n)) (hJ : J.card ≤ r - 1) :
    (I.filter fun i => J ⊆ R i).card ≤ D * U.card ^ (r - 1 - J.card) := by
  classical
  by_cases hJU : J ⊆ U
  · set 𝒮 := ((U \ J).powersetCard (r - 1 - J.card)).image (fun S => S ∪ J)
    have hsub : (I.filter fun i => J ⊆ R i) ⊆
        𝒮.biUnion (fun S => I.filter fun i => S ⊆ R i) := by
      intro i hi
      rw [mem_filter] at hi
      obtain ⟨S, hJS, hSR, hS⟩ := exists_subsuperset_card_eq hi.2 hJ (hR i hi.1)
      rw [mem_biUnion]
      refine ⟨S, mem_image.2 ⟨S \ J, mem_powersetCard.2 ⟨sdiff_subset_sdiff
        (hSR.trans (hRU i hi.1)) subset_rfl, by rw [card_sdiff_of_subset hJS, hS]⟩,
        sdiff_union_of_subset hJS⟩, mem_filter.2 ⟨hi.1, hSR⟩⟩
    have h𝒮 : 𝒮.card ≤ U.card ^ (r - 1 - J.card) := by
      refine card_image_le.trans ?_
      rw [card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans
        (Nat.pow_le_pow_left (card_le_card sdiff_subset) _)
    calc _ ≤ _ := card_le_card hsub
      _ ≤ ∑ S ∈ 𝒮, (I.filter fun i => S ⊆ R i).card := card_biUnion_le
      _ ≤ ∑ _S ∈ 𝒮, D := by
          apply sum_le_sum
          intro S hS
          obtain ⟨S', hS', rfl⟩ := mem_image.1 hS
          rw [mem_powersetCard] at hS'
          apply hD
          rw [card_union_of_disjoint (disjoint_of_subset_left hS'.1 sdiff_disjoint), hS'.2]
          omega
      _ = 𝒮.card * D := by rw [sum_const, smul_eq_mul]
      _ ≤ D * U.card ^ (r - 1 - J.card) := by rw [mul_comm]; exact Nat.mul_le_mul_left _ h𝒮
  · have : (I.filter fun i => J ⊆ R i) = ∅ := by
      rw [filter_eq_empty_iff]
      intro i hi hJR
      exact hJU (hJR.trans (hRU i hi))
    rw [this, card_empty]
    exact Nat.zero_le _

end RefinedAbsorption.Placement
