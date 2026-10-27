module
public import RequestProject.Placement.ClusterInner
public import RequestProject.Placement.Lemma52

/-!
# Clustered placement (Lemma 5.2 with control of piece vertex sets)

This is the variant of the Partial Clique Embedding Lemma used when the placed gadgets belong to
*pieces* (e.g. fake edges belonging to the pieces of a refiner) and the pieces must afterwards
receive absorbers of their own.  A piece `p ∈ P` has a base vertex set `V₀ p` and a set `Mem p` of
member gadgets; after placement its vertex set is `V₀ p` together with the auxiliary images of its
members (`pvOf`).  Besides the conclusions of `partialCliqueEmbedding`, the clustered lemma bounds
the `(r-1)`-degree of the family of final piece vertex sets by `C · D`, where `D` bounds the
`(r-1)`-degree of the family of base vertex sets.  This is the refinement-degree invariant that
the later placement of absorbers on the pieces requires.

The proof caps the piece loads `#{p : U ⊆ pv p}` by `μ^|U| · D · n^(r-1-|U|)` for all
`|U| ≤ r - 1` and extends a partial placement greedily (`clusterInv_step`).
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset

variable {n h : ℕ} {ι κ : Type*} [DecidableEq ι]

/-- The vertex set of the piece `p` once the gadgets in `s` are placed along `Φ`. -/
def pvOf (V₀ : κ → Finset (Fin n)) (Mem : κ → Finset ι) (Φ : ι → Fin h → Fin n)
    (s : Finset ι) (p : κ) : Finset (Fin n) :=
  V₀ p ∪ ((Mem p).filter (· ∈ s)).biUnion fun j => auxImage (Φ j)

theorem card_pvOf_le {V₀ : κ → Finset (Fin n)} {Mem : κ → Finset ι} {Φ : ι → Fin h → Fin n}
    {s : Finset ι} {p : κ} {k₀ m : ℕ} (hV : (V₀ p).card ≤ k₀) (hM : (Mem p).card ≤ m) :
    (pvOf V₀ Mem Φ s p).card ≤ k₀ + m * h := by
  unfold pvOf
  refine (card_union_le _ _).trans (Nat.add_le_add hV ?_)
  refine card_biUnion_le.trans ?_
  calc ∑ j ∈ (Mem p).filter (· ∈ s), (auxImage (Φ j)).card
      ≤ ∑ _j ∈ (Mem p).filter (· ∈ s), h := by
        apply sum_le_sum; intro j _
        exact card_image_le.trans (by simp)
    _ = ((Mem p).filter (· ∈ s)).card * h := by rw [sum_const, smul_eq_mul]
    _ ≤ m * h := Nat.mul_le_mul_right _ ((card_filter_le _ _).trans hM)

/-- The invariant of the clustered outer placement. -/
structure ClusterOuterInv (r μ D : ℕ) (Rs : ι → Finset (Fin n))
    (Ts : ι → Finset (Finset (Fin n ⊕ Fin h))) (G : Finset (Finset (Fin n))) (P : Finset κ)
    (V₀ : κ → Finset (Fin n)) (Mem : κ → Finset ι) (s : Finset ι) (Φ : ι → Fin h → Fin n) :
    Prop where
  valid : ∀ i ∈ s, ValidPlacement (Rs i) (Φ i)
  disj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
    Disjoint (newEdges (Ts i) (Φ i)) (newEdges (Ts j) (Φ j))
  host : ∀ i ∈ s, Disjoint (newEdges (Ts i) (Φ i)) G
  loads : ∀ U : Finset (Fin n), U.card ≤ r - 1 →
    pload P (pvOf V₀ Mem Φ s) U ≤ cap r μ D n ∅ U.card

/-- The degree of the placed edges is controlled by the piece loads. -/
theorem deg_used_le_pload {r k m : ℕ} (I : Finset ι) (Rs : ι → Finset (Fin n))
    (Ts : ι → Finset (Finset (Fin n ⊕ Fin h))) (P : Finset κ) (V₀ : κ → Finset (Fin n))
    (Mem : κ → Finset ι) (s : Finset ι) (hsI : s ⊆ I) (Φ : ι → Fin h → Fin n)
    (hw : ∀ i ∈ I, GadgetWF r k (Rs i) (Ts i))
    (hmemP : ∀ p ∈ P, (Mem p).card ≤ m)
    (hcover : ∀ i ∈ I, ∃ p ∈ P, i ∈ Mem p ∧ Rs i ⊆ V₀ p) (S : Finset (Fin n)) :
    deg (s.biUnion fun i => newEdges (Ts i) (Φ i)) S ≤
      2 ^ (k + h) * (m * pload P (pvOf V₀ Mem Φ s) S) := by
  classical
  unfold deg
  rw [filter_biUnion]
  calc _ ≤ ∑ i ∈ s, ((newEdges (Ts i) (Φ i)).filter (fun e => S ⊆ e)).card := card_biUnion_le
    _ ≤ ∑ i ∈ s, if S ⊆ Rs i ∪ auxImage (Φ i) then 2 ^ (k + h) else 0 := by
        apply sum_le_sum
        intro i hi
        split_ifs with hS
        · exact (card_le_card (filter_subset _ _)).trans
            (card_image_le.trans (card_template_le (hw i (hsI hi))))
        · apply le_of_eq
          rw [card_eq_zero, filter_eq_empty_iff]
          intro e he hSe
          simp only [newEdges, mem_image] at he
          obtain ⟨t, ht, rfl⟩ := he
          exact hS (hSe.trans (placeEdge_subset (hw i (hsI hi)) (Φ i) ht))
    _ = 2 ^ (k + h) * (s.filter fun i => S ⊆ Rs i ∪ auxImage (Φ i)).card := by
        rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
    _ ≤ 2 ^ (k + h) * (m * pload P (pvOf V₀ Mem Φ s) S) := by
        apply Nat.mul_le_mul_left
        have hsub : (s.filter fun i => S ⊆ Rs i ∪ auxImage (Φ i)) ⊆
            (P.filter fun p => S ⊆ pvOf V₀ Mem Φ s p).biUnion
              (fun p => (Mem p).filter (· ∈ s)) := by
          intro i hi
          rw [mem_filter] at hi
          obtain ⟨p, hp, hip, hRp⟩ := hcover i (hsI hi.1)
          rw [mem_biUnion]
          refine ⟨p, mem_filter.2 ⟨hp, ?_⟩, mem_filter.2 ⟨hip, hi.1⟩⟩
          intro x hx
          rcases mem_union.1 (hi.2 hx) with h1 | h1
          · exact mem_union_left _ (hRp h1)
          · exact mem_union_right _ (mem_biUnion.2 ⟨i, mem_filter.2 ⟨hip, hi.1⟩, h1⟩)
        refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
        calc ∑ p ∈ P.filter (fun p => S ⊆ pvOf V₀ Mem Φ s p), ((Mem p).filter (· ∈ s)).card
            ≤ ∑ _p ∈ P.filter (fun p => S ⊆ pvOf V₀ Mem Φ s p), m := by
              apply sum_le_sum; intro p hp
              exact (card_filter_le _ _).trans (hmemP p (mem_filter.1 hp).1)
          _ = m * pload P (pvOf V₀ Mem Φ s) S := by
              rw [sum_const, smul_eq_mul, mul_comm]; rfl

theorem pvOf_insert {V₀ : κ → Finset (Fin n)} {Mem : κ → Finset ι} {Φ : ι → Fin h → Fin n}
    {s : Finset ι} {i : ι} (his : i ∉ s) (φ : Fin h → Fin n) :
    pvOf V₀ Mem (Function.update Φ i φ) (insert i s) =
      pvAt Mem i (pvOf V₀ Mem Φ s) univ φ := by
  funext p
  have hΦ : ∀ j ∈ s, Function.update Φ i φ j = Φ j := fun j hj =>
    Function.update_of_ne (by rintro rfl; exact his hj) _ _
  ext x
  simp only [pvOf, pvAt, mem_union, mem_biUnion, mem_filter, mem_insert]
  split_ifs with hip
  · simp only [mem_union, mem_biUnion, mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro (hx | ⟨j, ⟨hjM, rfl | hjs⟩, hx⟩)
      · exact Or.inl (Or.inl hx)
      · rw [auxImage, Function.update_self] at hx
        exact Or.inr (by simpa using hx)
      · rw [hΦ j hjs] at hx
        exact Or.inl (Or.inr ⟨j, ⟨hjM, hjs⟩, hx⟩)
    · rintro ((hx | ⟨j, ⟨hjM, hjs⟩, hx⟩) | ⟨a, rfl⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨j, ⟨hjM, Or.inr hjs⟩, by rw [hΦ j hjs]; exact hx⟩
      · exact Or.inr ⟨i, ⟨hip, Or.inl rfl⟩, by
          rw [auxImage, Function.update_self]; exact mem_image_of_mem _ (mem_univ a)⟩
  · simp only [mem_union, mem_biUnion, mem_filter]
    constructor
    · rintro (hx | ⟨j, ⟨hjM, rfl | hjs⟩, hx⟩)
      · exact Or.inl hx
      · exact absurd hjM hip
      · rw [hΦ j hjs] at hx
        exact Or.inr ⟨j, ⟨hjM, hjs⟩, hx⟩
    · rintro (hx | ⟨j, ⟨hjM, hjs⟩, hx⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨j, ⟨hjM, Or.inr hjs⟩, by rw [hΦ j hjs]; exact hx⟩

/-- The constants of the clustered lemma. -/
def clM (h k : ℕ) : ℕ := 2 ^ (k + h)
def clPmax (h k₀ m : ℕ) : ℕ := k₀ + (m + 1) * h
def clMu (h k₀ m : ℕ) : ℕ := 8 * (m * 2 ^ clPmax h k₀ m) * clPmax h k₀ m + 2 * m + 1
def clK (r h k k₀ m : ℕ) : ℕ := clM h k * m * clMu h k₀ m ^ (r - 1) + clMu h k₀ m ^ (r - 1)
/-- The constant `C(r, h, k, k₀, m)` of the clustered placement lemma. -/
def clC (r h k k₀ m : ℕ) : ℕ := 8 * clM h k * (clK r h k k₀ m + 1) * (k + h + 1)

theorem clM_pos (h k : ℕ) : 0 < clM h k := by unfold clM; positivity

theorem le_clC (r h k k₀ m : ℕ) : clK r h k k₀ m ≤ clC r h k k₀ m := by
  unfold clC
  have := clM_pos h k
  calc clK r h k k₀ m ≤ 1 * (clK r h k k₀ m + 1) * 1 := by omega
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega)

/-- **One step of the clustered outer placement.** -/
theorem clusterOuter_step {r k k₀ m : ℕ} (I : Finset ι) (Rs : ι → Finset (Fin n))
    (Ts : ι → Finset (Finset (Fin n ⊕ Fin h))) (P : Finset κ) (V₀ : κ → Finset (Fin n))
    (Mem : κ → Finset ι) (G : Finset (Finset (Fin n))) (D : ℕ)
    (hw : ∀ i ∈ I, GadgetWF r k (Rs i) (Ts i))
    (hP : ∀ p ∈ P, (V₀ p).card ≤ k₀ ∧ r - 1 ≤ (V₀ p).card ∧ (Mem p).card ≤ m)
    (hmem : ∀ i ∈ I, (P.filter fun p => i ∈ Mem p).card ≤ m)
    (hcover : ∀ i ∈ I, ∃ p ∈ P, i ∈ Mem p ∧ Rs i ⊆ V₀ p)
    (hG : ∀ S : Finset (Fin n), S.card = r - 1 → clC r h k k₀ m * deg G S ≤ n)
    (hDn : clC r h k k₀ m * D ≤ n)
    (hDeg : ∀ S : Finset (Fin n), S.card = r - 1 → (P.filter fun p => S ⊆ V₀ p).card ≤ D)
    {s : Finset ι} (hsI : s ⊆ I) {i : ι} (hiI : i ∈ I) (his : i ∉ s) {Φ : ι → Fin h → Fin n}
    (hinv : ClusterOuterInv r (clMu h k₀ m) D Rs Ts G P V₀ Mem s Φ) :
    ∃ φ, ClusterOuterInv r (clMu h k₀ m) D Rs Ts G P V₀ Mem (insert i s)
      (Function.update Φ i φ) := by
  classical
  set M := clM h k
  set μ := clMu h k₀ m
  set K := clK r h k k₀ m
  set C := clC r h k k₀ m
  set Pmax := clPmax h k₀ m
  have hμ0 : 0 < μ := Nat.succ_pos _
  have hrootP := rootIncidence P V₀ D (fun p hp => (hP p hp).2.1) hDeg
  have hD : 0 < D := by
    obtain ⟨p, hp, -, -⟩ := hcover i hiI
    have := hrootP ∅ (by simp)
    have hmem' : p ∈ P.filter fun q => (∅ : Finset (Fin n)) ⊆ V₀ q := by simp [hp]
    have h1 := card_pos.2 ⟨p, hmem'⟩
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · rw [h0, zero_mul] at this; omega
    · exact h0
  have hM := clM_pos h k
  have hCpos : 0 < C := by unfold C clC; positivity
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
    have h1 := deg_used_le_pload I Rs Ts P V₀ Mem s hsI Φ hw (fun p hp => (hP p hp).2.2)
      hcover B
    have h2 := hinv.loads B (by omega)
    have h3 : cap r μ D n ∅ B.card = μ ^ (r - 1) * D := by
      simp [cap, hB]
    calc deg used B ≤ M * (m * pload P (pvOf V₀ Mem Φ s) B) := h1
      _ ≤ M * (m * (μ ^ (r - 1) * D)) := by rw [← h3]; gcongr
      _ = (M * m * μ ^ (r - 1)) * D := by ring
      _ ≤ K * D := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hnum : 4 * (k + h + 2 ^ (k + h) * (Gd + K * D)) < 3 * n := by
    have e1 : 8 * (M * Gd) ≤ n := by
      refine le_trans ?_ hCGd
      rw [← mul_assoc]
      apply Nat.mul_le_mul_right
      unfold C clC
      calc 8 * M = 8 * M * 1 * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e2 : 8 * (M * (K * D)) ≤ n := by
      refine le_trans ?_ hDn
      rw [← mul_assoc, ← mul_assoc]
      apply Nat.mul_le_mul_right
      unfold C clC
      calc 8 * M * K = 8 * M * K * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have e3 : 8 * (k + h + 1) ≤ n := by
      refine le_trans ?_ hCD
      unfold C clC
      calc 8 * (k + h + 1) = 8 * 1 * 1 * (k + h + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) (by omega))
    have : 2 ^ (k + h) = M := rfl
    have hma : M * (Gd + K * D) = M * Gd + M * (K * D) := mul_add _ _ _
    rw [this, hma]
    omega
  have hsize : ∀ q ∈ P, (pvOf V₀ Mem Φ s q).card + h ≤ Pmax := by
    intro q hq
    have := card_pvOf_le (Φ := Φ) (s := s) (hP q hq).1 (hP q hq).2.2
    simp only [Pmax, clPmax]
    nlinarith
  have hμ : 2 * m ≤ μ := by simp only [μ, clMu]; omega
  have hμ2 : 8 * (m * 2 ^ Pmax) * Pmax ≤ μ := by simp only [μ, clMu, Pmax]; omega
  -- inner placement
  have key : ∀ A : Finset (Fin h), ∃ φ,
      ClusterInv r μ D P Mem i (pvOf V₀ Mem Φ s) (Rs i) (Ts i) F A φ := by
    have hn : 0 < n := by omega
    intro A
    induction A using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => ⟨0, hn⟩, by simp, by simp, ?_, ?_⟩
      · intro U hU
        have : pvAt Mem i (pvOf V₀ Mem Φ s) (∅ : Finset (Fin h)) (fun _ => (⟨0, hn⟩ : Fin n)) =
            pvOf V₀ Mem Φ s := by
          funext q; simp [pvAt]
        rw [this]; exact hinv.loads U hU
      · intro t ht hA
        obtain ⟨p, hp⟩ := (hw i hiI).edge_aux t ht
        exact absurd (hA p hp) (by simp)
    | insert p A hp ih =>
      obtain ⟨φ, hφ⟩ := ih
      exact ⟨_, (clusterInv_step P Mem i (pvOf V₀ Mem Φ s) (Rs i) (Ts i) (hw i hiI) F
        (hmem i hiI) hsize hF hD hμ0 hμ hμ2 hnum hφ hp).choose_spec⟩
  obtain ⟨φ, hφ⟩ := key univ
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
  · intro U hU
    rw [pvOf_insert his φ]
    exact hφ.loads U hU

/-- **Clustered Partial Clique Embedding Lemma.**  For fixed `r, h, k, k₀, m` there is `C` such
that gadgets (as in `partialCliqueEmbedding`) grouped into pieces — each piece with a base vertex
set of between `r - 1` and `k₀` vertices and at most `m` members, every gadget in at most `m`
pieces and covered by a piece whose base contains its roots — can be placed so that the new edges
are pairwise disjoint and avoid `G`, the union of new edges has `(r-1)`-degree at most `C · D`,
and the final piece vertex sets `pvOf V₀ Mem Φ I p` have `(r-1)`-degree at most `C · D`, where `D`
bounds the `(r-1)`-degree of the base vertex sets. -/
theorem clusteredPlacement (r h k k₀ m : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ) {ι κ : Type*} [DecidableEq ι] (I : Finset ι)
      (R : ι → Finset (Fin n)) (T : ι → Finset (Finset (Fin n ⊕ Fin h)))
      (P : Finset κ) (V₀ : κ → Finset (Fin n)) (Mem : κ → Finset ι)
      (G : Finset (Finset (Fin n))) (D : ℕ),
      (∀ i ∈ I, GadgetWF r k (R i) (T i)) →
      (∀ p ∈ P, (V₀ p).card ≤ k₀ ∧ r - 1 ≤ (V₀ p).card ∧ (Mem p).card ≤ m) →
      (∀ i ∈ I, (P.filter fun p => i ∈ Mem p).card ≤ m) →
      (∀ i ∈ I, ∃ p ∈ P, i ∈ Mem p ∧ R i ⊆ V₀ p) →
      (∀ S : Finset (Fin n), S.card = r - 1 → C * deg G S ≤ n) →
      (∀ S : Finset (Fin n), S.card = r - 1 → (P.filter fun p => S ⊆ V₀ p).card ≤ D) →
      C * D ≤ n → 0 < n →
      ∃ Φ : ι → Fin h → Fin n,
        (∀ i ∈ I, ValidPlacement (R i) (Φ i)) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (newEdges (T i) (Φ i)) (newEdges (T j) (Φ j))) ∧
        (∀ i ∈ I, Disjoint (newEdges (T i) (Φ i)) G) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          deg (I.biUnion fun i => newEdges (T i) (Φ i)) S ≤ C * D) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          (P.filter fun p => S ⊆ pvOf V₀ Mem Φ I p).card ≤ C * D) := by
  refine ⟨clC r h k k₀ m, by unfold clC; have := clM_pos h k; positivity, ?_⟩
  intro n ι κ _ I R T P V₀ Mem G D hw hP hmem hcover hG hDeg hDn hn
  have hrootP := rootIncidence P V₀ D (fun p hp => (hP p hp).2.1) hDeg
  have key : ∀ s ⊆ I, ∃ Φ, ClusterOuterInv r (clMu h k₀ m) D R T G P V₀ Mem s Φ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun _ _ => ⟨0, hn⟩, ⟨by simp, by simp, by simp, ?_⟩⟩
      intro U hU
      have hpv : pvOf V₀ Mem (fun (_ : ι) (_ : Fin h) => (⟨0, hn⟩ : Fin n)) ∅ = V₀ := by
        funext p; simp [pvOf]
      rw [hpv]
      refine (hrootP U hU).trans ?_
      simp only [cap, card_empty, Nat.sub_zero]
      exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by
        have : 0 < clMu h k₀ m := Nat.succ_pos _
        positivity))
    | insert i s his ih =>
      intro hsI
      obtain ⟨Φ, hΦ⟩ := ih ((subset_insert i s).trans hsI)
      obtain ⟨φ, hφ⟩ := clusterOuter_step I R T P V₀ Mem G D hw hP hmem hcover hG hDn hDeg
        ((subset_insert i s).trans hsI) (hsI (mem_insert_self i s)) his hΦ
      exact ⟨_, hφ⟩
  obtain ⟨Φ, hΦ⟩ := key I subset_rfl
  have hcapS : ∀ S : Finset (Fin n), S.card = r - 1 →
      pload P (pvOf V₀ Mem Φ I) S ≤ clMu h k₀ m ^ (r - 1) * D := by
    intro S hS
    have := hΦ.loads S hS.le
    simpa [cap, hS] using this
  refine ⟨Φ, hΦ.valid, hΦ.disj, hΦ.host, fun S hS => ?_, fun S hS => ?_⟩
  · refine (deg_used_le_pload I R T P V₀ Mem I subset_rfl Φ hw (fun p hp => (hP p hp).2.2)
      hcover S).trans ?_
    calc clM h k * (m * pload P (pvOf V₀ Mem Φ I) S)
        ≤ clM h k * (m * (clMu h k₀ m ^ (r - 1) * D)) := by gcongr; exact hcapS S hS
      _ = (clM h k * m * clMu h k₀ m ^ (r - 1)) * D := by ring
      _ ≤ clK r h k k₀ m * D := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ clC r h k k₀ m * D := Nat.mul_le_mul_right _ (le_clC r h k k₀ m)
  · calc (P.filter fun p => S ⊆ pvOf V₀ Mem Φ I p).card = pload P (pvOf V₀ Mem Φ I) S := rfl
      _ ≤ clMu h k₀ m ^ (r - 1) * D := hcapS S hS
      _ ≤ clK r h k k₀ m * D := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
      _ ≤ clC r h k k₀ m * D := Nat.mul_le_mul_right _ (le_clC r h k k₀ m)

end RefinedAbsorption.Placement
