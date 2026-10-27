module
public import RequestProject.Pending.SafeInner

/-!
# The Partial Clique Embedding Lemma with a packing-type safety condition

`safePartialCliqueEmbedding`: the Partial Clique Embedding Lemma (Lemma 5.2 of Delcourt–Postle,
`RefinedAbsorption.Placement.partialCliqueEmbedding`) with the additional output that, for a
prescribed family `𝓢` of vertex sets in which every set `T` has at most `b` one-vertex extensions
`insert v T ∈ 𝓢`, no member of `𝓢` lies inside `roots ∪ auxiliary image` of a gadget unless it
lies inside the roots.  The proof is the same greedy argument; at every vertex step at most
`2^(k+h) b` further vertices are excluded (`innerInv_step_avoid`).
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset RefinedAbsorption.Placement

variable {n h : ℕ} {ι : Type*}

/-- No member of `𝓢` inside `R ∪ φ(A)` except inside `R`. -/
def SafeFor (𝓢 : Finset (Finset (Fin n))) (R : Finset (Fin n)) (φ : Fin h → Fin n)
    (A : Finset (Fin h)) : Prop :=
  ∀ S ∈ 𝓢, S ⊆ R ∪ A.image φ → S ⊆ R

/-- The vertices excluded by `𝓢` when extending `R ∪ φ(A)`. -/
def dangerSet (𝓢 : Finset (Finset (Fin n))) (B : Finset (Fin n)) : Finset (Fin n) :=
  B.powerset.biUnion fun T => univ.filter fun v => v ∉ T ∧ insert v T ∈ 𝓢

theorem card_dangerSet_le (𝓢 : Finset (Finset (Fin n))) (B : Finset (Fin n)) {b : ℕ}
    (hb : ∀ T : Finset (Fin n), (univ.filter fun v => v ∉ T ∧ insert v T ∈ 𝓢).card ≤ b) :
    (dangerSet 𝓢 B).card ≤ 2 ^ B.card * b := by
  unfold dangerSet
  refine card_biUnion_le.trans ?_
  calc ∑ T ∈ B.powerset, (univ.filter fun v => v ∉ T ∧ insert v T ∈ 𝓢).card
      ≤ ∑ _T ∈ B.powerset, b := sum_le_sum fun T _ => hb T
    _ = 2 ^ B.card * b := by rw [sum_const, card_powerset, smul_eq_mul]

theorem safeFor_empty (𝓢 : Finset (Finset (Fin n))) (R : Finset (Fin n)) (φ : Fin h → Fin n) :
    SafeFor 𝓢 R φ ∅ := by
  intro S _ hS
  simpa using hS

theorem safeFor_insert {𝓢 : Finset (Finset (Fin n))} {R : Finset (Fin n)} {φ : Fin h → Fin n}
    {A : Finset (Fin h)} {p : Fin h} (hp : p ∉ A) (hs : SafeFor 𝓢 R φ A) {v : Fin n}
    (hv : v ∉ dangerSet 𝓢 (R ∪ A.image φ)) :
    SafeFor 𝓢 R (Function.update φ p v) (insert p A) := by
  intro S hS hsub
  have himg : (insert p A).image (Function.update φ p v) = insert v (A.image φ) := by
    rw [image_insert, Function.update_self, image_update_of_not_mem hp]
  rw [himg] at hsub
  by_cases hvS : v ∈ S
  · exfalso
    apply hv
    unfold dangerSet
    refine mem_biUnion.2 ⟨S.erase v, mem_powerset.2 ?_, mem_filter.2 ⟨mem_univ _,
      notMem_erase v S, by rw [insert_erase hvS]; exact hS⟩⟩
    intro x hx
    have hxS := mem_of_mem_erase hx
    have hxv := ne_of_mem_erase hx
    rcases mem_union.1 (hsub hxS) with h1 | h1
    · exact mem_union_left _ h1
    · rcases mem_insert.1 h1 with h2 | h2
      · exact absurd h2 hxv
      · exact mem_union_right _ h2
  · apply hs S hS
    intro x hx
    rcases mem_union.1 (hsub hx) with h1 | h1
    · exact mem_union_left _ h1
    · rcases mem_insert.1 h1 with h2 | h2
      · exact absurd (h2 ▸ hx) hvS
      · exact mem_union_right _ h2

/-- Running the safe inner placement over all auxiliary positions. -/
theorem exists_innerInv_univ_safe {r k lam D Fdeg b : ℕ} (Rs : ι → Finset (Fin n))
    (Φ : ι → Fin h → Fin n) (s : Finset ι) (R : Finset (Fin n))
    (T : Finset (Finset (Fin n ⊕ Fin h))) (hw : GadgetWF r k R T) (F : Finset (Finset (Fin n)))
    (hroot : ∀ J ⊆ R, J.card ≤ r - 1 → load Rs Φ s J ∅ ≤ D * n ^ (r - 1 - J.card))
    (hF : ∀ B : Finset (Fin n), B.card = r - 1 → deg F B ≤ Fdeg)
    (hD : 0 < D) (hlam : 4 * 2 ^ (k + h) * h ≤ lam) (𝓢 : Finset (Finset (Fin n)))
    (hb : ∀ T : Finset (Fin n), (univ.filter fun v => v ∉ T ∧ insert v T ∈ 𝓢).card ≤ b)
    (hnum : 4 * (k + h + 2 ^ (k + h) * Fdeg + 2 ^ (k + h) * b) < 3 * n) :
    ∃ φ, InnerInv r lam D Rs Φ s R T F univ φ ∧ SafeFor 𝓢 R φ univ := by
  have hn : 0 < n := by omega
  have key : ∀ A : Finset (Fin h), ∃ φ, InnerInv r lam D Rs Φ s R T F A φ ∧ SafeFor 𝓢 R φ A := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨fun _ => ⟨0, hn⟩, innerInv_empty r lam D Rs Φ s R T hw F _,
        safeFor_empty 𝓢 R _⟩
    | insert p A hp ih =>
      obtain ⟨φ, hφ, hsφ⟩ := ih
      have hcardB : (R ∪ A.image φ).card ≤ k + h :=
        (card_union_le _ _).trans (Nat.add_le_add hw.roots_le
          (card_image_le.trans ((card_le_univ A).trans (by simp))))
      have hB4 : (dangerSet 𝓢 (R ∪ A.image φ)).card ≤ 2 ^ (k + h) * b :=
        (card_dangerSet_le 𝓢 _ hb).trans (Nat.mul_le_mul_right _
          (Nat.pow_le_pow_right (by norm_num) hcardB))
      obtain ⟨v, hv, hinv⟩ := innerInv_step_avoid Rs Φ s R T hw F hroot hF hD hlam
        (dangerSet 𝓢 (R ∪ A.image φ)) (by omega) hφ hp
      exact ⟨_, hinv, safeFor_insert hp hsφ hv⟩
  exact key univ

variable [DecidableEq ι] in
/-- **One step of the outer placement**: one more gadget is placed. -/
theorem outerInv_step_safe {r k b : ℕ} (I : Finset ι) (Rs : ι → Finset (Fin n))
    (Ts : ι → Finset (Finset (Fin n ⊕ Fin h))) (G : Finset (Finset (Fin n))) (D : ℕ)
    (hw : ∀ i ∈ I, GadgetWF r k (Rs i) (Ts i))
    (hG : ∀ S : Finset (Fin n), S.card = r - 1 → placeC r h k * deg G S ≤ n)
    (hDn : placeC r h k * D ≤ n) (𝓢 : Finset (Finset (Fin n)))
    (hb : ∀ T : Finset (Fin n), (univ.filter fun v => v ∉ T ∧ insert v T ∈ 𝓢).card ≤ b)
    (hbn : placeC r h k * b ≤ n)
    (hDeg : ∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ Rs i).card ≤ D)
    {s : Finset ι} (hsI : s ⊆ I) {i : ι} (hiI : i ∈ I) (his : i ∉ s) {Φ : ι → Fin h → Fin n}
    (hinv : OuterInv r (placeLam h k) D Rs Ts G s Φ)
    (hsafe : ∀ j ∈ s, SafeFor 𝓢 (Rs j) (Φ j) univ) :
    ∃ φ, OuterInv r (placeLam h k) D Rs Ts G (insert i s) (Function.update Φ i φ) ∧
      ∀ j ∈ insert i s, SafeFor 𝓢 (Rs j) (Function.update Φ i φ j) univ := by
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
  have hnum : 4 * (k + h + 2 ^ (k + h) * (Gd + K * D) + 2 ^ (k + h) * b) < 3 * n := by
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
    have e4 : 8 * (M * b) ≤ n := by
      refine le_trans ?_ hbn
      rw [← mul_assoc]
      apply Nat.mul_le_mul_right
      unfold C placeC
      calc 8 * M = 8 * M * 1 * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have : 2 ^ (k + h) = M := rfl
    have hma : M * (Gd + K * D) = M * Gd + M * (K * D) := mul_add _ _ _
    rw [this, hma]
    omega
  obtain ⟨φ, hφ, hφsafe⟩ := exists_innerInv_univ_safe Rs Φ s (Rs i) (Ts i) (hw i hiI) F hroot hF hD
    hlam 𝓢 hb hnum
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
  refine ⟨φ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
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
  · intro j hj
    rcases mem_insert.1 hj with rfl | hj
    · rw [Function.update_self]; exact hφsafe
    · rw [hΦ j hj]; exact hsafe j hj

/-- **Partial Clique Embedding Lemma with safety.** -/
theorem safePartialCliqueEmbedding (r h k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ) {ι : Type*} [DecidableEq ι] (I : Finset ι)
      (R : ι → Finset (Fin n)) (T : ι → Finset (Finset (Fin n ⊕ Fin h)))
      (G : Finset (Finset (Fin n))) (D b : ℕ) (𝓢 : Finset (Finset (Fin n))),
      (∀ i ∈ I, GadgetWF r k (R i) (T i)) →
      (∀ S : Finset (Fin n), S.card = r - 1 → C * deg G S ≤ n) →
      C * D ≤ n →
      (∀ S : Finset (Fin n), S.card = r - 1 → (I.filter fun i => S ⊆ R i).card ≤ D) →
      (∀ T : Finset (Fin n), (univ.filter fun v => v ∉ T ∧ insert v T ∈ 𝓢).card ≤ b) →
      C * b ≤ n → 0 < n →
      ∃ Φ : ι → Fin h → Fin n,
        (∀ i ∈ I, ValidPlacement (R i) (Φ i)) ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (newEdges (T i) (Φ i)) (newEdges (T j) (Φ j))) ∧
        (∀ i ∈ I, Disjoint (newEdges (T i) (Φ i)) G) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 →
          deg (I.biUnion fun i => newEdges (T i) (Φ i)) S ≤ C * D) ∧
        (∀ i ∈ I, ∀ S ∈ 𝓢, S ⊆ R i ∪ auxImage (Φ i) → S ⊆ R i) := by
  refine ⟨placeC r h k, by unfold placeC; have := placeM_pos h k; positivity, ?_⟩
  intro n ι _ I R T G D b 𝓢 hw hG hDn hDeg hb hbn hn
  have key : ∀ s ⊆ I, ∃ Φ, OuterInv r (placeLam h k) D R T G s Φ ∧
      ∀ j ∈ s, SafeFor 𝓢 (R j) (Φ j) univ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun _ _ => ⟨0, hn⟩, ⟨by simp, by simp, by simp, ?_⟩, by simp⟩
      intro J U _ _
      simp [load]
    | insert i s his ih =>
      intro hsI
      obtain ⟨Φ, hΦ, hsΦ⟩ := ih ((subset_insert i s).trans hsI)
      obtain ⟨φ, hφ, hsφ⟩ := outerInv_step_safe I R T G D hw hG hDn 𝓢 hb hbn hDeg
        ((subset_insert i s).trans hsI) (hsI (mem_insert_self i s)) his hΦ hsΦ
      exact ⟨_, hφ, hsφ⟩
  obtain ⟨Φ, hΦ, hsΦ⟩ := key I subset_rfl
  refine ⟨Φ, hΦ.valid, hΦ.disj, hΦ.host, fun S hS => ?_, fun i hi S hS hsub => ?_⟩
  · refine (deg_used_le I R T G I subset_rfl Φ hΦ hw (Nat.le_add_left _ _) hDeg S hS).trans ?_
    exact Nat.mul_le_mul_right _ (placeK_le_placeC r h k)
  · exact hsΦ i hi S hS (by simpa [auxImage] using hsub)

end RefinedAbsorption.Pending
