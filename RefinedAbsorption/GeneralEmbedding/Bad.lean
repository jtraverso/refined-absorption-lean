module
public import RefinedAbsorption.GeneralEmbedding.Step

/-!
# Counting the bad embeddings of one supergraph
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {n r C : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {ends : ι → Finset (Fin n)} {ℋ : Finset (Finset ι)} {m : Finset ι → ℕ}
  {W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))}

/-- Embeddings reusing a new edge already used by `φ` on `𝒮`. -/
noncomputable def bad1Set (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))
    (𝒮 : Finset (Finset ι)) (φ : (H : Finset ι) → Fin (m H) → Fin n) (H : Finset ι) :
    Finset (Fin (m H) → Fin n) :=
  ((W H).filter (fun e => e.toRight.Nonempty)).biUnion (fun e =>
    ((newPairs W 𝒮).filter (fun p => e.toLeft ⊆ pimg φ p)).biUnion (fun p =>
      univ.filter (fun f : Fin (m H) → Fin n => ∀ i ∈ e.toRight, f i ∈ pimg φ p \ e.toLeft)))

/-- Embeddings putting a new edge through a nearly saturated set. -/
noncomputable def bad2Set (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))
    (𝒮 : Finset (Finset ι)) (φ : (H : Finset ι) → Fin (m H) → Fin n) (Q D : ℝ) (C r : ℕ)
    (H : Finset ι) : Finset (Fin (m H) → Fin n) :=
  ((W H).filter (fun e => e.toRight.Nonempty)).biUnion (fun e =>
    e.toLeft.powerset.biUnion (fun A' =>
      (e.toRight.powerset.filter (fun B' => B'.Nonempty)).biUnion (fun B' =>
        (satSets W 𝒮 φ Q D C r A' B'.card).biUnion (fun T =>
          univ.filter (fun f : Fin (m H) → Fin n => ∀ i ∈ B', f i ∈ T)))))

theorem card_bad1_le {Q D C' γ : ℝ} (hγ : 0 < γ) (hQ : 1 ≤ Q) (hD0 : 0 ≤ D) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hends : ∀ x, (ends x).card = r)
    (hdeg : ∀ S : Finset (Fin n), S.card + 1 = r →
      ((univ.filter (fun x => S ⊆ ends x)).card : ℝ) ≤ D)
    (href : IsCRefinedFamily C ℋ) (hint : IsEdgeIntersecting ends ℋ m W)
    (hunif : ∀ H ∈ ℋ, ∀ e ∈ W H, e.card = r)
    (hbd : ∀ H ∈ ℋ, (W H).card ≤ C) {𝒮 : Finset (Finset ι)} (h𝒮 : 𝒮 ⊆ ℋ)
    {φ : (H : Finset ι) → Fin (m H) → Fin n}
    (hacc : ∀ A : Finset (Fin n), A.card + 1 ≤ r →
      (accDeg W 𝒮 φ A : ℝ) ≤ thr Q ((C : ℝ) ^ 2) D n r A.card)
    (hC'0 : 0 < C') (hDn : D ≤ n / C')
    (hC' : 4 * (C * ((C : ℝ) ^ 2 + Kseq Q ((C : ℝ) ^ 2) (r - 1)) * (r : ℝ) ^ r) ≤ γ * C')
    {H : Finset ι} (hH : H ∈ ℋ) :
    ((bad1Set W 𝒮 φ H).card : ℝ) ≤ γ * (n : ℝ) ^ (m H) / 4 := by
  classical
  set c2 : ℝ := (C : ℝ) ^ 2 with hc2
  set K := Kseq Q c2 with hK
  have hc20 : 0 ≤ c2 := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set Wn := (W H).filter (fun e => e.toRight.Nonempty) with hWn
  rcases Wn.eq_empty_or_nonempty with hWe | ⟨e₀, he₀⟩
  · unfold bad1Set; rw [← hWn, hWe, biUnion_empty, card_empty, Nat.cast_zero]; positivity
  have hm1 : 1 ≤ m H := by
    obtain ⟨i, _⟩ := (mem_filter.1 he₀).2
    exact Nat.one_le_iff_ne_zero.2 (fun h => by have := i.2; omega)
  -- the bound for one edge
  set X : ℝ := (c2 + K (r - 1)) * (r : ℝ) ^ r * (D * (n : ℝ) ^ (m H - 1)) with hX
  have hX0 : 0 ≤ X := by
    have := Kseq_nonneg (Q := Q) (c := c2) (by linarith) hc20 (r - 1)
    positivity
  have hedge : ∀ e ∈ Wn, ((((newPairs W 𝒮).filter (fun p => e.toLeft ⊆ pimg φ p)).biUnion
      (fun p => univ.filter (fun f : Fin (m H) → Fin n =>
        ∀ i ∈ e.toRight, f i ∈ pimg φ p \ e.toLeft))).card : ℝ) ≤ X := by
    intro e he
    obtain ⟨heW, hne⟩ := mem_filter.1 he
    have hcard := card_toLeft_add_card_toRight (u := e)
    rw [hunif H hH e heW] at hcard
    set b := e.toRight.card with hb
    have hb1 : 1 ≤ b := card_pos.2 hne
    have hbm : b ≤ m H := by
      have := card_le_univ e.toRight; rwa [Fintype.card_fin] at this
    have hRr : e.toLeft.card + 1 ≤ r := by omega
    have hterm : ∀ p ∈ (newPairs W 𝒮).filter (fun p => e.toLeft ⊆ pimg φ p),
        ((univ.filter (fun f : Fin (m H) → Fin n =>
          ∀ i ∈ e.toRight, f i ∈ pimg φ p \ e.toLeft)).card : ℝ) ≤
          (r : ℝ) ^ r * (n : ℝ) ^ (m H - b) := by
      intro p hp
      rw [card_fun_mem]
      push_cast
      have hp1 := (mem_filter.1 hp).1
      obtain ⟨hpH, hpe⟩ := mem_sigma.1 (mem_filter.1 hp1).1
      have h1 : ((pimg φ p \ e.toLeft).card : ℝ) ≤ r := by
        have := (card_le_card (sdiff_subset (s := pimg φ p) (t := e.toLeft))).trans
          ((card_embedEdge_le _ _).trans (hunif p.1 (h𝒮 hpH) p.2 hpe).le)
        exact_mod_cast this
      have h2 : ((pimg φ p \ e.toLeft).card : ℝ) ^ b ≤ (r : ℝ) ^ r :=
        (pow_le_pow_left₀ (Nat.cast_nonneg _) h1 b).trans
          (pow_le_pow_right₀ hr1 (by omega))
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have htot := totDeg_bound hD0 hends hdeg href hint hbd h𝒮 hacc e.toLeft hRr
    have hK : K e.toLeft.card ≤ K (r - 1) := Kseq_mono hQ hc20 (by omega)
    have hexp : r - 1 - e.toLeft.card = b - 1 := by omega
    rw [hexp] at htot
    calc _ ≤ ∑ p ∈ (newPairs W 𝒮).filter (fun p => e.toLeft ⊆ pimg φ p),
          ((univ.filter (fun f : Fin (m H) → Fin n =>
            ∀ i ∈ e.toRight, f i ∈ pimg φ p \ e.toLeft)).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ p ∈ (newPairs W 𝒮).filter (fun p => e.toLeft ⊆ pimg φ p),
          (r : ℝ) ^ r * (n : ℝ) ^ (m H - b) := sum_le_sum hterm
      _ = (totDeg W 𝒮 φ e.toLeft : ℝ) * ((r : ℝ) ^ r * (n : ℝ) ^ (m H - b)) := by
          rw [sum_const, nsmul_eq_mul]; rfl
      _ ≤ ((c2 + K e.toLeft.card) * D * (n : ℝ) ^ (b - 1)) *
          ((r : ℝ) ^ r * (n : ℝ) ^ (m H - b)) := by gcongr
      _ ≤ ((c2 + K (r - 1)) * D * (n : ℝ) ^ (b - 1)) *
          ((r : ℝ) ^ r * (n : ℝ) ^ (m H - b)) := by gcongr
      _ = X := by
          rw [hX]
          have : (n : ℝ) ^ (b - 1) * (n : ℝ) ^ (m H - b) = (n : ℝ) ^ (m H - 1) := by
            rw [← pow_add]; congr 1; omega
          rw [← this]; ring
  have hWn_card : (Wn.card : ℝ) ≤ C := by
    exact_mod_cast (card_le_card (filter_subset _ _)).trans (hbd H hH)
  have hfinal : (C : ℝ) * X ≤ γ * (n : ℝ) ^ (m H) / 4 := by
    have hDn' : D * (n : ℝ) ^ (m H - 1) ≤ (n : ℝ) ^ (m H) / C' := by
      have e1 : (n : ℝ) ^ (m H) = n * (n : ℝ) ^ (m H - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e1, le_div_iff₀ hC'0]
      have h := (le_div_iff₀ hC'0).1 hDn
      have hp : 0 ≤ (n : ℝ) ^ (m H - 1) := by positivity
      nlinarith
    have hP : 0 ≤ (c2 + K (r - 1)) * (r : ℝ) ^ r := by
      have := Kseq_nonneg (Q := Q) (c := c2) (by linarith) hc20 (r - 1)
      positivity
    have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
    have hnm : 0 ≤ (n : ℝ) ^ (m H) := by positivity
    calc (C : ℝ) * X = C * ((c2 + K (r - 1)) * (r : ℝ) ^ r) * (D * (n : ℝ) ^ (m H - 1)) := by
          rw [hX]; ring
      _ ≤ C * ((c2 + K (r - 1)) * (r : ℝ) ^ r) * ((n : ℝ) ^ (m H) / C') := by gcongr
      _ = (4 * (C * (c2 + K (r - 1)) * (r : ℝ) ^ r)) * (n : ℝ) ^ (m H) / (4 * C') := by
          field_simp
      _ ≤ (γ * C') * (n : ℝ) ^ (m H) / (4 * C') := by gcongr
      _ = γ * (n : ℝ) ^ (m H) / 4 := by field_simp
  unfold bad1Set
  rw [← hWn]
  calc _ ≤ ∑ e ∈ Wn, ((((newPairs W 𝒮).filter (fun p => e.toLeft ⊆ pimg φ p)).biUnion
        (fun p => univ.filter (fun f : Fin (m H) → Fin n =>
          ∀ i ∈ e.toRight, f i ∈ pimg φ p \ e.toLeft))).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ e ∈ Wn, X := sum_le_sum hedge
    _ = Wn.card * X := by rw [sum_const, nsmul_eq_mul]
    _ ≤ C * X := mul_le_mul_of_nonneg_right hWn_card hX0
    _ ≤ _ := hfinal

theorem card_bad2_le {Q D γ : ℝ} (hγ : 0 < γ) (hQ : 2 ≤ Q) (hD1 : 1 ≤ D) (hn : 1 ≤ n)
    (hr : 1 ≤ r) (hC1 : 1 ≤ C)
    (hends : ∀ x, (ends x).card = r)
    (hdeg : ∀ S : Finset (Fin n), S.card + 1 = r →
      ((univ.filter (fun x => S ⊆ ends x)).card : ℝ) ≤ D)
    (href : IsCRefinedFamily C ℋ) (hint : IsEdgeIntersecting ends ℋ m W)
    (hunif : ∀ H ∈ ℋ, ∀ e ∈ W H, e.card = r)
    (hbd : ∀ H ∈ ℋ, (W H).card ≤ C) {𝒮 : Finset (Finset ι)} (h𝒮 : 𝒮 ⊆ ℋ)
    {φ : (H : Finset ι) → Fin (m H) → Fin n}
    (hacc : ∀ A : Finset (Fin n), A.card + 1 ≤ r →
      (accDeg W 𝒮 φ A : ℝ) ≤ thr Q ((C : ℝ) ^ 2) D n r A.card)
    (hQγ : 4 * (C * 2 ^ (3 * r + 1) * (r : ℝ) ^ r) ≤ γ * Q)
    {H : Finset ι} (hH : H ∈ ℋ) :
    ((bad2Set W 𝒮 φ Q D C r H).card : ℝ) ≤ γ * (n : ℝ) ^ (m H) / 4 := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hQ0 : 0 < Q := by linarith
  set Wn := (W H).filter (fun e => e.toRight.Nonempty) with hWn
  set Y : ℝ := 2 ^ (r + 1) * (r : ℝ) ^ r / Q * (n : ℝ) ^ (m H) with hY
  have hY0 : 0 ≤ Y := by positivity
  -- one triple `(e, A', B')`
  have hinner : ∀ e ∈ Wn, ∀ A' : Finset (Fin n), ∀ B' ∈ e.toRight.powerset.filter
      (fun B' => B'.Nonempty), (((satSets W 𝒮 φ Q D C r A' B'.card).biUnion (fun T =>
        univ.filter (fun f : Fin (m H) → Fin n => ∀ i ∈ B', f i ∈ T))).card : ℝ) ≤ Y := by
    intro e he A' B' hB'
    obtain ⟨heW, _⟩ := mem_filter.1 he
    obtain ⟨hB'sub, hB'ne⟩ := mem_filter.1 hB'
    rw [mem_powerset] at hB'sub
    set b := B'.card with hb
    have hb1 : 1 ≤ b := card_pos.2 hB'ne
    have hbm : b ≤ m H := by
      have := card_le_univ B'; rwa [Fintype.card_fin] at this
    have hbr : b ≤ r := by
      have h1 := card_le_card hB'sub
      have h2 := card_toLeft_add_card_toRight (u := e)
      rw [hunif H hH e heW] at h2
      omega
    have hsat := card_satSets_le hQ hD1 hn hC1 hends hdeg href hint hunif hbd h𝒮 hacc A' hb1
    calc _ ≤ ∑ T ∈ satSets W 𝒮 φ Q D C r A' b,
          ((univ.filter (fun f : Fin (m H) → Fin n => ∀ i ∈ B', f i ∈ T)).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ = ∑ T ∈ satSets W 𝒮 φ Q D C r A' b, (b : ℝ) ^ b * (n : ℝ) ^ (m H - b) := by
          refine sum_congr rfl fun T hT => ?_
          rw [card_fun_mem]
          have hTc := (mem_powersetCard.1 (mem_filter.1 hT).1).2
          rw [hTc]; push_cast; rfl
      _ = (satSets W 𝒮 φ Q D C r A' b).card * ((b : ℝ) ^ b * (n : ℝ) ^ (m H - b)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 ^ (r + 1) / Q * (n : ℝ) ^ b) * ((r : ℝ) ^ r * (n : ℝ) ^ (m H - b)) := by
          gcongr
          calc (b : ℝ) ^ b ≤ (r : ℝ) ^ b :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hbr) b
            _ ≤ (r : ℝ) ^ r := pow_le_pow_right₀ hr1 hbr
      _ = Y := by
          rw [hY]
          have : (n : ℝ) ^ b * (n : ℝ) ^ (m H - b) = (n : ℝ) ^ (m H) := by
            rw [← pow_add]; congr 1; omega
          rw [← this]; ring
  have hpow_le : ∀ (s : Finset (Fin n ⊕ Fin (m H))), s ∈ W H →
      (2 : ℝ) ^ s.toLeft.card ≤ 2 ^ r ∧ (2 : ℝ) ^ s.toRight.card ≤ 2 ^ r := by
    intro s hs
    have h2 := card_toLeft_add_card_toRight (u := s)
    rw [hunif H hH s hs] at h2
    exact ⟨pow_le_pow_right₀ (by norm_num) (by omega),
      pow_le_pow_right₀ (by norm_num) (by omega)⟩
  -- one edge `e`
  have hedge : ∀ e ∈ Wn, ((e.toLeft.powerset.biUnion (fun A' =>
      (e.toRight.powerset.filter (fun B' => B'.Nonempty)).biUnion (fun B' =>
        (satSets W 𝒮 φ Q D C r A' B'.card).biUnion (fun T =>
          univ.filter (fun f : Fin (m H) → Fin n => ∀ i ∈ B', f i ∈ T))))).card : ℝ) ≤
        2 ^ r * (2 ^ r * Y) := by
    intro e he
    obtain ⟨h1, h2⟩ := hpow_le e (mem_filter.1 he).1
    have hA : ∀ A' ∈ e.toLeft.powerset,
        (((e.toRight.powerset.filter (fun B' => B'.Nonempty)).biUnion (fun B' =>
          (satSets W 𝒮 φ Q D C r A' B'.card).biUnion (fun T =>
            univ.filter (fun f : Fin (m H) → Fin n => ∀ i ∈ B', f i ∈ T)))).card : ℝ) ≤
          2 ^ r * Y := by
      intro A' _
      calc _ ≤ ∑ B' ∈ e.toRight.powerset.filter (fun B' => B'.Nonempty),
            (((satSets W 𝒮 φ Q D C r A' B'.card).biUnion (fun T =>
              univ.filter (fun f : Fin (m H) → Fin n => ∀ i ∈ B', f i ∈ T))).card : ℝ) := by
            exact_mod_cast card_biUnion_le
        _ ≤ ∑ B' ∈ e.toRight.powerset.filter (fun B' => B'.Nonempty), Y :=
            sum_le_sum fun B' hB' => hinner e he A' B' hB'
        _ = (e.toRight.powerset.filter (fun B' => B'.Nonempty)).card * Y := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ 2 ^ r * Y := by
            gcongr
            calc ((e.toRight.powerset.filter (fun B' => B'.Nonempty)).card : ℝ)
                ≤ (e.toRight.powerset.card : ℝ) := by exact_mod_cast card_filter_le _ _
              _ = 2 ^ e.toRight.card := by rw [card_powerset]; push_cast; rfl
              _ ≤ 2 ^ r := h2
    calc _ ≤ ∑ A' ∈ e.toLeft.powerset,
          (((e.toRight.powerset.filter (fun B' => B'.Nonempty)).biUnion (fun B' =>
            (satSets W 𝒮 φ Q D C r A' B'.card).biUnion (fun T =>
              univ.filter (fun f : Fin (m H) → Fin n => ∀ i ∈ B', f i ∈ T)))).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ A' ∈ e.toLeft.powerset, 2 ^ r * Y := sum_le_sum hA
      _ = (e.toLeft.powerset.card : ℝ) * (2 ^ r * Y) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ r * (2 ^ r * Y) := by
          gcongr
          rw [card_powerset]; push_cast; exact h1
  have hWn_card : (Wn.card : ℝ) ≤ C := by
    exact_mod_cast (card_le_card (filter_subset _ _)).trans (hbd H hH)
  unfold bad2Set
  rw [← hWn]
  calc _ ≤ ∑ e ∈ Wn, ((e.toLeft.powerset.biUnion (fun A' =>
        (e.toRight.powerset.filter (fun B' => B'.Nonempty)).biUnion (fun B' =>
          (satSets W 𝒮 φ Q D C r A' B'.card).biUnion (fun T =>
            univ.filter (fun f : Fin (m H) → Fin n => ∀ i ∈ B', f i ∈ T))))).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ e ∈ Wn, 2 ^ r * (2 ^ r * Y) := sum_le_sum hedge
    _ = Wn.card * (2 ^ r * (2 ^ r * Y)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ C * (2 ^ r * (2 ^ r * Y)) := by gcongr
    _ = (4 * (C * 2 ^ (3 * r + 1) * (r : ℝ) ^ r)) * (n : ℝ) ^ (m H) / (4 * Q) := by
        rw [hY]; field_simp; ring
    _ ≤ (γ * Q) * (n : ℝ) ^ (m H) / (4 * Q) := by gcongr
    _ = γ * (n : ℝ) ^ (m H) / 4 := by field_simp

end RefinedAbsorption
