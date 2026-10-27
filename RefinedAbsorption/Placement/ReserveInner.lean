module
public import RefinedAbsorption.Placement.Inner

/-!
# Placing one gadget inside a reserve, one auxiliary vertex at a time

This is the reserve version of `Inner.lean`: the auxiliary vertices of the gadgets are placed
inside a prescribed set `Z ⊆ Fin n` (the *reserve*), and all counting is done relative to
`a = |Z|` instead of `n`.  The roots may lie anywhere in `Fin n`.

The caps of the mixed loads are `capA r λ D a j u = λ^u · D · a^(r-1-j-u)` (for `|J| = j`,
`|U| = u`).  The root loads must satisfy `d(J, ∅) ≤ D · a^(r-1-|J|)`; this is automatic for
`Z = univ` (`rootIncidence`), and in general it says that the roots are not too dense compared
to the reserve.

`innerInvA_step` extends the invariant by one position: the saturated constraints, the forbidden
edges and the injectivity constraints exclude fewer than `a` vertices of `Z`.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset

variable {n h : ℕ} {ι : Type*}

/-- The cap of the load `d(J,U)` relative to a reserve of size `a`, for `|J| = j`, `|U| = u`. -/
def capA (r lam D a j u : ℕ) : ℕ := lam ^ u * D * a ^ (r - 1 - j - u)

/-- The invariant of the inner placement inside the reserve `Z`. -/
structure InnerInvA (r lam D : ℕ) (Z : Finset (Fin n)) (Rs : ι → Finset (Fin n))
    (Φ : ι → Fin h → Fin n) (s : Finset ι) (R : Finset (Fin n))
    (T : Finset (Finset (Fin n ⊕ Fin h))) (F : Finset (Finset (Fin n))) (A : Finset (Fin h))
    (φ : Fin h → Fin n) : Prop where
  inj : Set.InjOn φ A
  avoid : ∀ p ∈ A, φ p ∉ R
  range : ∀ p ∈ A, φ p ∈ Z
  loads : ∀ J ⊆ R, ∀ P ⊆ A, P.Nonempty → J.card + P.card ≤ r - 1 →
    load Rs Φ s J (P.image φ) < capA r lam D Z.card J.card P.card
  edges : ∀ t ∈ T, (∀ p, Sum.inr p ∈ t → p ∈ A) → placeEdge φ t ∉ F

theorem innerInvA_empty (r lam D : ℕ) (Z : Finset (Fin n)) (Rs : ι → Finset (Fin n))
    (Φ : ι → Fin h → Fin n) (s : Finset ι) {k : ℕ} (R : Finset (Fin n))
    (T : Finset (Finset (Fin n ⊕ Fin h))) (hw : GadgetWF r k R T) (F : Finset (Finset (Fin n)))
    (φ : Fin h → Fin n) : InnerInvA r lam D Z Rs Φ s R T F ∅ φ where
  inj := by simp
  avoid := by simp
  range := by simp
  loads := by
    intro J _ P hP hne
    rw [subset_empty] at hP
    subst hP
    exact absurd hne (by simp)
  edges := by
    intro t ht hA
    obtain ⟨p, hp⟩ := hw.edge_aux t ht
    exact absurd (hA p hp) (by simp)

/-- The saturated-constraint count inside the reserve: fewer than `h a / λ` vertices of `Z`
would push the load `d(J, U ∪ {v})` to its cap. -/
theorem card_heavy_lam_leA {r lam D : ℕ} (Z : Finset (Fin n)) (Rs : ι → Finset (Fin n))
    (Φ : ι → Fin h → Fin n) (s : Finset ι) (J U : Finset (Fin n)) (u : ℕ)
    (hJu : J.card + u + 1 ≤ r - 1) (hD : 0 < D) (ha : 0 < Z.card) (hlam : 0 < lam)
    (hU : load Rs Φ s J U ≤ capA r lam D Z.card J.card u) :
    ((Z \ U).filter fun v => capA r lam D Z.card J.card (u + 1) ≤
      load Rs Φ s J (insert v U)).card * lam ≤ h * Z.card := by
  have key := card_heavy_mul_le Rs Φ s J U (capA r lam D Z.card J.card (u + 1))
  set c := ((Z \ U).filter fun v => capA r lam D Z.card J.card (u + 1) ≤
    load Rs Φ s J (insert v U)).card
  have hc : c ≤ ((univ \ U).filter fun v => capA r lam D Z.card J.card (u + 1) ≤
      load Rs Φ s J (insert v U)).card :=
    card_le_card (filter_subset_filter _ (sdiff_subset_sdiff (subset_univ _) subset_rfl))
  have he : r - 1 - J.card - u = (r - 1 - J.card - (u + 1)) + 1 := by omega
  unfold capA at key hU
  rw [he] at hU
  set e := r - 1 - J.card - (u + 1)
  set a := Z.card
  have hX : 0 < lam ^ u * D * a ^ e := by positivity
  have : c * lam * (lam ^ u * D * a ^ e) ≤ h * a * (lam ^ u * D * a ^ e) := by
    calc c * lam * (lam ^ u * D * a ^ e) = c * (lam ^ (u + 1) * D * a ^ e) := by ring
      _ ≤ _ * (lam ^ (u + 1) * D * a ^ e) := Nat.mul_le_mul_right _ hc
      _ ≤ h * load Rs Φ s J U := key
      _ ≤ h * (lam ^ u * D * a ^ (e + 1)) := Nat.mul_le_mul_left _ hU
      _ = h * a * (lam ^ u * D * a ^ e) := by ring
  exact Nat.le_of_mul_le_mul_right this hX

/-- **One step of the inner placement inside the reserve.** -/
theorem innerInvA_step {r k lam D Fdeg : ℕ} (Z : Finset (Fin n)) (Rs : ι → Finset (Fin n))
    (Φ : ι → Fin h → Fin n) (s : Finset ι) (R : Finset (Fin n))
    (T : Finset (Finset (Fin n ⊕ Fin h))) (hw : GadgetWF r k R T) (F : Finset (Finset (Fin n)))
    (hroot : ∀ J ⊆ R, J.card ≤ r - 1 → load Rs Φ s J ∅ ≤ D * Z.card ^ (r - 1 - J.card))
    (hF : ∀ B : Finset (Fin n), B.card = r - 1 → deg F B ≤ Fdeg)
    (hD : 0 < D) (hlam : 4 * 2 ^ (k + h) * h ≤ lam)
    (hnum : 4 * (k + h + 2 ^ (k + h) * Fdeg) < 3 * Z.card)
    {A : Finset (Fin h)} {φ : Fin h → Fin n} (hinv : InnerInvA r lam D Z Rs Φ s R T F A φ)
    {p : Fin h} (hp : p ∉ A) :
    ∃ v, InnerInvA r lam D Z Rs Φ s R T F (insert p A) (Function.update φ p v) := by
  classical
  have ha : 0 < Z.card := by omega
  have hh : 0 < h := Fin.pos p
  have hM : 0 < 2 ^ (k + h) := by positivity
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlam
  set Bad1 : Finset (Fin n) := R ∪ A.image φ
  set pairs := (R.powerset ×ˢ A.powerset).filter (fun x => x.1.card + x.2.card + 1 ≤ r - 1)
  set Bad2 : Finset (Fin n) := pairs.biUnion (fun x => (Z \ x.2.image φ).filter
    (fun v => capA r lam D Z.card x.1.card (x.2.card + 1) ≤
      load Rs Φ s x.1 (insert v (x.2.image φ))))
  set edgesP := T.filter (fun t => Sum.inr p ∈ t ∧ ∀ q, Sum.inr q ∈ t → q ∈ insert p A)
  set Bad3 : Finset (Fin n) := edgesP.biUnion (fun t => univ.filter (fun v =>
    v ∉ placeEdge φ (t.erase (Sum.inr p)) ∧ insert v (placeEdge φ (t.erase (Sum.inr p))) ∈ F))
  have hA : A.card ≤ h := card_le_univ A |>.trans (by simp)
  have h1 : Bad1.card ≤ k + h :=
    (card_union_le _ _).trans (Nat.add_le_add hw.roots_le (card_image_le.trans hA))
  have hpairs : pairs.card ≤ 2 ^ (k + h) := by
    calc pairs.card ≤ (R.powerset ×ˢ A.powerset).card := card_filter_le _ _
      _ = 2 ^ R.card * 2 ^ A.card := by rw [card_product, card_powerset, card_powerset]
      _ ≤ 2 ^ k * 2 ^ h := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hw.roots_le)
          (Nat.pow_le_pow_right (by norm_num) hA)
      _ = 2 ^ (k + h) := (pow_add _ _ _).symm
  have h2 : 4 * Bad2.card ≤ Z.card := by
    have hsum : Bad2.card * lam ≤ 2 ^ (k + h) * (h * Z.card) := by
      calc Bad2.card * lam ≤ (∑ x ∈ pairs, ((Z \ x.2.image φ).filter (fun v =>
            capA r lam D Z.card x.1.card (x.2.card + 1) ≤
              load Rs Φ s x.1 (insert v (x.2.image φ)))).card) * lam :=
            Nat.mul_le_mul_right _ card_biUnion_le
        _ = ∑ x ∈ pairs, ((Z \ x.2.image φ).filter (fun v =>
            capA r lam D Z.card x.1.card (x.2.card + 1) ≤
              load Rs Φ s x.1 (insert v (x.2.image φ)))).card * lam := sum_mul _ _ _
        _ ≤ ∑ _x ∈ pairs, h * Z.card := by
            apply sum_le_sum
            rintro ⟨J, P'⟩ hx
            simp only [pairs, mem_filter, mem_product, mem_powerset] at hx
            obtain ⟨⟨hJR, hP'A⟩, hcard⟩ := hx
            have hcardP : (P'.image φ).card = P'.card :=
              card_image_of_injOn (hinv.inj.mono (coe_subset.2 hP'A))
            have := card_heavy_lam_leA Z Rs Φ s J (P'.image φ) P'.card (by omega) hD ha hlam0
            refine this ?_
            rcases P'.eq_empty_or_nonempty with hP' | hP'
            · subst hP'
              simp only [image_empty, card_empty]
              have := hroot J hJR (by omega)
              simpa [capA, mul_comm] using this
            · exact (hinv.loads J hJR P' hP'A hP' (by omega)).le
        _ = pairs.card * (h * Z.card) := by rw [sum_const, smul_eq_mul]
        _ ≤ 2 ^ (k + h) * (h * Z.card) := Nat.mul_le_mul_right _ hpairs
    have : 4 * Bad2.card * (2 ^ (k + h) * h) ≤ Z.card * (2 ^ (k + h) * h) := by
      calc 4 * Bad2.card * (2 ^ (k + h) * h) = Bad2.card * (4 * 2 ^ (k + h) * h) := by ring
        _ ≤ Bad2.card * lam := Nat.mul_le_mul_left _ hlam
        _ ≤ 2 ^ (k + h) * (h * Z.card) := hsum
        _ = Z.card * (2 ^ (k + h) * h) := by ring
    exact Nat.le_of_mul_le_mul_right this (by positivity)
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
  have hlt : (Bad1 ∪ Bad2 ∪ Bad3).card < Z.card := by
    have := card_union_le (Bad1 ∪ Bad2) Bad3
    have := card_union_le Bad1 Bad2
    omega
  obtain ⟨v, hvZ, hv⟩ := exists_mem_notMem_of_card_lt_card hlt
  simp only [mem_union, not_or] at hv
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := hv
  have hvR : v ∉ R := fun h => hv1 (mem_union_left _ h)
  have hvA : ∀ q ∈ A, φ q ≠ v := fun q hq h => hv1 (mem_union_right _ (h ▸ mem_image_of_mem φ hq))
  have hφ' : ∀ q ∈ A, Function.update φ p v q = φ q := fun q hq =>
    Function.update_of_ne (by rintro rfl; exact hp hq) _ _
  refine ⟨v, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [coe_insert]
    refine (Set.injOn_insert (by simpa using hp)).2 ⟨?_, ?_⟩
    · intro a ha b hb hab
      rw [hφ' a ha, hφ' b hb] at hab
      exact hinv.inj ha hb hab
    · rintro ⟨q, hq, hqv⟩
      rw [Function.update_self, hφ' q hq] at hqv
      exact hvA q hq hqv
  · intro q hq
    rcases mem_insert.1 hq with rfl | hq
    · rw [Function.update_self]; exact hvR
    · rw [hφ' q hq]; exact hinv.avoid q hq
  · intro q hq
    rcases mem_insert.1 hq with rfl | hq
    · rw [Function.update_self]; exact hvZ
    · rw [hφ' q hq]; exact hinv.range q hq
  · intro J hJR P hP hPne hcard
    by_cases hpP : p ∈ P
    · rw [image_update_of_mem hpP]
      have hP' : P.erase p ⊆ A := by
        intro q hq
        rcases mem_insert.1 (hP (mem_of_mem_erase hq)) with h | h
        · exact absurd h (ne_of_mem_erase hq)
        · exact h
      have hcardP : (P.erase p).card + 1 = P.card := card_erase_add_one hpP
      have hmem : (J, P.erase p) ∈ pairs := by
        simp only [pairs, mem_filter, mem_product, mem_powerset]
        exact ⟨⟨hJR, hP'⟩, by omega⟩
      have hvU : v ∉ (P.erase p).image φ := by
        intro h
        obtain ⟨q, hq, hqv⟩ := mem_image.1 h
        exact hvA q (hP' hq) hqv
      have : ¬ (capA r lam D Z.card J.card ((P.erase p).card + 1) ≤
          load Rs Φ s J (insert v ((P.erase p).image φ))) := by
        intro hc
        exact hv2 (mem_biUnion.2 ⟨_, hmem, mem_filter.2 ⟨mem_sdiff.2 ⟨hvZ, hvU⟩, hc⟩⟩)
      rw [hcardP] at this
      exact not_le.1 this
    · have hPA : P ⊆ A := by
        intro q hq
        rcases mem_insert.1 (hP hq) with h | h
        · exact absurd (h ▸ hq) hpP
        · exact h
      rw [image_update_of_not_mem hpP]
      exact hinv.loads J hJR P hPA hPne hcard
  · intro t ht haux
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

/-- Running the inner placement inside the reserve over all auxiliary positions. -/
theorem exists_innerInvA_univ {r k lam D Fdeg : ℕ} (Z : Finset (Fin n))
    (Rs : ι → Finset (Fin n)) (Φ : ι → Fin h → Fin n) (s : Finset ι) (R : Finset (Fin n))
    (T : Finset (Finset (Fin n ⊕ Fin h))) (hw : GadgetWF r k R T) (F : Finset (Finset (Fin n)))
    (hroot : ∀ J ⊆ R, J.card ≤ r - 1 → load Rs Φ s J ∅ ≤ D * Z.card ^ (r - 1 - J.card))
    (hF : ∀ B : Finset (Fin n), B.card = r - 1 → deg F B ≤ Fdeg)
    (hD : 0 < D) (hlam : 4 * 2 ^ (k + h) * h ≤ lam)
    (hnum : 4 * (k + h + 2 ^ (k + h) * Fdeg) < 3 * Z.card) :
    ∃ φ, InnerInvA r lam D Z Rs Φ s R T F univ φ := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have : Z.card = 0 := by
        rw [card_eq_zero, eq_empty_iff_forall_notMem]; intro x; exact x.elim0
      omega
    · exact h0
  have key : ∀ A : Finset (Fin h), ∃ φ, InnerInvA r lam D Z Rs Φ s R T F A φ := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨fun _ => ⟨0, hn⟩, innerInvA_empty r lam D Z Rs Φ s R T hw F _⟩
    | insert p A hp ih =>
      obtain ⟨φ, hφ⟩ := ih
      exact ⟨_, (innerInvA_step Z Rs Φ s R T hw F hroot hF hD hlam hnum hφ hp).choose_spec⟩
  exact key univ

end RefinedAbsorption.Placement
