module
public import RequestProject.Placement.Lemma52

/-!
# The Partial Clique Embedding Lemma avoiding forbidden vertex sets

A copy of the vertex-by-vertex step of the Partial Clique Embedding Lemma
(`RefinedAbsorption.Placement.innerInv_step`, Lemma 5.2 of Delcourt–Postle) in which the chosen
vertex also avoids an extra set `Bad4` of size counted in the numerical slack.  It is used to
place gadgets so that no member of a prescribed family `𝓢` of sets ("dangerous sets", e.g. the
`(r+1)`-subsets of the blocks of a packing) lies inside the roots plus the auxiliary vertices of
a gadget unless it lies inside the roots.
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset RefinedAbsorption.Placement

variable {n h : ℕ} {ι : Type*}

/-- **One step of the inner placement.** -/
theorem innerInv_step_avoid {r k lam D Fdeg : ℕ} (Rs : ι → Finset (Fin n)) (Φ : ι → Fin h → Fin n)
    (s : Finset ι) (R : Finset (Fin n)) (T : Finset (Finset (Fin n ⊕ Fin h)))
    (hw : GadgetWF r k R T) (F : Finset (Finset (Fin n)))
    (hroot : ∀ J ⊆ R, J.card ≤ r - 1 → load Rs Φ s J ∅ ≤ D * n ^ (r - 1 - J.card))
    (hF : ∀ B : Finset (Fin n), B.card = r - 1 → deg F B ≤ Fdeg)
    (hD : 0 < D) (hlam : 4 * 2 ^ (k + h) * h ≤ lam)
    (Bad4 : Finset (Fin n)) (hnum : 4 * (k + h + 2 ^ (k + h) * Fdeg + Bad4.card) < 3 * n)
    {A : Finset (Fin h)} {φ : Fin h → Fin n} (hinv : InnerInv r lam D Rs Φ s R T F A φ)
    {p : Fin h} (hp : p ∉ A) :
    ∃ v, v ∉ Bad4 ∧ InnerInv r lam D Rs Φ s R T F (insert p A) (Function.update φ p v) := by
  classical
  have hn : 0 < n := by omega
  have hh : 0 < h := Fin.pos p
  have hM : 0 < 2 ^ (k + h) := by positivity
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlam
  -- the three kinds of excluded vertices
  set Bad1 : Finset (Fin n) := R ∪ A.image φ
  set pairs := (R.powerset ×ˢ A.powerset).filter (fun x => x.1.card + x.2.card + 1 ≤ r - 1)
  set Bad2 : Finset (Fin n) := pairs.biUnion (fun x => (univ \ x.2.image φ).filter
    (fun v => cap r lam D n x.1 (x.2.card + 1) ≤ load Rs Φ s x.1 (insert v (x.2.image φ))))
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
  have h2 : 4 * Bad2.card ≤ n := by
    have hsum : Bad2.card * lam ≤ 2 ^ (k + h) * (h * n) := by
      calc Bad2.card * lam ≤ (∑ x ∈ pairs, ((univ \ x.2.image φ).filter (fun v =>
            cap r lam D n x.1 (x.2.card + 1) ≤ load Rs Φ s x.1 (insert v (x.2.image φ)))).card)
            * lam := Nat.mul_le_mul_right _ card_biUnion_le
        _ = ∑ x ∈ pairs, ((univ \ x.2.image φ).filter (fun v =>
            cap r lam D n x.1 (x.2.card + 1) ≤ load Rs Φ s x.1 (insert v (x.2.image φ)))).card
            * lam := sum_mul _ _ _
        _ ≤ ∑ _x ∈ pairs, h * n := by
            apply sum_le_sum
            rintro ⟨J, P'⟩ hx
            simp only [pairs, mem_filter, mem_product, mem_powerset] at hx
            obtain ⟨⟨hJR, hP'A⟩, hcard⟩ := hx
            apply card_heavy_lam_le Rs Φ s J _ _ hcard hD hn hlam0
            rcases P'.eq_empty_or_nonempty with hP' | hP'
            · subst hP'
              simp only [image_empty, card_empty]
              have := hroot J hJR (by omega)
              simpa [cap] using this
            · exact (hinv.loads J hJR P' hP'A hP' (by omega)).le
        _ = pairs.card * (h * n) := by rw [sum_const, smul_eq_mul]
        _ ≤ 2 ^ (k + h) * (h * n) := Nat.mul_le_mul_right _ hpairs
    have : 4 * Bad2.card * (2 ^ (k + h) * h) ≤ n * (2 ^ (k + h) * h) := by
      calc 4 * Bad2.card * (2 ^ (k + h) * h) = Bad2.card * (4 * 2 ^ (k + h) * h) := by ring
        _ ≤ Bad2.card * lam := Nat.mul_le_mul_left _ hlam
        _ ≤ 2 ^ (k + h) * (h * n) := hsum
        _ = n * (2 ^ (k + h) * h) := by ring
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
  have hlt : (Bad1 ∪ Bad2 ∪ Bad3 ∪ Bad4).card < (univ : Finset (Fin n)).card := by
    rw [card_univ, Fintype.card_fin]
    have := card_union_le (Bad1 ∪ Bad2 ∪ Bad3) Bad4
    have := card_union_le (Bad1 ∪ Bad2) Bad3
    have := card_union_le Bad1 Bad2
    omega
  obtain ⟨v, -, hv⟩ := exists_mem_notMem_of_card_lt_card hlt
  simp only [mem_union, not_or] at hv
  obtain ⟨⟨⟨hv1, hv2⟩, hv3⟩, hv4⟩ := hv
  have hvR : v ∉ R := fun h => hv1 (mem_union_left _ h)
  have hvA : ∀ q ∈ A, φ q ≠ v := fun q hq h => hv1 (mem_union_right _ (h ▸ mem_image_of_mem φ hq))
  have hφ' : ∀ q ∈ A, Function.update φ p v q = φ q := fun q hq =>
    Function.update_of_ne (by rintro rfl; exact hp hq) _ _
  refine ⟨v, hv4, ⟨?_, ?_, ?_, ?_⟩⟩
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
  · -- loads
    intro J hJR P hP hPne hcard
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
      have : ¬ (cap r lam D n J ((P.erase p).card + 1) ≤
          load Rs Φ s J (insert v ((P.erase p).image φ))) := by
        intro hc
        exact hv2 (mem_biUnion.2 ⟨_, hmem, mem_filter.2 ⟨mem_sdiff.2 ⟨mem_univ _, hvU⟩, hc⟩⟩)
      rw [hcardP] at this
      exact not_le.1 this
    · have hPA : P ⊆ A := by
        intro q hq
        rcases mem_insert.1 (hP hq) with h | h
        · exact absurd (h ▸ hq) hpP
        · exact h
      rw [image_update_of_not_mem hpP]
      exact hinv.loads J hJR P hPA hPne hcard
  · -- edges
    intro t ht haux
    by_cases hpt : Sum.inr p ∈ t
    · rw [placeEdge_update_of_mem hpt]
      have hmem : t ∈ edgesP := mem_filter.2 ⟨ht, hpt, haux⟩
      have hvB : v ∉ placeEdge φ (t.erase (Sum.inr p)) := by
        intro hvB
        have := placeEdge_subset hw φ (t := t) ht
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

end RefinedAbsorption.Pending
