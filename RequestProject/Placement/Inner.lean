module
public import RequestProject.Placement.Counting

/-!
# Placing one gadget, one auxiliary vertex at a time

Fix the gadgets already placed (`Rs`, `Φ`, `s`), a forbidden `r`-graph `F` (host edges plus
edges already used), and a new gadget `(R, T)`.  We place the auxiliary vertices of the new
gadget one at a time.  The invariant `InnerInv A φ` says that on the already placed auxiliary
positions `A`:
* `φ` is injective and avoids the roots;
* every mixed load `d(J, φ(P))` with `J ⊆ R`, `∅ ≠ P ⊆ A`, `|J| + |P| ≤ r - 1` is still strictly
  below its cap (so placing the gadget keeps all loads capped);
* every template edge whose auxiliary vertices are already placed avoids `F`.

`innerInv_step` extends the invariant by one position: the saturated constraints, the forbidden
edges and the injectivity constraints exclude fewer than `n` vertices.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset

variable {n h : ℕ} {ι : Type*}

/-- The invariant of the inner (vertex-by-vertex) placement. -/
structure InnerInv (r lam D : ℕ) (Rs : ι → Finset (Fin n)) (Φ : ι → Fin h → Fin n)
    (s : Finset ι) (R : Finset (Fin n)) (T : Finset (Finset (Fin n ⊕ Fin h)))
    (F : Finset (Finset (Fin n))) (A : Finset (Fin h)) (φ : Fin h → Fin n) : Prop where
  inj : Set.InjOn φ A
  avoid : ∀ p ∈ A, φ p ∉ R
  loads : ∀ J ⊆ R, ∀ P ⊆ A, P.Nonempty → J.card + P.card ≤ r - 1 →
    load Rs Φ s J (P.image φ) < cap r lam D n J P.card
  edges : ∀ t ∈ T, (∀ p, Sum.inr p ∈ t → p ∈ A) → placeEdge φ t ∉ F

theorem innerInv_empty (r lam D : ℕ) (Rs : ι → Finset (Fin n)) (Φ : ι → Fin h → Fin n)
    (s : Finset ι) {k : ℕ} (R : Finset (Fin n)) (T : Finset (Finset (Fin n ⊕ Fin h)))
    (hw : GadgetWF r k R T) (F : Finset (Finset (Fin n))) (φ : Fin h → Fin n) :
    InnerInv r lam D Rs Φ s R T F ∅ φ where
  inj := by simp
  avoid := by simp
  loads := by
    intro J _ P hP hne
    rw [subset_empty] at hP
    subst hP
    exact absurd hne (by simp)
  edges := by
    intro t ht hA
    obtain ⟨p, hp⟩ := hw.edge_aux t ht
    exact absurd (hA p hp) (by simp)

theorem image_update_of_not_mem {P : Finset (Fin h)} {p : Fin h} (hp : p ∉ P)
    (φ : Fin h → Fin n) (v : Fin n) : P.image (Function.update φ p v) = P.image φ := by
  apply image_congr
  intro q hq
  rw [Function.update_of_ne (by rintro rfl; exact hp hq)]

theorem image_update_of_mem {P : Finset (Fin h)} {p : Fin h} (hp : p ∈ P)
    (φ : Fin h → Fin n) (v : Fin n) :
    P.image (Function.update φ p v) = insert v ((P.erase p).image φ) := by
  conv_lhs => rw [← insert_erase hp]
  rw [image_insert, Function.update_self, image_update_of_not_mem (notMem_erase p P)]

theorem placeEdge_update_of_not_mem {t : Finset (Fin n ⊕ Fin h)} {p : Fin h}
    (hp : Sum.inr p ∉ t) (φ : Fin h → Fin n) (v : Fin n) :
    placeEdge (Function.update φ p v) t = placeEdge φ t := by
  apply image_congr
  intro x hx
  rcases x with a | q
  · rfl
  · simp only [emb, Sum.elim_inr]
    rw [Function.update_of_ne (by rintro rfl; exact hp hx)]

theorem placeEdge_update_of_mem {t : Finset (Fin n ⊕ Fin h)} {p : Fin h}
    (hp : Sum.inr p ∈ t) (φ : Fin h → Fin n) (v : Fin n) :
    placeEdge (Function.update φ p v) t = insert v (placeEdge φ (t.erase (Sum.inr p))) := by
  unfold placeEdge
  conv_lhs => rw [← insert_erase hp]
  rw [image_insert]
  simp only [emb, Sum.elim_inr, Function.update_self]
  congr 1
  exact placeEdge_update_of_not_mem (notMem_erase _ _) φ v

/-- The saturated-constraint count: for one pair `(J, P')`, fewer than `h n / λ` vertices would
push the load `d(J, φ(P') ∪ {v})` to its cap. -/
theorem card_heavy_lam_le {r lam D : ℕ} (Rs : ι → Finset (Fin n)) (Φ : ι → Fin h → Fin n)
    (s : Finset ι) (J U : Finset (Fin n)) (u : ℕ) (hJu : J.card + u + 1 ≤ r - 1)
    (hD : 0 < D) (hn : 0 < n) (hlam : 0 < lam)
    (hU : load Rs Φ s J U ≤ cap r lam D n J u) :
    ((univ \ U).filter fun v => cap r lam D n J (u + 1) ≤ load Rs Φ s J (insert v U)).card *
      lam ≤ h * n := by
  have key := card_heavy_mul_le Rs Φ s J U (cap r lam D n J (u + 1))
  set c := ((univ \ U).filter fun v => cap r lam D n J (u + 1) ≤
    load Rs Φ s J (insert v U)).card
  have he : r - 1 - J.card - u = (r - 1 - J.card - (u + 1)) + 1 := by omega
  unfold cap at key hU
  rw [he] at hU
  set e := r - 1 - J.card - (u + 1)
  have hX : 0 < lam ^ u * D * n ^ e := by positivity
  have : c * lam * (lam ^ u * D * n ^ e) ≤ h * n * (lam ^ u * D * n ^ e) := by
    calc c * lam * (lam ^ u * D * n ^ e) = c * (lam ^ (u + 1) * D * n ^ e) := by ring
      _ ≤ h * load Rs Φ s J U := key
      _ ≤ h * (lam ^ u * D * n ^ (e + 1)) := Nat.mul_le_mul_left _ hU
      _ = h * n * (lam ^ u * D * n ^ e) := by ring
  exact Nat.le_of_mul_le_mul_right this hX

/-- A forbidden-edge constraint excludes at most `deg F B` vertices. -/
theorem card_forbidden_le (F : Finset (Finset (Fin n))) (B : Finset (Fin n)) :
    (univ.filter fun v => v ∉ B ∧ insert v B ∈ F).card ≤ deg F B := by
  unfold deg
  apply card_le_card_of_injOn (fun v => insert v B)
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hv
    simp only [coe_filter, Set.mem_setOf_eq]
    exact ⟨hv.2, subset_insert _ _⟩
  · intro v hv w hw hvw
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hv hw
    have : v ∈ insert w B := by
      rw [← show insert v B = insert w B from hvw]; exact mem_insert_self v B
    rcases mem_insert.1 this with h | h
    · exact h
    · exact absurd h hv.1

/-- **One step of the inner placement.** -/
theorem innerInv_step {r k lam D Fdeg : ℕ} (Rs : ι → Finset (Fin n)) (Φ : ι → Fin h → Fin n)
    (s : Finset ι) (R : Finset (Fin n)) (T : Finset (Finset (Fin n ⊕ Fin h)))
    (hw : GadgetWF r k R T) (F : Finset (Finset (Fin n)))
    (hroot : ∀ J ⊆ R, J.card ≤ r - 1 → load Rs Φ s J ∅ ≤ D * n ^ (r - 1 - J.card))
    (hF : ∀ B : Finset (Fin n), B.card = r - 1 → deg F B ≤ Fdeg)
    (hD : 0 < D) (hlam : 4 * 2 ^ (k + h) * h ≤ lam)
    (hnum : 4 * (k + h + 2 ^ (k + h) * Fdeg) < 3 * n)
    {A : Finset (Fin h)} {φ : Fin h → Fin n} (hinv : InnerInv r lam D Rs Φ s R T F A φ)
    {p : Fin h} (hp : p ∉ A) :
    ∃ v, InnerInv r lam D Rs Φ s R T F (insert p A) (Function.update φ p v) := by
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

end RefinedAbsorption.Placement
