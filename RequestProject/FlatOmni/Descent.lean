module
public import RequestProject.FlatOmni.WindowGe

/-!
# Descent through windows inside a prescribed set

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Theorem 3.8 for graphs.
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

`LocalOut q C ends Z X Bd`: after an injective relabelling, the multigraph `X` has a complete
`C`-refined `K_q^2`-multi-refiner whose new copies lie inside `Z`, with vertex degrees of the new
copies and piece degrees at most `Bd`.

**`localDescent`**: a graph multigraph `X` of bounded multiplicity whose copies lie in a set `P`
has such a refiner inside `P`, with budget `A · (D + sharpPot 2 |P|)`.  The descent through
windows (`windowRefinerM_pot`) is run on `Fin |P|` and transported into `P`.
-/

@[expose] public section

namespace RefinedAbsorption.FlatOmni

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement RefinedAbsorption.Dense RefinedAbsorption.Window
  RefinedAbsorption.Sharp

/-- Output of a local refiner construction (see the module docstring). -/
def LocalOut (q C : ℕ) {n : ℕ} {E : Type} (ends : E → Finset (Fin n)) (Z : Finset (Fin n))
    (X : Finset E) (Bd : ℕ) : Prop :=
  ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
    (R : Finset E') (𝒲 : Finset (Finset E')),
    Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
    IsMultiRefiner q 2 C ends' (X.image g) R 𝒲 ∧ (∀ c ∈ R, ends' c ⊆ Z) ∧
    (∀ v, mdeg ends' R {v} ≤ Bd) ∧ (∀ v, pdeg ends' 𝒲 {v} ≤ Bd)

section MapEnds

variable {m n : ℕ} {E : Type*} [DecidableEq E]

omit [DecidableEq E] in
theorem mdeg_mapEnds_emb (emb : Fin m ↪ Fin n) (ends : E → Finset (Fin m)) (G : Finset E)
    (i : Fin m) : mdeg (mapEnds emb ends) G {emb i} = mdeg ends G {i} := by
  unfold mdeg mapEnds
  congr 1
  refine filter_congr fun c _ => ?_
  simp only [singleton_subset_iff, mem_image, emb.injective.eq_iff, exists_eq_right]

omit [DecidableEq E] in
theorem mdeg_mapEnds_emb_out (emb : Fin m ↪ Fin n) (ends : E → Finset (Fin m)) (G : Finset E)
    (v : Fin n) (hv : ∀ i, emb i ≠ v) : mdeg (mapEnds emb ends) G {v} = 0 := by
  unfold mdeg mapEnds
  rw [card_eq_zero, filter_eq_empty_iff]
  intro c _ h
  obtain ⟨i, -, hi⟩ := mem_image.1 (singleton_subset_iff.1 h)
  exact hv i hi

omit [DecidableEq E] in
theorem biUnion_mapEnds (emb : Fin m ↪ Fin n) (ends : E → Finset (Fin m)) (W : Finset E) :
    W.biUnion (mapEnds emb ends) = (W.biUnion ends).image emb := by
  ext v
  simp only [mapEnds, mem_biUnion, mem_image]
  constructor
  · rintro ⟨c, hc, i, hi, rfl⟩; exact ⟨i, ⟨c, hc, hi⟩, rfl⟩
  · rintro ⟨i, ⟨c, hc, hi⟩, rfl⟩; exact ⟨c, hc, i, hi, rfl⟩

omit [DecidableEq E] in
theorem pdeg_mapEnds_emb (emb : Fin m ↪ Fin n) (ends : E → Finset (Fin m))
    (𝒲 : Finset (Finset E)) (i : Fin m) :
    pdeg (mapEnds emb ends) 𝒲 {emb i} = pdeg ends 𝒲 {i} := by
  unfold pdeg
  congr 1
  refine filter_congr fun W _ => ?_
  rw [biUnion_mapEnds]
  simp only [singleton_subset_iff, mem_image, emb.injective.eq_iff, exists_eq_right]

omit [DecidableEq E] in
theorem pdeg_mapEnds_emb_out (emb : Fin m ↪ Fin n) (ends : E → Finset (Fin m))
    (𝒲 : Finset (Finset E)) (v : Fin n) (hv : ∀ i, emb i ≠ v) :
    pdeg (mapEnds emb ends) 𝒲 {v} = 0 := by
  unfold pdeg
  rw [card_eq_zero, filter_eq_empty_iff]
  intro W _ h
  rw [biUnion_mapEnds] at h
  obtain ⟨i, -, hi⟩ := mem_image.1 (singleton_subset_iff.1 h)
  exact hv i hi

end MapEnds

/-- **Descent through windows inside a prescribed set** (see the module docstring). -/
theorem localDescent {q : ℕ} (hq : 2 < q) (M₀ : ℕ) :
    ∃ C A : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
      (P : Finset (Fin n)) (X : Finset E) (D : ℕ),
      MIsRGraph 2 ends X → (∀ x ∈ X, ends x ⊆ P) → 1 ≤ D → (∀ e, mult ends X e ≤ M₀) →
      (∀ v, mdeg ends X {v} ≤ D) →
      LocalOut q C ends P X (A * (D + sharpPot 2 P.card)) := by
  classical
  obtain ⟨M, -, hst⟩ := windowStageM_two_ge hq
  obtain ⟨Cst, m₀, hCst, hstage⟩ := hst (max M M₀) (le_max_left _ _)
  obtain ⟨Cb, Ab, hbase⟩ := baseRefiner q 2 le_rfl hq (max m₀ 1)
  have hwin := windowRefinerM_pot (Φ := sharpPot 2) (a := sharpCost 2)
    (fun m m' hm h => sharpPot_step (by norm_num) (by omega) h)
    (fun m hm => one_le_sharpCost 2 (by omega)) hstage hbase hCst
  set K := Cst + (Cst + Ab) * Cst with hK
  refine ⟨Cst + Cb + (Cst + Cb) + (Cst + Cb), (Cst + Ab) + K, ?_⟩
  intro n E _ ends P X D hXr hXP hD1 hXm hdeg
  set m := P.card with hm
  set emb : Fin m ↪ Fin n := (P.orderEmbOfFin rfl).toEmbedding with hemb
  have hembP : ∀ i, emb i ∈ P := fun i => P.orderEmbOfFin_mem rfl i
  have hPemb : ∀ v ∈ P, ∃ i, emb i = v := by
    intro v hv
    have : v ∈ Set.range (P.orderEmbOfFin rfl) := by rw [range_orderEmbOfFin]; exact hv
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi⟩
  -- the labels of `X`, with vertices pulled back to `Fin m`
  set endsS : {c // c ∈ X} → Finset (Fin m) :=
    fun c => (ends c.1).preimage emb emb.injective.injOn with hendsS
  have hmapS : ∀ c : {c // c ∈ X}, (endsS c).image emb = ends c.1 := by
    intro c
    rw [hendsS, image_preimage]
    exact filter_true_of_mem fun v hv => hPemb v (hXP c.1 c.2 hv)
  have hcardS : ∀ c : {c // c ∈ X}, (endsS c).card = 2 := by
    intro c
    rw [← card_image_of_injective _ emb.injective, hmapS]
    exact hXr c.1 c.2
  have hmultS : ∀ e, mult endsS univ e ≤ max M M₀ := by
    intro e
    refine le_trans ?_ ((hXm (e.image emb)).trans (le_max_right _ _))
    unfold mult
    refine card_le_card_of_injOn (fun c => c.1) (fun c hc => ?_)
      (fun c _ c' _ h => Subtype.ext h)
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hc ⊢
    refine ⟨c.2, ?_⟩
    rw [← hmapS c, hc]
  have hdegS : ∀ S : Finset (Fin m), S.card = 2 - 1 → mdeg endsS univ S ≤ D := by
    intro S hS
    obtain ⟨i, rfl⟩ := card_eq_one.1 hS
    refine le_trans ?_ (hdeg (emb i))
    unfold mdeg
    refine card_le_card_of_injOn (fun c => c.1) (fun c hc => ?_)
      (fun c _ c' _ h => Subtype.ext h)
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and,
      singleton_subset_iff] at hc ⊢
    refine ⟨c.2, ?_⟩
    rw [← hmapS c]
    exact mem_image_of_mem _ hc
  obtain ⟨E', _, g, ends'm, R, 𝒲, hg, hends, hfr, hch, -, hdegR, hpd⟩ :=
    hwin m endsS univ univ D (fun c _ => hcardS c) (fun _ _ => subset_univ _) hD1
      (fun e => hmultS e) hdegS
  have hu : (univ : Finset (Fin m)).card = m := by simp
  rw [hu] at hdegR hpd
  -- transport back into `P`
  have h1 := hch.toResidual
  have h2 := residual_mapEnds h1 emb (fun _ _ => emb.injective.injOn) emb.injective.injOn
    (empty_subset _)
  set ends'' : E ⊕ E' → Finset (Fin n) := Sum.elim ends (mapEnds emb ends'm) with hends''
  have h3 := residual_relabel h2 Sum.inr ends'' (fun c _ => rfl) Sum.inr_injective.injOn
    (empty_subset _)
  rw [image_empty] at h3
  set g'' : E → E ⊕ E' := fun c => if hc : c ∈ X then Sum.inr (g ⟨c, hc⟩) else Sum.inl c
    with hg''
  have hXimg : X.image g'' = ((univ : Finset {c // c ∈ X}).image g).image Sum.inr := by
    ext y
    simp only [mem_image, mem_univ, true_and, hg'']
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨g ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩, by simp [hc]⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c.1, c.2, by simp [c.2]⟩
  have hBd : (Cst + Ab) * D + K * sharpPot 2 m ≤ ((Cst + Ab) + K) * (D + sharpPot 2 m) := by
    nlinarith
  refine ⟨E ⊕ E', inferInstance, g'', ends'', R.image Sum.inr, 𝒲.image (image Sum.inr), ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro c c' h
    by_cases hc : c ∈ X <;> by_cases hc' : c' ∈ X <;> simp only [hg'', hc, hc', dif_pos,
      dif_neg, not_false_eq_true, reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq] at h
    · exact congrArg Subtype.val (hg h)
    · exact h
  · intro c
    simp only [hg'']
    split_ifs with hc
    · show (ends'm (g ⟨c, hc⟩)).image emb = ends c
      rw [hends]; exact hmapS ⟨c, hc⟩
    · rfl
  · intro y hy x hx
    obtain ⟨c', hc', rfl⟩ := mem_image.1 hy
    simp only [hg''] at hx
    split_ifs at hx with hxX
    exact hfr c' hc' ⟨x, hxX⟩ (Sum.inr_injective hx)
  · rw [hXimg]; exact h3.mono (le_refl _)
  · intro y hy
    obtain ⟨c', -, rfl⟩ := mem_image.1 hy
    intro v hv
    obtain ⟨i, -, rfl⟩ := mem_image.1 hv
    exact hembP i
  · intro v
    rw [mdeg_image_eq (A := R) (fun c _ => rfl) Sum.inr_injective.injOn subset_rfl]
    show mdeg (mapEnds emb ends'm) R {v} ≤ _
    by_cases hv : ∃ i, emb i = v
    · obtain ⟨i, rfl⟩ := hv
      rw [mdeg_mapEnds_emb]
      exact (hdegR {i} (by simp)).trans hBd
    · push_neg at hv
      rw [mdeg_mapEnds_emb_out emb ends'm R v hv]
      exact Nat.zero_le _
  · intro v
    refine (pdeg_image_le (ends₁ := mapEnds emb ends'm) Sum.inr (fun c => rfl) 𝒲 {v}).trans ?_
    by_cases hv : ∃ i, emb i = v
    · obtain ⟨i, rfl⟩ := hv
      rw [pdeg_mapEnds_emb]
      exact (hpd {i} (by simp)).trans hBd
    · push_neg at hv
      rw [pdeg_mapEnds_emb_out emb ends'm 𝒲 v hv]
      exact Nat.zero_le _

end RefinedAbsorption.FlatOmni
