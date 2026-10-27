module
public import RequestProject.Nibble.LLL

/-!
# Closing lemma: an `A₀`-perfect matching from many options per vertex (Local Lemma)

Every vertex `a ∈ A₀` has a set `O a` of `t` options (labelled edges containing `a` and no other
vertex of `A₀`); the option sets are pairwise disjoint, and every vertex `v ∉ A₀` lies in at most
`Δ` options in total (`load`).  If `t` is large compared with `Δ`, there is a choice of one option
per vertex of `A₀` such that the chosen options are pairwise vertex-disjoint.

The proof keeps every option independently with probability `p` and applies the symmetric Local
Lemma to the events "no option of `a` is kept" and "two intersecting options of different
vertices are both kept".  This is the closing step (Lemma 3.4 of Delcourt–Postle,
arXiv:2204.08981, with no forbidden configurations) used for Theorem 2.8.
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset RefinedAbsorption.Nibble

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- The number of options (over all `a ∈ A₀`) containing the vertex `v`. -/
def load (ends : E → Finset V) (A₀ : Finset V) (O : V → Finset E) (v : V) : ℕ :=
  ∑ a ∈ A₀, ((O a).filter (fun e => v ∈ ends e)).card

/-- The pairs of intersecting options of different vertices. -/
noncomputable def badPairs (ends : E → Finset V) (A₀ : Finset V) (O : V → Finset E) :
    Finset (E × E) := by
  classical
  exact ((A₀.biUnion O) ×ˢ (A₀.biUnion O)).filter (fun pr =>
    (¬ ∃ a ∈ A₀, pr.1 ∈ O a ∧ pr.2 ∈ O a) ∧ ¬ Disjoint (ends pr.1) (ends pr.2))

theorem card_partners_le (ends : E → Finset V) (A₀ : Finset V) (O : V → Finset E) (r : ℕ)
    (Δ : ℝ) (hsep : ∀ a ∈ A₀, ∀ e ∈ O a, ∀ a' ∈ A₀, a' ∈ ends e → a' = a)
    (hcard : ∀ a ∈ A₀, ∀ e ∈ O a, (ends e).card ≤ r)
    (hload : ∀ v, v ∉ A₀ → (load ends A₀ O v : ℝ) ≤ Δ) (hΔ : 0 ≤ Δ)
    {f : E} (a : V) (ha : a ∈ A₀) (hf : f ∈ O a) :
    ((A₀.biUnion O).filter (fun f' => (¬ ∃ b ∈ A₀, f ∈ O b ∧ f' ∈ O b) ∧
        ¬ Disjoint (ends f) (ends f'))).card ≤ (r : ℝ) * Δ := by
  classical
  set T := (ends f).filter (fun v => v ∉ A₀) with hT
  have hsub : (A₀.biUnion O).filter (fun f' => (¬ ∃ b ∈ A₀, f ∈ O b ∧ f' ∈ O b) ∧
      ¬ Disjoint (ends f) (ends f')) ⊆
      T.biUnion (fun v => A₀.biUnion (fun a' => (O a').filter (fun e => v ∈ ends e))) := by
    intro f' hf'
    rw [mem_filter] at hf'
    obtain ⟨hf'E, hno, hnd⟩ := hf'
    obtain ⟨a', ha', hf'a'⟩ := mem_biUnion.1 hf'E
    obtain ⟨v, hvf, hvf'⟩ := not_disjoint_iff.1 hnd
    have hvA : v ∉ A₀ := by
      intro hvA
      have h1 := hsep a ha f hf v hvA hvf
      have h2 := hsep a' ha' f' hf'a' v hvA hvf'
      exact hno ⟨a, ha, hf, h1 ▸ h2 ▸ hf'a'⟩
    exact mem_biUnion.2 ⟨v, mem_filter.2 ⟨hvf, hvA⟩,
      mem_biUnion.2 ⟨a', ha', mem_filter.2 ⟨hf'a', hvf'⟩⟩⟩
  have h1 := card_le_card hsub
  have h2 : (T.biUnion (fun v => A₀.biUnion
      (fun a' => (O a').filter (fun e => v ∈ ends e)))).card ≤ ∑ v ∈ T, load ends A₀ O v := by
    refine card_biUnion_le.trans (sum_le_sum fun v _ => ?_)
    exact card_biUnion_le
  have h3 : ((∑ v ∈ T, load ends A₀ O v : ℕ) : ℝ) ≤ ∑ v ∈ T, Δ := by
    push_cast
    exact sum_le_sum fun v hv => hload v (mem_filter.1 hv).2
  have h4 : (T.card : ℝ) ≤ r := by
    exact_mod_cast (card_filter_le _ _).trans (hcard a ha f hf)
  rw [sum_const, nsmul_eq_mul] at h3
  calc _ ≤ ((∑ v ∈ T, load ends A₀ O v : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
    _ ≤ T.card * Δ := h3
    _ ≤ r * Δ := by gcongr

/-- **Closing lemma.** -/
theorem closing_lll (ends : E → Finset V) (A₀ : Finset V) (O : V → Finset E) (r t : ℕ)
    (Δ p : ℝ) (hOcard : ∀ a ∈ A₀, (O a).card = t)
    (hOdisj : ∀ a ∈ A₀, ∀ a' ∈ A₀, a ≠ a' → Disjoint (O a) (O a'))
    (hsep : ∀ a ∈ A₀, ∀ e ∈ O a, ∀ a' ∈ A₀, a' ∈ ends e → a' = a)
    (hcard : ∀ a ∈ A₀, ∀ e ∈ O a, (ends e).card ≤ r)
    (hload : ∀ v, v ∉ A₀ → (load ends A₀ O v : ℝ) ≤ Δ)
    (hΔ : 0 ≤ Δ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 4 * max ((1 - p) ^ t) (p ^ 2) * (2 + 2 * r * Δ * (t + 2) + 1) ≤ 1) :
    ∃ M : Finset E, M ⊆ A₀.biUnion O ∧ (∀ a ∈ A₀, ∃ e ∈ M, e ∈ O a) ∧
      ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → Disjoint (ends e) (ends e') := by
  classical
  set Eall := A₀.biUnion O with hEall
  set P := badPairs ends A₀ O with hP
  have hPmem : ∀ pr, pr ∈ P ↔ (pr.1 ∈ Eall ∧ pr.2 ∈ Eall) ∧
      (¬ ∃ a ∈ A₀, pr.1 ∈ O a ∧ pr.2 ∈ O a) ∧ ¬ Disjoint (ends pr.1) (ends pr.2) := by
    intro pr
    simp only [hP, badPairs, mem_filter, mem_product]
    rfl
  -- owner uniqueness
  have hown : ∀ e, ∀ a ∈ A₀, ∀ a' ∈ A₀, e ∈ O a → e ∈ O a' → a = a' := by
    intro e a ha a' ha' h1 h2
    by_contra hne
    exact disjoint_left.1 (hOdisj a ha a' ha' hne) h1 h2
  set I : Finset (V ⊕ (E × E)) := A₀.disjSum P with hI
  let Ev : V ⊕ (E × E) → Finset E → Prop := fun i S => match i with
    | Sum.inl a => Disjoint S (O a)
    | Sum.inr pr => ({pr.1, pr.2} : Finset E) ⊆ S
  let Cs : V ⊕ (E × E) → Finset E := fun i => match i with
    | Sum.inl a => O a
    | Sum.inr pr => {pr.1, pr.2}
  set q := max ((1 - p) ^ t) (p ^ 2) with hqdef
  set d : ℝ := 2 + 2 * r * Δ * (t + 2) with hd
  have hq0 : 0 ≤ q := le_max_of_le_right (sq_nonneg p)
  have hd0 : 0 ≤ d := by positivity
  -- partner bounds
  have hpart1 : ∀ f ∈ Eall, ((P.filter (fun pr => pr.1 = f)).card : ℝ) ≤ r * Δ := by
    intro f hf
    obtain ⟨a, ha, hfa⟩ := mem_biUnion.1 hf
    refine le_trans ?_ (card_partners_le ends A₀ O r Δ hsep hcard hload hΔ a ha hfa)
    have : (P.filter (fun pr => pr.1 = f)).card ≤ ((A₀.biUnion O).filter (fun f' =>
        (¬ ∃ b ∈ A₀, f ∈ O b ∧ f' ∈ O b) ∧ ¬ Disjoint (ends f) (ends f'))).card := by
      refine card_le_card_of_injOn (fun pr => pr.2) ?_ ?_
      · intro pr hpr
        rw [coe_filter] at hpr
        obtain ⟨hpr, rfl⟩ := hpr
        rw [hPmem] at hpr
        exact mem_filter.2 ⟨hpr.1.2, hpr.2⟩
      · intro x hx y hy hxy
        rw [coe_filter] at hx hy
        exact Prod.ext (hx.2.trans hy.2.symm) hxy
    exact_mod_cast this
  have hpart2 : ∀ f ∈ Eall, ((P.filter (fun pr => pr.2 = f)).card : ℝ) ≤ r * Δ := by
    intro f hf
    obtain ⟨a, ha, hfa⟩ := mem_biUnion.1 hf
    refine le_trans ?_ (card_partners_le ends A₀ O r Δ hsep hcard hload hΔ a ha hfa)
    have : (P.filter (fun pr => pr.2 = f)).card ≤ ((A₀.biUnion O).filter (fun f' =>
        (¬ ∃ b ∈ A₀, f ∈ O b ∧ f' ∈ O b) ∧ ¬ Disjoint (ends f) (ends f'))).card := by
      refine card_le_card_of_injOn (fun pr => pr.1) ?_ ?_
      · intro pr hpr
        rw [coe_filter] at hpr
        obtain ⟨hpr, rfl⟩ := hpr
        rw [hPmem] at hpr
        refine mem_filter.2 ⟨hpr.1.1, fun ⟨b, hb, h1, h2⟩ => hpr.2.1 ⟨b, hb, h2, h1⟩, ?_⟩
        rw [disjoint_comm]; exact hpr.2.2
      · intro x hx y hy hxy
        rw [coe_filter] at hx hy
        exact Prod.ext hxy (hx.2.trans hy.2.symm)
    exact_mod_cast this
  -- pairs touching a coin set
  have hpairsC : ∀ C : Finset E, C ⊆ Eall →
      ((P.filter (fun pr => ¬ Disjoint C {pr.1, pr.2})).card : ℝ) ≤ C.card * (2 * (r * Δ)) := by
    intro C hC
    have hsub : P.filter (fun pr => ¬ Disjoint C {pr.1, pr.2}) ⊆
        C.biUnion (fun f => P.filter (fun pr => pr.1 = f) ∪ P.filter (fun pr => pr.2 = f)) := by
      intro pr hpr
      rw [mem_filter] at hpr
      obtain ⟨f, hfC, hf⟩ := not_disjoint_iff.1 hpr.2
      rw [mem_insert, mem_singleton] at hf
      refine mem_biUnion.2 ⟨f, hfC, ?_⟩
      rcases hf with hf | hf
      · exact mem_union_left _ (mem_filter.2 ⟨hpr.1, hf.symm⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hpr.1, hf.symm⟩)
    have h1 := (card_le_card hsub).trans card_biUnion_le
    calc ((P.filter (fun pr => ¬ Disjoint C {pr.1, pr.2})).card : ℝ)
        ≤ ((∑ f ∈ C, (P.filter (fun pr => pr.1 = f) ∪ P.filter (fun pr => pr.2 = f)).card : ℕ)
          : ℝ) := by exact_mod_cast h1
      _ ≤ ∑ f ∈ C, (2 * (r * Δ)) := by
        push_cast
        refine sum_le_sum fun f hf => ?_
        have := card_union_le (P.filter (fun pr => pr.1 = f)) (P.filter (fun pr => pr.2 = f))
        have h' : ((P.filter (fun pr => pr.1 = f) ∪ P.filter (fun pr => pr.2 = f)).card : ℝ)
            ≤ (P.filter (fun pr => pr.1 = f)).card + (P.filter (fun pr => pr.2 = f)).card := by
          exact_mod_cast this
        linarith [hpart1 f (hC hf), hpart2 f (hC hf)]
      _ = C.card * (2 * (r * Δ)) := by rw [sum_const, nsmul_eq_mul]
  -- owners of a coin set
  have hownC : ∀ e : E, (A₀.filter (fun a => e ∈ O a)).card ≤ 1 := by
    intro e
    refine card_le_one.2 fun a ha a' ha' => ?_
    rw [mem_filter] at ha ha'
    exact hown e a ha.1 a' ha'.1 ha.2 ha'.2
  have hdisjSum_filter : ∀ (Q : V ⊕ (E × E) → Prop) [DecidablePred Q],
      (I.filter Q).card = (A₀.filter (fun a => Q (Sum.inl a))).card +
        (P.filter (fun pr => Q (Sum.inr pr))).card := by
    intro Q _
    rw [hI, show (A₀.disjSum P).filter Q = (A₀.filter (fun a => Q (Sum.inl a))).disjSum
        (P.filter (fun pr => Q (Sum.inr pr))) by ext x; cases x <;> simp, card_disjSum]
  obtain ⟨S, hSE, hS⟩ := lll_real hp0 hp1 Eall I Ev Cs d
    (by
      intro i hi S hS
      cases i with
      | inl a =>
        show Disjoint S (O a) ↔ Disjoint (S ∩ O a) (O a)
        constructor
        · exact fun h => disjoint_of_subset_left inter_subset_left h
        · intro h
          rw [disjoint_left]
          intro x hxS hxO
          exact disjoint_left.1 h (mem_inter.2 ⟨hxS, hxO⟩) hxO
      | inr pr =>
        show ({pr.1, pr.2} : Finset E) ⊆ S ↔ {pr.1, pr.2} ⊆ S ∩ {pr.1, pr.2}
        constructor
        · exact fun h => subset_inter h subset_rfl
        · exact fun h => h.trans inter_subset_left)
    (by
      intro i hi
      cases i with
      | inl a =>
        have ha : a ∈ A₀ := by simpa [hI] using hi
        show Pr p Eall (fun S => Disjoint S (O a)) ≤ q
        rw [Pr_disjoint p (fun x hx => mem_biUnion.2 ⟨a, ha, hx⟩), hOcard a ha]
        exact le_max_left _ _
      | inr pr =>
        have hpr : pr ∈ P := by simpa [hI] using hi
        have hpr' := (hPmem pr).1 hpr
        have hne : pr.1 ≠ pr.2 := by
          intro h
          obtain ⟨a, ha, hfa⟩ := mem_biUnion.1 hpr'.1.1
          exact hpr'.2.1 ⟨a, ha, hfa, h ▸ hfa⟩
        show Pr p Eall (fun S => ({pr.1, pr.2} : Finset E) ⊆ S) ≤ q
        rw [Pr_subset p (insert_subset hpr'.1.1 (singleton_subset_iff.2 hpr'.1.2)),
          card_pair hne]
        exact le_max_right _ _)
    (by
      intro i hi
      cases i with
      | inl a =>
        have ha : a ∈ A₀ := by simpa [hI] using hi
        rw [hdisjSum_filter]
        have h1 : (A₀.filter (fun a' => ¬ Disjoint (Cs (Sum.inl a)) (Cs (Sum.inl a')))).card
            ≤ 1 := by
          refine card_le_one.2 fun b hb b' hb' => ?_
          rw [mem_filter] at hb hb'
          have e1 : b = a := by
            by_contra hne
            exact hb.2 ((hOdisj a ha b hb.1 (Ne.symm hne)))
          have e2 : b' = a := by
            by_contra hne
            exact hb'.2 ((hOdisj a ha b' hb'.1 (Ne.symm hne)))
          rw [e1, e2]
        have h2 := hpairsC (O a) (fun x hx => mem_biUnion.2 ⟨a, ha, hx⟩)
        rw [hOcard a ha] at h2
        push_cast
        have h1' : ((A₀.filter (fun a' => ¬ Disjoint (Cs (Sum.inl a)) (Cs (Sum.inl a')))).card
            : ℝ) ≤ 1 := by exact_mod_cast h1
        have : ((P.filter (fun pr => ¬ Disjoint (Cs (Sum.inl a)) (Cs (Sum.inr pr)))).card : ℝ)
            ≤ t * (2 * (r * Δ)) := h2
        have hrΔ : 0 ≤ (r : ℝ) * Δ := by positivity
        nlinarith
      | inr pr =>
        have hpr : pr ∈ P := by simpa [hI] using hi
        have hpr' := (hPmem pr).1 hpr
        rw [hdisjSum_filter]
        have h1 : (A₀.filter (fun a' => ¬ Disjoint (Cs (Sum.inr pr)) (Cs (Sum.inl a')))).card
            ≤ 2 := by
          have hsub : A₀.filter (fun a' => ¬ Disjoint (Cs (Sum.inr pr)) (Cs (Sum.inl a'))) ⊆
              A₀.filter (fun a => pr.1 ∈ O a) ∪ A₀.filter (fun a => pr.2 ∈ O a) := by
            intro b hb
            rw [mem_filter] at hb
            obtain ⟨x, hx, hxO⟩ := not_disjoint_iff.1 hb.2
            change x ∈ ({pr.1, pr.2} : Finset E) at hx
            rw [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact mem_union_left _ (mem_filter.2 ⟨hb.1, hxO⟩)
            · exact mem_union_right _ (mem_filter.2 ⟨hb.1, hxO⟩)
          exact (card_le_card hsub).trans ((card_union_le _ _).trans
            (Nat.add_le_add (hownC _) (hownC _)))
        have hC : ({pr.1, pr.2} : Finset E) ⊆ Eall :=
          insert_subset hpr'.1.1 (singleton_subset_iff.2 hpr'.1.2)
        have h2 := hpairsC _ hC
        have hc2 : (({pr.1, pr.2} : Finset E).card : ℝ) ≤ 2 := by
          exact_mod_cast card_le_two
        have h1' : ((A₀.filter (fun a' => ¬ Disjoint (Cs (Sum.inr pr)) (Cs (Sum.inl a')))).card
            : ℝ) ≤ 2 := by exact_mod_cast h1
        have : ((P.filter (fun pr' => ¬ Disjoint (Cs (Sum.inr pr)) (Cs (Sum.inr pr')))).card : ℝ)
            ≤ (({pr.1, pr.2} : Finset E).card : ℝ) * (2 * (r * Δ)) := h2
        have hrΔ : 0 ≤ (r : ℝ) * Δ := by positivity
        have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
        push_cast
        nlinarith)
    hq0 hd0 (by rw [hd] at *; linarith)
  -- extract the matching
  have hch : ∀ a ∈ A₀, ∃ e, e ∈ O a ∧ e ∈ S := by
    intro a ha
    have h := hS (Sum.inl a) (by simp [hI, ha])
    obtain ⟨e, heS, heO⟩ := not_disjoint_iff.1 h
    exact ⟨e, heO, heS⟩
  let g : A₀ → E := fun a => Classical.choose (hch a.1 a.2)
  have hg : ∀ a : A₀, g a ∈ O a.1 ∧ g a ∈ S := fun a => Classical.choose_spec (hch a.1 a.2)
  refine ⟨A₀.attach.image g, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, -, rfl⟩ := mem_image.1 he
    exact mem_biUnion.2 ⟨a.1, a.2, (hg a).1⟩
  · intro a ha
    exact ⟨g ⟨a, ha⟩, mem_image.2 ⟨⟨a, ha⟩, mem_attach _ _, rfl⟩, (hg ⟨a, ha⟩).1⟩
  · intro e he e' he' hne
    obtain ⟨a, -, rfl⟩ := mem_image.1 he
    obtain ⟨a', -, rfl⟩ := mem_image.1 he'
    by_contra hnd
    have hpr : (g a, g a') ∈ P := by
      rw [hPmem]
      refine ⟨⟨mem_biUnion.2 ⟨a.1, a.2, (hg a).1⟩, mem_biUnion.2 ⟨a'.1, a'.2, (hg a').1⟩⟩,
        ?_, hnd⟩
      rintro ⟨b, hb, h1, h2⟩
      have e1 := hown _ a.1 a.2 b hb (hg a).1 h1
      have e2 := hown _ a'.1 a'.2 b hb (hg a').1 h2
      have : a = a' := Subtype.ext (e1.trans e2.symm)
      exact hne (this ▸ rfl)
    have h := hS (Sum.inr (g a, g a')) (by simp [hI, hpr])
    exact h (insert_subset (hg a).2 (singleton_subset_iff.2 (hg a').2))

end RefinedAbsorption.Pending
