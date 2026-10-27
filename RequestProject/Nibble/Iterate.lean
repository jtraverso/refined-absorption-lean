module
public import RequestProject.Nibble.Round

/-!
# Iterating the nibble

We apply `nibble_round` `R` times.  After round `i` the hypergraph has degrees
`D_i (1 ± e_i)` with `D_i = D_0 (1 - (k-1)θ)^i` and `e_{i+1} = e_i + 4kθ e_i +
4k²θ(C/D_i + θ) + 2θη`.  The isolated chosen edges of all rounds form a matching `M`; every
test set `T` keeps at most `(1-θ/2)^R |T ∩ V| + τ + R ζ' |T ∩ V|` vertices uncovered by `M`, where
`ζ' = 2k(1+kL)ζ` (`nibble_iterate`).
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset

variable {α : Type*} [DecidableEq α]

/-- The error sequence of the iterated nibble. -/
noncomputable def errSeq (k θ η C D0 e0 : ℝ) : ℕ → ℝ
  | 0 => e0
  | i + 1 => errSeq k θ η C D0 e0 i + 4 * k * θ * errSeq k θ η C D0 e0 i +
      4 * k ^ 2 * θ * (C / (D0 * (1 - (k - 1) * θ) ^ i) + θ) + 2 * θ * η

theorem errSeq_nonneg {k θ η C D0 e0 : ℝ} (hD0 : 0 ≤ D0) (hx : 0 ≤ 1 - (k - 1) * θ)
    (hC : 0 ≤ C) (he0 : 0 ≤ e0) (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hk : 0 ≤ k) :
    ∀ i, 0 ≤ errSeq k θ η C D0 e0 i
  | 0 => he0
  | i + 1 => by
    have ih := errSeq_nonneg hD0 hx hC he0 hθ hη hk i
    have : 0 ≤ C / (D0 * (1 - (k - 1) * θ) ^ i) := div_nonneg hC (by positivity)
    simp only [errSeq]
    positivity

/-- The invariant tracked for every test set: `a = |T ∩ V_i|`, `u` the number of vertices of
`T ∩ V` not covered by the matching. -/
def TestInv (τ θ ζ' X0 : ℝ) (i : ℕ) (a u : ℝ) : Prop :=
  (τ ≤ a ∧ a ≤ (1 - θ / 2) ^ i * X0 ∧ u - a ≤ i * ζ' * X0) ∨ (a < τ ∧ u < τ + i * ζ' * X0)

theorem testInv_zero {τ θ ζ' X0 : ℝ} : TestInv τ θ ζ' X0 0 X0 X0 := by
  unfold TestInv
  by_cases h : τ ≤ X0
  · left; simp [h]
  · right; push_neg at h; simp [h]

theorem testInv_succ {τ θ ζ' X0 : ℝ} {i : ℕ} {a a' u u' w : ℝ} (hθ1 : θ ≤ 1)
    (hζ : 0 ≤ ζ') (hX0 : 0 ≤ X0)
    (haX : a ≤ X0) (ha' : a' ≤ a) (hw : w ≤ a - a') (hu : u' ≤ u - a + a' + w)
    (hround : τ ≤ a → a' ≤ (1 - θ / 2) * a ∧ w ≤ ζ' * a)
    (hinv : TestInv τ θ ζ' X0 i a u) : TestInv τ θ ζ' X0 (i + 1) a' u' := by
  unfold TestInv at hinv ⊢
  push_cast
  rcases hinv with ⟨hτa, haq, hua⟩ | ⟨haτ, huτ⟩
  · obtain ⟨h1, h2⟩ := hround hτa
    have hq : 0 ≤ 1 - θ / 2 := by linarith
    have ha1 : a' ≤ (1 - θ / 2) ^ (i + 1) * X0 := by
      rw [pow_succ]
      calc a' ≤ (1 - θ / 2) * a := h1
        _ ≤ (1 - θ / 2) * ((1 - θ / 2) ^ i * X0) := by gcongr
        _ = _ := by ring
    have hwX : w ≤ ζ' * X0 := h2.trans (by gcongr)
    have hg : u' - a' ≤ (i + 1) * ζ' * X0 := by nlinarith
    by_cases hτ' : τ ≤ a'
    · left; exact ⟨hτ', ha1, hg⟩
    · right
      push_neg at hτ'
      exact ⟨hτ', by linarith⟩
  · right
    refine ⟨lt_of_le_of_lt ha' haτ, ?_⟩
    have : 0 ≤ ζ' * X0 := mul_nonneg hζ hX0
    nlinarith

theorem testInv_final {τ θ ζ' X0 : ℝ} {i : ℕ} {a u : ℝ} (hθ1 : θ ≤ 1)
    (hX0 : 0 ≤ X0) (hτ : 0 ≤ τ) (hinv : TestInv τ θ ζ' X0 i a u) :
    u ≤ (1 - θ / 2) ^ i * X0 + τ + i * ζ' * X0 := by
  have hq : 0 ≤ (1 - θ / 2) ^ i * X0 := mul_nonneg (pow_nonneg (by linarith) _) hX0
  rcases hinv with ⟨_, h2, h3⟩ | ⟨_, h2⟩ <;> linarith

/-- Cardinality bookkeeping for one round, for a test set `T`. -/
theorem round_card_facts {V Vi : Finset α} {Mi S : Finset (Finset α)} (T : Finset α)
    (hViV : Vi ⊆ V) (hMVi : ∀ F ∈ Mi, Disjoint F Vi) :
    ((T ∩ (Vi \ cov S)).card : ℝ) ≤ (T ∩ Vi).card ∧
    ((waste S ∩ (T ∩ Vi)).card : ℝ) ≤ (T ∩ Vi).card - (T ∩ (Vi \ cov S)).card ∧
    (((T ∩ V) \ cov (Mi ∪ iso S)).card : ℝ) ≤ ((T ∩ V) \ cov Mi).card - (T ∩ Vi).card +
      (T ∩ (Vi \ cov S)).card + (waste S ∩ (T ∩ Vi)).card := by
  have hsub1 : T ∩ (Vi \ cov S) ⊆ T ∩ Vi := inter_subset_inter_left sdiff_subset
  have hdiff : (T ∩ Vi) \ (T ∩ (Vi \ cov S)) = (T ∩ Vi) ∩ cov S := by
    ext x; simp only [mem_sdiff, mem_inter]; tauto
  have hc1 : ((T ∩ Vi) \ (T ∩ (Vi \ cov S))).card + (T ∩ (Vi \ cov S)).card = (T ∩ Vi).card :=
    card_sdiff_add_card_eq_card hsub1
  have hwsub : waste S ∩ (T ∩ Vi) ⊆ (T ∩ Vi) ∩ cov S := by
    intro x hx
    rw [mem_inter] at hx ⊢
    exact ⟨hx.2, (mem_sdiff.1 hx.1).1⟩
  refine ⟨by exact_mod_cast card_le_card hsub1, ?_, ?_⟩
  · have := card_le_card hwsub
    rw [← hdiff] at this
    have h' : ((waste S ∩ (T ∩ Vi)).card : ℝ) ≤ ((T ∩ Vi) \ (T ∩ (Vi \ cov S))).card := by
      exact_mod_cast this
    have hc1' : (((T ∩ Vi) \ (T ∩ (Vi \ cov S))).card : ℝ) + (T ∩ (Vi \ cov S)).card =
        (T ∩ Vi).card := by exact_mod_cast hc1
    linarith
  · set U := (T ∩ V) \ cov Mi
    have hcovU : cov (Mi ∪ iso S) = cov Mi ∪ cov (iso S) := by
      unfold cov; rw [union_biUnion]
    have hU' : (T ∩ V) \ cov (Mi ∪ iso S) = U \ cov (iso S) := by
      rw [hcovU]; ext x; simp only [U, mem_sdiff, mem_union]; tauto
    have hXiU : T ∩ Vi ⊆ U := by
      intro x hx
      rw [mem_inter] at hx
      refine mem_sdiff.2 ⟨mem_inter.2 ⟨hx.1, hViV hx.2⟩, fun hc => ?_⟩
      obtain ⟨F, hF, hxF⟩ := mem_cov.1 hc
      exact disjoint_left.1 (hMVi F hF) hxF hx.2
    have hkey : ((T ∩ Vi) ∩ cov S) \ (waste S ∩ (T ∩ Vi)) ⊆ U ∩ cov (iso S) := by
      intro x hx
      simp only [mem_sdiff, mem_inter] at hx
      refine mem_inter.2 ⟨hXiU (mem_inter.2 ⟨hx.1.1.1, hx.1.1.2⟩), ?_⟩
      by_contra hc
      exact hx.2 ⟨mem_sdiff.2 ⟨hx.1.2, hc⟩, hx.1.1.1, hx.1.1.2⟩
    have hc2 : (U \ cov (iso S)).card + (U ∩ cov (iso S)).card = U.card := by
      have := card_sdiff_add_card_inter U (cov (iso S)); exact this
    have hc3 : (((T ∩ Vi) ∩ cov S) \ (waste S ∩ (T ∩ Vi))).card + (waste S ∩ (T ∩ Vi)).card =
        ((T ∩ Vi) ∩ cov S).card := card_sdiff_add_card_eq_card hwsub
    have hc4 := card_le_card hkey
    rw [hU']
    rw [← hdiff] at hc3
    have hc2' : ((U \ cov (iso S)).card : ℝ) + (U ∩ cov (iso S)).card = U.card := by
      exact_mod_cast hc2
    have hc3' : ((((T ∩ Vi) ∩ cov S) \ (waste S ∩ (T ∩ Vi))).card : ℝ) +
        (waste S ∩ (T ∩ Vi)).card = ((T ∩ Vi) \ (T ∩ (Vi \ cov S))).card := by
      rw [← hdiff]; exact_mod_cast hc3
    have hc4' : ((((T ∩ Vi) ∩ cov S) \ (waste S ∩ (T ∩ Vi))).card : ℝ) ≤
        (U ∩ cov (iso S)).card := by exact_mod_cast hc4
    have hc1' : (((T ∩ Vi) \ (T ∩ (Vi \ cov S))).card : ℝ) + (T ∩ (Vi \ cov S)).card =
        (T ∩ Vi).card := by exact_mod_cast hc1
    linarith

/-- **The iterated nibble.** -/
theorem nibble_iterate {E : Finset (Finset α)} {V : Finset α} {k L R : ℕ}
    {D0 e0 C θ η τ ζ : ℝ} (𝒯 : Finset (Finset α))
    (hk2 : 2 ≤ k) (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ v ∈ V, D0 * (1 - e0) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D0 * (1 + e0))
    (hcod : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ C)
    (hD0 : 0 < D0) (hC : 0 < C) (he0 : 0 ≤ e0) (hθ0 : 0 < θ) (hθ : k * θ ≤ 1 / 4) (hη0 : 0 < η)
    (hη : η ≤ 1) (hτ : 0 < τ) (hζ : 160 * k * θ ^ 2 ≤ ζ)
    (hrounds : ∀ i < R, 1 ≤ D0 * (1 - (k - 1) * θ) ^ i ∧ k * C ≤ D0 * (1 - (k - 1) * θ) ^ i / 2 ∧
      errSeq k θ η C D0 e0 i ≤ 1 / 4 ∧
      V.card * (2 * θ) ^ L
        + 2 * V.card * Real.exp (-(θ * η ^ 2 * (D0 * (1 - (k - 1) * θ) ^ i) / (16 * k ^ 2 * C)))
        + 𝒯.card * (Real.exp (-(θ * τ / (512 * k))) + Real.exp (-(ζ * τ))) < 1) :
    ∃ M ⊆ E, (∀ F₁ ∈ M, ∀ F₂ ∈ M, F₁ ≠ F₂ → Disjoint F₁ F₂) ∧
      ∀ T ∈ 𝒯, (((T ∩ V) \ cov M).card : ℝ) ≤
        (1 - θ / 2) ^ R * (T ∩ V).card + τ + R * (2 * k * (1 + k * L) * ζ) * (T ∩ V).card := by
  classical
  set ζ' := 2 * k * (1 + k * L) * ζ with hζ'
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hζ0 : 0 ≤ ζ := le_trans (by positivity) hζ
  have hζ'0 : 0 ≤ ζ' := by positivity
  have hθ1 : θ ≤ 1 := by nlinarith
  have hstate : ∀ i, i ≤ R → ∃ Ei ⊆ E, ∃ Vi ⊆ V, ∃ Mi ⊆ E,
      (∀ F ∈ Ei, F ⊆ Vi) ∧
      (∀ v ∈ Vi, D0 * (1 - (k - 1) * θ) ^ i * (1 - errSeq k θ η C D0 e0 i) ≤ (star Ei v).card ∧
        ((star Ei v).card : ℝ) ≤ D0 * (1 - (k - 1) * θ) ^ i * (1 + errSeq k θ η C D0 e0 i)) ∧
      (∀ F₁ ∈ Mi, ∀ F₂ ∈ Mi, F₁ ≠ F₂ → Disjoint F₁ F₂) ∧
      (∀ F ∈ Mi, Disjoint F Vi) ∧
      (∀ T ∈ 𝒯, TestInv τ θ ζ' (T ∩ V).card i (T ∩ Vi).card ((T ∩ V) \ cov Mi).card) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨E, Subset.rfl, V, Subset.rfl, ∅, empty_subset _, hEV, ?_, by simp, by simp, ?_⟩
      · intro v hv; simpa [errSeq] using hdeg v hv
      · intro T _
        have : cov (∅ : Finset (Finset α)) = ∅ := by simp [cov]
        rw [this, sdiff_empty]
        exact testInv_zero
    | succ i ih =>
      intro hi
      obtain ⟨Ei, hEi, Vi, hVi, Mi, hMi, hEiVi, hdegi, hMdisj, hMVi, hinv⟩ := ih (by omega)
      obtain ⟨hD1, hCD, hei, hprob⟩ := hrounds i (by omega)
      have hei0 : 0 ≤ errSeq k θ η C D0 e0 i :=
        errSeq_nonneg hD0.le (by nlinarith) hC.le he0 hθ0.le hη0.le (by linarith) i
      have hprob' : Vi.card * (2 * θ) ^ L
          + 2 * Vi.card * Real.exp (-(θ * η ^ 2 * (D0 * (1 - (k - 1) * θ) ^ i) / (16 * k ^ 2 * C)))
          + 𝒯.card * (Real.exp (-(θ * τ / (512 * k))) + Real.exp (-(ζ * τ))) < 1 := by
        have hc : (Vi.card : ℝ) ≤ V.card := by exact_mod_cast card_le_card hVi
        have h1 : (Vi.card : ℝ) * (2 * θ) ^ L ≤ V.card * (2 * θ) ^ L := by gcongr
        have h2 : 2 * (Vi.card : ℝ) *
            Real.exp (-(θ * η ^ 2 * (D0 * (1 - (k - 1) * θ) ^ i) / (16 * k ^ 2 * C))) ≤
            2 * V.card *
            Real.exp (-(θ * η ^ 2 * (D0 * (1 - (k - 1) * θ) ^ i) / (16 * k ^ 2 * C))) := by
          gcongr
        linarith
      have hkEi : ∀ F ∈ Ei, F.card = k := fun F hF => hk F (hEi hF)
      have hcodi : ∀ u v : α, u ≠ v → (codeg Ei u v : ℝ) ≤ C := by
        intro u v huv
        refine le_trans ?_ (hcod u v huv)
        exact_mod_cast card_le_card (filter_subset_filter _ hEi)
      obtain ⟨S, hSEi, hSdeg, hScov, hSwaste⟩ := nibble_round 𝒯 hk2 hkEi hEiVi hdegi hcodi hD1
        hC hCD hei0 hei hθ0 hθ hη0 hη hζ hprob'
      have hcovS : cov S ⊆ Vi := cov_subset_of_subset hSEi hEiVi
      refine ⟨nextE Ei S, (filter_subset _ _).trans hEi, Vi \ cov S, sdiff_subset.trans hVi,
        Mi ∪ iso S, union_subset hMi ((filter_subset _ _).trans (hSEi.trans hEi)), ?_, ?_, ?_, ?_,
        ?_⟩
      · intro F hF
        rw [nextE, mem_filter] at hF
        intro x hx
        exact mem_sdiff.2 ⟨hEiVi F hF.1 hx, disjoint_left.1 hF.2 hx⟩
      · intro v hv
        have := hSdeg v hv
        simp only [errSeq, pow_succ]
        constructor
        · convert this.1 using 1; ring
        · convert this.2 using 1; ring
      · intro F₁ hF₁ F₂ hF₂ hne
        rcases mem_union.1 hF₁ with h1 | h1 <;> rcases mem_union.1 hF₂ with h2 | h2
        · exact hMdisj F₁ h1 F₂ h2 hne
        · have hF2S := (mem_filter.1 h2).1
          exact disjoint_of_subset_right (hEiVi F₂ (hSEi hF2S)) (hMVi F₁ h1)
        · have hF1S := (mem_filter.1 h1).1
          exact (disjoint_of_subset_right (hEiVi F₁ (hSEi hF1S)) (hMVi F₂ h2)).symm
        · exact (mem_filter.1 h1).2 F₂ (mem_filter.1 h2).1 hne.symm
      · intro F hF
        rcases mem_union.1 hF with h | h
        · exact disjoint_of_subset_right sdiff_subset (hMVi F h)
        · rw [disjoint_left]
          intro x hxF hx
          exact (mem_sdiff.1 hx).2 (mem_cov.2 ⟨F, (mem_filter.1 h).1, hxF⟩)
      · intro T hT
        obtain ⟨hc1, hc2, hc3⟩ := round_card_facts (V := V) (S := S) T hVi hMVi
        refine testInv_succ hθ1 hζ'0 (Nat.cast_nonneg _) ?_ hc1 hc2 hc3
          ?_ (hinv T hT)
        · exact_mod_cast card_le_card (inter_subset_inter_left hVi)
        · intro hτT
          refine ⟨?_, hSwaste T hT hτT⟩
          have h := hScov T hT hτT
          have he : T ∩ (Vi \ cov S) = (T ∩ Vi) \ cov S := by
            ext x; simp only [mem_inter, mem_sdiff]; tauto
          rw [he]; exact h
  obtain ⟨_, _, VR, _, M, hM, _, _, hMdisj, _, hinv⟩ := hstate R le_rfl
  refine ⟨M, hM, hMdisj, fun T hT => ?_⟩
  exact testInv_final hθ1 (Nat.cast_nonneg _) hτ.le (hinv T hT)

end RefinedAbsorption.Nibble
