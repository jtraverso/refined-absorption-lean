module
public import RefinedAbsorption.Nibble.LocalRound
public import RefinedAbsorption.Nibble.Iterate

/-!
# Iterating the nibble via the Local Lemma

`nibble_iterate_lll` is `nibble_iterate` with `nibble_round` replaced by `nibble_round_lll`:
the hypotheses bound the size of the test sets and the number of test sets through a vertex,
instead of `|V|` and `|𝒯|`.
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset

variable {α : Type*} [DecidableEq α]

/-- **The iterated nibble, via the Local Lemma.**  No bound on `|V|` or `|𝒯|` is needed. -/
theorem nibble_iterate_lll {E : Finset (Finset α)} {V : Finset α} {k L R : ℕ}
    {D0 e0 C θ η τ ζ : ℝ} (𝒯 : Finset (Finset α))
    (hk2 : 2 ≤ k) (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ v ∈ V, D0 * (1 - e0) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D0 * (1 + e0))
    (hcod : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ C)
    (hD0 : 0 < D0) (hC : 0 < C) (he0 : 0 ≤ e0) (hθ0 : 0 < θ) (hθ : k * θ ≤ 1 / 4) (hη0 : 0 < η)
    (hη : η ≤ 1) (hτ : 0 < τ) (hζ : 160 * k * θ ^ 2 ≤ ζ) {M : ℝ}
    (hM : 1 ≤ M) (h𝒯size : ∀ T ∈ 𝒯, (T.card : ℝ) ≤ M)
    (h𝒯mult : ∀ w : α, ((𝒯.filter (fun T => w ∈ T)).card : ℝ) ≤ M)
    (hrounds : ∀ i < R, 1 ≤ D0 * (1 - (k - 1) * θ) ^ i ∧ k * C ≤ D0 * (1 - (k - 1) * θ) ^ i / 2 ∧
      errSeq k θ η C D0 e0 i ≤ 1 / 4 ∧
      4 * ((2 * θ) ^ L
        + 2 * Real.exp (-(θ * η ^ 2 * (D0 * (1 - (k - 1) * θ) ^ i) / (16 * k ^ 2 * C)))
        + (Real.exp (-(θ * τ / (512 * k))) + Real.exp (-(ζ * τ)))) *
        ((k * (M + 1) * (2 * (D0 * (1 - (k - 1) * θ) ^ i)) ^ 2) *
          ((k * k * (2 * (D0 * (1 - (k - 1) * θ) ^ i))) * (M + 1)) + 1) ≤ 1) :
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
      have hkEi : ∀ F ∈ Ei, F.card = k := fun F hF => hk F (hEi hF)
      have hcodi : ∀ u v : α, u ≠ v → (codeg Ei u v : ℝ) ≤ C := by
        intro u v huv
        refine le_trans ?_ (hcod u v huv)
        exact_mod_cast card_le_card (filter_subset_filter _ hEi)
      obtain ⟨S, hSEi, hSdeg, hScov, hSwaste⟩ := nibble_round_lll 𝒯 hk2 hkEi hEiVi hdegi hcodi
        hD1 hC hCD hei0 hei hθ0 hθ hη0 hη hζ hM h𝒯size h𝒯mult hprob
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
