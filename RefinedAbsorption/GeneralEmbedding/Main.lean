module
public import RefinedAbsorption.GeneralEmbedding.Greedy

/-!
# Lemma 3.8 of the survey (General Embedding): proof

* `card_image_deg_le`: the `(r-1)`-degree of `φ(W)` is at most the total degree of the new
  pairs plus the degree of `J` (an edge of `W_H` without new vertices is an edge of `H`);
* `generalEmbeddingLemma`: the proof of `GeneralEmbeddingLemma`.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {n r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {ends : ι → Finset (Fin n)} {ℋ : Finset (Finset ι)} {m : Finset ι → ℕ}
  {W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))}

/-- An edge of a supergraph without new vertices is mapped to itself. -/
theorem embedEdge_of_toRight_empty {m' : ℕ} (f : Fin m' → Fin n) {e : Finset (Fin n ⊕ Fin m')}
    (he : e.toRight = ∅) : embedEdge f e = e.toLeft := by
  ext x
  rw [mem_embedEdge, he]
  simp

theorem card_image_deg_le (hends : ∀ x, (ends x).card = r)
    (hsys : IsSupergraphSystem r ends ℋ m W) (hint : IsEdgeIntersecting ends ℋ m W)
    (φ : (H : Finset ι) → Fin (m H) → Fin n) (S : Finset (Fin n)) :
    ((systemImage ℋ m W φ).filter (fun f => S ⊆ f)).card ≤
      totDeg W ℋ φ S + (univ.filter (fun x => S ⊆ ends x)).card := by
  have hsub : (systemImage ℋ m W φ).filter (fun f => S ⊆ f) ⊆
      ((newPairs W ℋ).filter (fun p => S ⊆ pimg φ p)).image (pimg φ) ∪
        (univ.filter (fun x => S ⊆ ends x)).image ends := by
    intro g hg
    obtain ⟨hg1, hSg⟩ := mem_filter.1 hg
    obtain ⟨H, hH, hgH⟩ := mem_biUnion.1 hg1
    obtain ⟨e, he, rfl⟩ := mem_image.1 hgH
    rcases e.toRight.eq_empty_or_nonempty with h | h
    · obtain ⟨x, _, hx⟩ := hint H hH e he
      have hcard : e.toLeft.card = r := by
        have := card_toLeft_add_card_toRight (u := e)
        rw [h, card_empty, add_zero, hsys.uniform H hH e he] at this
        exact this
      have heq : e.toLeft = ends x :=
        eq_of_subset_of_card_le hx (by rw [hends, hcard])
      rw [embedEdge_of_toRight_empty _ h, heq] at hSg ⊢
      exact mem_union_right _ (mem_image.2 ⟨x, mem_filter.2 ⟨mem_univ _, hSg⟩, rfl⟩)
    · refine mem_union_left _ (mem_image.2 ⟨⟨H, e⟩, mem_filter.2 ⟨mem_filter.2
        ⟨mem_sigma.2 ⟨hH, he⟩, h⟩, hSg⟩, rfl⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add card_image_le
    card_image_le))

end RefinedAbsorption

namespace RefinedAbsorption

open Finset

open Classical in
/-- **Lemma 3.8 (General Embedding).** -/
theorem generalEmbeddingLemma : GeneralEmbeddingLemma := by
  intro C r hr hrC γ hγ hγ1
  set c2 : ℝ := (C : ℝ) ^ 2 with hc2
  set Q : ℝ := max 2 (4 * (C * 2 ^ (3 * r + 1) * (r : ℝ) ^ r) / γ) with hQdef
  set K : ℝ := Kseq Q c2 (r - 1) with hK
  have hQ2 : 2 ≤ Q := le_max_left _ _
  have hc20 : 0 ≤ c2 := by positivity
  have hK0 : 0 ≤ K := Kseq_nonneg (by linarith) hc20 _
  set C' : ℝ := max (1 + c2 + K) (4 * (C * (c2 + K) * (r : ℝ) ^ r) / γ) with hC'def
  have hC'1 : 1 ≤ C' := le_trans (by linarith) (le_max_left _ _)
  refine ⟨C', hC'1, ?_⟩
  intro n G ι _ _ ends ℋ m W D hn hG hends hendsG hdeg hDn href hsys hint hcb hcount
  have hC1 : 1 ≤ C := by omega
  have hbd : ∀ H ∈ ℋ, (W H).card ≤ C := fun H hH => (hcb H hH).1
  have hC' : 4 * (C * ((C : ℝ) ^ 2 + Kseq Q ((C : ℝ) ^ 2) (r - 1)) * (r : ℝ) ^ r) ≤ γ * C' := by
    have : 4 * (C * (c2 + K) * (r : ℝ) ^ r) / γ ≤ C' := le_max_right _ _
    rw [div_le_iff₀ hγ] at this
    linarith
  have hQγ : 4 * (C * 2 ^ (3 * r + 1) * (r : ℝ) ^ r) ≤ γ * Q := by
    have : 4 * (C * 2 ^ (3 * r + 1) * (r : ℝ) ^ r) / γ ≤ Q := le_max_right _ _
    rw [div_le_iff₀ hγ] at this
    linarith
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨x₀⟩⟩
  · -- `J` has no edges: every `W_H` is empty
    have hW : ∀ H ∈ ℋ, W H = ∅ := by
      intro H hH
      rw [eq_empty_iff_forall_notMem]
      intro e he
      obtain ⟨x, _, _⟩ := hint H hH e he
      exact hι.false x
    have hex : ∀ H ∈ ℋ, ∃ f : Fin (m H) → Fin n, IsHostEmbedding G ends H (W H) f := by
      intro H hH
      have hpos : (0 : ℝ) < γ * (n : ℝ) ^ (m H) := by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      have := hpos.trans_le (hcount H hH)
      obtain ⟨f, hf⟩ := card_pos.1 (by exact_mod_cast this)
      exact ⟨f, (mem_filter.1 hf).2⟩
    refine ⟨fun H => if hH : H ∈ ℋ then (hex H hH).choose else fun _ => ⟨0, hn⟩,
      fun H hH => ?_, fun H₁ hH₁ _ _ _ e₁ he₁ => ?_, fun S hS => ?_⟩
    · simp only [dif_pos hH]; exact (hex H hH).choose_spec
    · rw [hW H₁ hH₁] at he₁; exact absurd he₁ (notMem_empty _)
    · have hsi : systemImage ℋ m W
          (fun H => if hH : H ∈ ℋ then (hex H hH).choose else fun _ => ⟨0, hn⟩) = ∅ := by
        unfold systemImage
        rw [← subset_empty]
        intro g hg
        obtain ⟨H, hH, hg⟩ := mem_biUnion.1 hg
        rw [hW H hH, image_empty] at hg
        exact hg
      rw [hsi, filter_empty, card_empty, Nat.cast_zero]
      have h0 := hdeg S hS
      have : (0 : ℝ) ≤ D := le_trans (Nat.cast_nonneg _) h0
      positivity
  · -- `J` has an edge, so `D ≥ 1`
    have hD1 : 1 ≤ D := by
      obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq (s := ends x₀) (n := r - 1)
        (by rw [hends]; omega)
      have h := hdeg S (by omega)
      have hpos : 0 < (univ.filter (fun x => S ⊆ ends x)).card :=
        card_pos.2 ⟨x₀, mem_filter.2 ⟨mem_univ _, hS⟩⟩
      have : (1 : ℝ) ≤ (univ.filter (fun x => S ⊆ ends x)).card := by exact_mod_cast hpos
      linarith
    have hC'0 : 0 < C' := by linarith
    obtain ⟨φ, hacc, hemb, hdist⟩ := greedy_embedding hγ hQ2 hD1 hn hr hC1 hends hdeg href
      hsys hint hbd hC'0 hDn hC' hQγ hcount ℋ subset_rfl
    refine ⟨φ, hemb, hdist, fun S hS => ?_⟩
    have h1 := card_image_deg_le hends hsys hint φ S
    have h2 := totDeg_bound (by linarith) hends hdeg href hint hbd subset_rfl hacc S hS.le
    have h3 := hdeg S hS
    have hSc : S.card = r - 1 := by omega
    rw [hSc, show r - 1 - (r - 1) = 0 by omega, pow_zero, mul_one] at h2
    have h4 : (((systemImage ℋ m W φ).filter (fun f => S ⊆ f)).card : ℝ) ≤
        (c2 + K) * D + D := by
      have := Nat.cast_le (α := ℝ) |>.2 h1
      push_cast at this
      linarith
    have h5 : (1 + c2 + K) * D ≤ C' * D :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    linarith

end RefinedAbsorption
