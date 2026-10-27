module
public import RefinedAbsorption.Pending.MultiNibble
public import RefinedAbsorption.Pending.Closing

/-!
# Theorem 2.8 for a fixed `D`: the combinatorial core

`thm28_core` proves the conclusion of Theorem 2.8 (an `A`-perfect matching of `G₁ ∪ G₂`) for one
fixed real `D`, assuming

* the multi-hypergraph local nibble at `D₀ = ⌊D⌋` (`multiNibbleA`, passed as `hNib`), and
* finitely many explicit numerical inequalities `N2`–`N7` between `D`, `D₀`, `α`, `β`, `c`, the
  number `t = ⌈D^{1-α}⌉` of reserve options per vertex and the probability `p`.

These inequalities hold for all large `D` (`Pending/Theorem28.lean`).

Proof.
1. Every `a ∈ A` keeps exactly `t` of its reserve edges (`O a ⊆ G₂`).  Since every edge of `G₂`
   has exactly one vertex in `A`, the option sets are disjoint.
2. For `b ∈ B \ A` the weight of `a` is `w_b(a) = #{e ∈ O a : b ∈ e} ≤ codeg(a,b) ≤ D^{1-β}`, and
   `∑_a w_b(a) ≤ deg_{G₂}(b) ≤ D`.  The test sets are the level sets
   `T_{b,s} = {a ∈ A : w_b(a) ≥ s}`, `1 ≤ s ≤ ⌊D^{1-β}⌋`.
3. The nibble on `G₁` gives a matching `M₁`; let `A₀` be the uncovered part of `A`.  By the layer
   cake formula `∑_{a ∈ A₀} w_b(a) = ∑_s |T_{b,s} ∩ A₀|`, and each term is at most
   `D₀^{-c} |T_{b,s}| + D₀^{β/2}` (large level sets by the nibble, small ones trivially), so the
   load of `b` on the options of `A₀` is at most `ΔB = D₀^{-c} D + ⌊D^{1-β}⌋ D₀^{β/2}`.
4. The closing lemma (`closing_lll`) gives an `A₀`-perfect matching `M₂` inside the options.
5. `M₁ ∪ M₂` is a matching: edges of `G₁` lie in `V₁`, options lie in `V₂`, `V₁ ∩ V₂ = A`, and the
   only vertex of `A` in an option of `a ∈ A₀` is `a`, which `M₁` does not cover.
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset RefinedAbsorption.Faithful2024

/-- **Layer cake formula** for natural weights bounded by `m`. -/
theorem layer_cake {V : Type*} [DecidableEq V] (S : Finset V) (w : V → ℕ) (m : ℕ)
    (hw : ∀ a ∈ S, w a ≤ m) :
    ∑ a ∈ S, w a = ∑ s ∈ Icc 1 m, (S.filter (fun a => s ≤ w a)).card := by
  have h1 : ∀ a ∈ S, w a = ∑ s ∈ Icc 1 m, if s ≤ w a then 1 else 0 := by
    intro a ha
    rw [← card_filter]
    have : (Icc 1 m).filter (fun s => s ≤ w a) = Icc 1 (w a) := by
      ext s
      simp only [mem_filter, mem_Icc]
      have := hw a ha
      constructor <;> intro h <;> omega
    rw [this, Nat.card_Icc]; omega
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [card_filter]

set_option maxHeartbeats 1000000 in
/-- **Theorem 2.8 at a fixed `D`**, from the nibble and explicit numerical conditions. -/
theorem thm28_core {r : ℕ} {β c α D p : ℝ} {D₀ t : ℕ}
    (hNib : ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (ends : E → Finset V)
      (G₁ : Finset E) (A : Finset V) (𝒯 : Finset (Finset V)),
      (∀ f ∈ G₁, (ends f).card = r) →
      (∀ f ∈ G₁, ∀ v ∈ ends f, vdeg ends G₁ v ≤ D₀) →
      (∀ a ∈ A, (D₀ : ℝ) * (1 - (D₀ : ℝ) ^ (-(β / 2))) ≤ vdeg ends G₁ a) →
      (∀ u v, u ≠ v → (codeg2 ends G₁ u v : ℝ) ≤ (D₀ : ℝ) ^ (1 - β / 2)) →
      (∀ T ∈ 𝒯, T ⊆ A) → (∀ T ∈ 𝒯, (T.card : ℝ) ≤ (D₀ : ℝ) ^ 3) →
      (∀ v, ((𝒯.filter (fun T => v ∈ T)).card : ℝ) ≤ (D₀ : ℝ) ^ 3) →
      ∃ M ⊆ G₁, IsMatchingL ends M ∧ ∀ T ∈ 𝒯, (D₀ : ℝ) ^ (β / 2) ≤ T.card →
        ((T.filter (fun a => ∀ f ∈ M, a ∉ ends f)).card : ℝ) ≤ (D₀ : ℝ) ^ (-c) * T.card)
    (hD0 : 0 ≤ D) (hD₀ : D₀ = ⌊D⌋₊) (ht : t = ⌈D ^ (1 - α)⌉₊)
    (N2 : (D₀ : ℝ) * (1 - (D₀ : ℝ) ^ (-(β / 2))) ≤ D * (1 - D ^ (-β)))
    (N3 : D ^ (1 - β) ≤ (D₀ : ℝ) ^ (1 - β / 2))
    (N4 : D ≤ (D₀ : ℝ) ^ 3)
    (N5 : (r : ℝ) * t * ⌊D ^ (1 - β)⌋₊ ≤ (D₀ : ℝ) ^ 3)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N7 : 4 * max ((1 - p) ^ t) (p ^ 2) *
      (2 + 2 * r * ((D₀ : ℝ) ^ (-c) * D + ⌊D ^ (1 - β)⌋₊ * (D₀ : ℝ) ^ (β / 2)) * (t + 2) + 1)
        ≤ 1)
    (V E : Type) [DecidableEq V] [DecidableEq E] (ends : E → Finset V)
    (V₁ V₂ A B : Finset V) (G₁ G₂ : Finset E)
    (hcard : ∀ e ∈ G₁ ∪ G₂, (ends e).card = r)
    (hcod : ∀ u v : V, u ≠ v → (codeg2 ends (G₁ ∪ G₂) u v : ℝ) ≤ D ^ (1 - β))
    (hbip : IsBipartiteHyp ends V₂ G₂ A B)
    (hBdeg : ∀ b ∈ B, (vdeg ends G₂ b : ℝ) ≤ D)
    (hAres : ∀ a ∈ A, D ^ (1 - α) ≤ (vdeg ends G₂ a : ℝ))
    (hV₁ : ∀ e ∈ G₁, ends e ⊆ V₁) (hV : V₁ ∩ V₂ = A)
    (hdeg1 : ∀ v ∈ V₁, (vdeg ends G₁ v : ℝ) ≤ D)
    (hdegA : ∀ a ∈ A, D * (1 - D ^ (-β)) ≤ (vdeg ends G₁ a : ℝ)) :
    ∃ M : Finset E, IsAPerfectMatching ends (G₁ ∪ G₂) M A := by
  classical
  obtain ⟨hV₂, hG₂V, hG₂A⟩ := hbip
  set smax := ⌊D ^ (1 - β)⌋₊ with hsmax
  set ΔB : ℝ := (D₀ : ℝ) ^ (-c) * D + smax * (D₀ : ℝ) ^ (β / 2) with hΔB
  have hΔB0 : 0 ≤ ΔB := by positivity
  -- uniqueness of the `A`-vertex of an edge of `G₂`
  have huniq : ∀ e ∈ G₂, ∀ a ∈ A, ∀ a' ∈ A, a ∈ ends e → a' ∈ ends e → a = a' := by
    intro e he a ha a' ha' h1 h2
    exact card_le_one.1 (hG₂A e he).le a (mem_inter.2 ⟨h1, ha⟩) a' (mem_inter.2 ⟨h2, ha'⟩)
  -- step 1: the options
  have htle : ∀ a ∈ A, t ≤ (G₂.filter (fun e => a ∈ ends e)).card := by
    intro a ha; rw [ht]; exact Nat.ceil_le.2 (hAres a ha)
  let O : V → Finset E := fun a =>
    if h : a ∈ A then Classical.choose (exists_subset_card_eq (htle a h)) else ∅
  have hO : ∀ a ∈ A, O a ⊆ G₂.filter (fun e => a ∈ ends e) ∧ (O a).card = t := by
    intro a ha
    have := Classical.choose_spec (exists_subset_card_eq (htle a ha))
    dsimp only [O]; rw [dif_pos ha]; exact this
  have hOG₂ : ∀ a ∈ A, ∀ e ∈ O a, e ∈ G₂ ∧ a ∈ ends e := fun a ha e he =>
    mem_filter.1 ((hO a ha).1 he)
  have hOnA : ∀ a, a ∉ A → O a = ∅ := by
    intro a ha; dsimp only [O]; rw [dif_neg ha]
  -- step 2: weights
  let w : V → V → ℕ := fun b a => ((O a).filter (fun e => b ∈ ends e)).card
  have hwle : ∀ b ∈ B, b ∉ A → ∀ a ∈ A, w b a ≤ smax := by
    intro b hb hbA a ha
    have hab : a ≠ b := fun h => hbA (h ▸ ha)
    have h1 : w b a ≤ codeg2 ends (G₁ ∪ G₂) a b := by
      refine card_le_card fun e he => ?_
      rw [mem_filter] at he ⊢
      exact ⟨mem_union_right _ (hOG₂ a ha e he.1).1, (hOG₂ a ha e he.1).2, he.2⟩
    exact Nat.le_floor (le_trans (by exact_mod_cast h1) (hcod a b hab))
  have hsumw : ∀ b ∈ B, ((∑ a ∈ A, w b a : ℕ) : ℝ) ≤ D := by
    intro b hb
    have hdisj : (A : Set V).PairwiseDisjoint (fun a => (O a).filter (fun e => b ∈ ends e)) := by
      intro a ha a' ha' hne
      simp only [Function.onFun]
      rw [disjoint_left]
      intro e he he'
      rw [mem_filter] at he he'
      exact hne (huniq e (hOG₂ a ha e he.1).1 a ha a' ha' (hOG₂ a ha e he.1).2
        (hOG₂ a' ha' e he'.1).2)
    have h1 : ∑ a ∈ A, w b a = (A.biUnion (fun a => (O a).filter (fun e => b ∈ ends e))).card :=
      (card_biUnion hdisj).symm
    have h2 : (A.biUnion (fun a => (O a).filter (fun e => b ∈ ends e))).card ≤ vdeg ends G₂ b := by
      refine card_le_card fun e he => ?_
      obtain ⟨a, ha, he⟩ := mem_biUnion.1 he
      rw [mem_filter] at he
      exact mem_filter.2 ⟨(hOG₂ a ha e he.1).1, he.2⟩
    rw [h1]
    exact le_trans (by exact_mod_cast h2) (hBdeg b hb)
  -- the test sets
  set 𝒯 : Finset (Finset V) := ((B \ A) ×ˢ Icc 1 smax).image
    (fun bs => A.filter (fun a => bs.2 ≤ w bs.1 a)) with h𝒯
  have h𝒯A : ∀ T ∈ 𝒯, T ⊆ A := by
    intro T hT
    obtain ⟨bs, -, rfl⟩ := mem_image.1 hT
    exact filter_subset _ _
  have hD₀3 : ∀ x : ℝ, x ≤ D → x ≤ (D₀ : ℝ) ^ 3 := fun x hx => hx.trans N4
  have h𝒯size : ∀ T ∈ 𝒯, (T.card : ℝ) ≤ (D₀ : ℝ) ^ 3 := by
    intro T hT
    obtain ⟨⟨b, s⟩, hbs, rfl⟩ := mem_image.1 hT
    rw [mem_product, mem_sdiff, mem_Icc] at hbs
    refine hD₀3 _ (le_trans ?_ (hsumw b hbs.1.1))
    have h1 : (A.filter (fun a => s ≤ w b a)).card ≤ ∑ a ∈ A.filter (fun a => s ≤ w b a), w b a :=
      by
        rw [card_eq_sum_ones]
        exact sum_le_sum fun a ha => le_trans hbs.2.1 (mem_filter.1 ha).2
    have h2 : ∑ a ∈ A.filter (fun a => s ≤ w b a), w b a ≤ ∑ a ∈ A, w b a :=
      sum_le_sum_of_subset (filter_subset _ _)
    exact_mod_cast h1.trans h2
  have h𝒯mult : ∀ v, ((𝒯.filter (fun T => v ∈ T)).card : ℝ) ≤ (D₀ : ℝ) ^ 3 := by
    intro v
    have hsub : 𝒯.filter (fun T => v ∈ T) ⊆ (((O v).biUnion ends) ×ˢ Icc 1 smax).image
        (fun bs => A.filter (fun a => bs.2 ≤ w bs.1 a)) := by
      intro T hT
      rw [mem_filter] at hT
      obtain ⟨⟨b, s⟩, hbs, rfl⟩ := mem_image.1 hT.1
      rw [mem_product, mem_Icc] at hbs
      have hv := mem_filter.1 hT.2
      refine mem_image.2 ⟨(b, s), mem_product.2 ⟨?_, mem_Icc.2 hbs.2⟩, rfl⟩
      have hpos : 0 < w b v := lt_of_lt_of_le hbs.2.1 hv.2
      obtain ⟨e, he⟩ := card_pos.1 hpos
      rw [mem_filter] at he
      exact mem_biUnion.2 ⟨e, he.1, he.2⟩
    have h1 := (card_le_card hsub).trans card_image_le
    rw [card_product, Nat.card_Icc, Nat.add_sub_cancel] at h1
    have h2 : ((O v).biUnion ends).card ≤ r * t := by
      refine card_biUnion_le.trans ?_
      by_cases hvA : v ∈ A
      · refine le_of_eq ?_
        calc ∑ e ∈ O v, (ends e).card = ∑ e ∈ O v, r :=
              sum_congr rfl fun e he => hcard e (mem_union_right _ (hOG₂ v hvA e he).1)
          _ = r * t := by rw [sum_const, (hO v hvA).2, smul_eq_mul, mul_comm]
      · rw [hOnA v hvA, sum_empty]; exact Nat.zero_le _
    have h3 : (𝒯.filter (fun T => v ∈ T)).card ≤ r * t * smax :=
      h1.trans (Nat.mul_le_mul_right _ h2)
    exact le_trans (by exact_mod_cast h3) N5
  -- step 3: the nibble
  obtain ⟨M₁, hM₁G, hM₁m, hM₁T⟩ := hNib V E ends G₁ A 𝒯
    (fun f hf => hcard f (mem_union_left _ hf))
    (fun f hf v hv => by
      rw [hD₀]; exact Nat.le_floor (hdeg1 v (hV₁ f hf hv)))
    (fun a ha => N2.trans (hdegA a ha))
    (fun u v huv => by
      refine le_trans ?_ ((hcod u v huv).trans N3)
      exact_mod_cast card_le_card (filter_subset_filter _ subset_union_left))
    h𝒯A h𝒯size h𝒯mult
  set A₀ := A.filter (fun a => ∀ f ∈ M₁, a ∉ ends f) with hA₀
  have hA₀A : A₀ ⊆ A := filter_subset _ _
  -- the load of `b ∈ B \ A`
  have hloadB : ∀ b ∈ B, b ∉ A → (load ends A₀ O b : ℝ) ≤ ΔB := by
    intro b hb hbA
    have hw := hwle b hb hbA
    have e1 : load ends A₀ O b = ∑ s ∈ Icc 1 smax, (A₀.filter (fun a => s ≤ w b a)).card :=
      layer_cake A₀ (w b) smax fun a ha => hw a (hA₀A ha)
    have e2 : ∑ a ∈ A, w b a = ∑ s ∈ Icc 1 smax, (A.filter (fun a => s ≤ w b a)).card :=
      layer_cake A (w b) smax hw
    have hterm : ∀ s ∈ Icc 1 smax, ((A₀.filter (fun a => s ≤ w b a)).card : ℝ) ≤
        (D₀ : ℝ) ^ (-c) * (A.filter (fun a => s ≤ w b a)).card + (D₀ : ℝ) ^ (β / 2) := by
      intro s hs
      have hT : A.filter (fun a => s ≤ w b a) ∈ 𝒯 :=
        mem_image.2 ⟨(b, s), mem_product.2 ⟨mem_sdiff.2 ⟨hb, hbA⟩, hs⟩, rfl⟩
      have heq : A₀.filter (fun a => s ≤ w b a) =
          (A.filter (fun a => s ≤ w b a)).filter (fun a => ∀ f ∈ M₁, a ∉ ends f) := by
        rw [hA₀]; ext a; simp only [mem_filter]; tauto
      rw [heq]
      have hpos : 0 ≤ (D₀ : ℝ) ^ (-c) * (A.filter (fun a => s ≤ w b a)).card :=
        mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
      by_cases hbig : (D₀ : ℝ) ^ (β / 2) ≤ (A.filter (fun a => s ≤ w b a)).card
      · have := hM₁T _ hT hbig
        have h0 : (0 : ℝ) ≤ (D₀ : ℝ) ^ (β / 2) := by positivity
        linarith
      · push_neg at hbig
        have : (((A.filter (fun a => s ≤ w b a)).filter
            (fun a => ∀ f ∈ M₁, a ∉ ends f)).card : ℝ) ≤ (A.filter (fun a => s ≤ w b a)).card := by
          exact_mod_cast card_filter_le _ _
        linarith
    have hsum := sum_le_sum hterm
    rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul] at hsum
    have hS : ∑ s ∈ Icc 1 smax, ((A.filter (fun a => s ≤ w b a)).card : ℝ) ≤ D := by
      have := hsumw b hb
      rw [e2] at this
      exact_mod_cast this
    rw [e1]
    push_cast
    have hc0 : (0 : ℝ) ≤ (D₀ : ℝ) ^ (-c) := by positivity
    calc _ ≤ _ := hsum
      _ ≤ (D₀ : ℝ) ^ (-c) * D + smax * (D₀ : ℝ) ^ (β / 2) := by gcongr
  have hload : ∀ v, v ∉ A₀ → (load ends A₀ O v : ℝ) ≤ ΔB := by
    intro v hv
    by_cases hvB : v ∈ B ∧ v ∉ A
    · exact hloadB v hvB.1 hvB.2
    · have h0 : load ends A₀ O v = 0 := by
        refine sum_eq_zero fun a ha => card_eq_zero.2 (filter_eq_empty_iff.2 fun e he hve => ?_)
        have haA := hA₀A ha
        obtain ⟨heG, hae⟩ := hOG₂ a haA e he
        by_cases hvA : v ∈ A
        · exact hv ((huniq e heG a haA v hvA hae hve) ▸ ha)
        · have : v ∈ A ∪ B := hV₂ ▸ hG₂V e heG hve
          rcases mem_union.1 this with h | h
          · exact hvA h
          · exact hvB ⟨h, hvA⟩
      rw [h0, Nat.cast_zero]; exact hΔB0
  -- step 4: closing
  obtain ⟨M₂, hM₂O, hM₂cov, hM₂m⟩ := closing_lll ends A₀ O r t ΔB p
    (fun a ha => (hO a (hA₀A ha)).2)
    (fun a ha a' ha' hne => by
      rw [disjoint_left]
      intro e he he'
      exact hne (huniq e (hOG₂ a (hA₀A ha) e he).1 a (hA₀A ha) a' (hA₀A ha')
        (hOG₂ a (hA₀A ha) e he).2 (hOG₂ a' (hA₀A ha') e he').2))
    (fun a ha e he a' ha' hae => huniq e (hOG₂ a (hA₀A ha) e he).1 a' (hA₀A ha') a (hA₀A ha)
        hae (hOG₂ a (hA₀A ha) e he).2)
    (fun a ha e he => (hcard e (mem_union_right _ (hOG₂ a (hA₀A ha) e he).1)).le)
    hload hΔB0 hp0 hp1 N7
  -- step 5: combine
  have hM₂own : ∀ e ∈ M₂, ∃ a ∈ A₀, e ∈ O a := fun e he => mem_biUnion.1 (hM₂O he)
  refine ⟨M₁ ∪ M₂, ?_, ?_, ?_⟩
  · intro e he
    rcases mem_union.1 he with he | he
    · exact mem_union_left _ (hM₁G he)
    · obtain ⟨a, ha, hea⟩ := hM₂own e he
      exact mem_union_right _ (hOG₂ a (hA₀A ha) e hea).1
  · -- cross disjointness
    have hcross : ∀ e ∈ M₁, ∀ f ∈ M₂, Disjoint (ends e) (ends f) := by
      intro e he f hf
      obtain ⟨a, ha, hfa⟩ := hM₂own f hf
      have haA := hA₀A ha
      obtain ⟨hfG, haf⟩ := hOG₂ a haA f hfa
      rw [disjoint_left]
      intro v hve hvf
      have hv1 : v ∈ V₁ := hV₁ e (hM₁G he) hve
      have hv2 : v ∈ V₂ := hG₂V f hfG hvf
      have hvA : v ∈ A := hV ▸ mem_inter.2 ⟨hv1, hv2⟩
      have := huniq f hfG v hvA a haA hvf haf
      subst this
      exact (mem_filter.1 ha).2 e he hve
    intro e he f hf hef
    rcases mem_union.1 he with he | he <;> rcases mem_union.1 hf with hf | hf
    · exact hM₁m e he f hf hef
    · exact hcross e he f hf
    · exact (hcross f hf e he).symm
    · exact hM₂m e he f hf hef
  · intro a ha
    by_cases hcov : ∀ f ∈ M₁, a ∉ ends f
    · have ha0 : a ∈ A₀ := mem_filter.2 ⟨ha, hcov⟩
      obtain ⟨e, heM, heO⟩ := hM₂cov a ha0
      exact ⟨e, mem_union_right _ heM, (hOG₂ a ha e heO).2⟩
    · push_neg at hcov
      obtain ⟨f, hf, haf⟩ := hcov
      exact ⟨f, mem_union_left _ hf, haf⟩

end RefinedAbsorption.Pending
