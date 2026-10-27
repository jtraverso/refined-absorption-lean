module
public import RefinedAbsorption.Pending.Regularize
public import RefinedAbsorption.Nibble.LocalMain
public import RefinedAbsorption.Faithful2024.Section2

/-!
# A local nibble for labelled multi-hypergraphs, near-regular only on `A`

`multiNibbleA`: let `G₁` be an `r`-uniform multi-hypergraph given by labelled copies
`ends : E → Finset V` (parallel copies allowed), with all degrees at most `D₀`, codegrees at most
`D₀^{1-δ}`, and degree at least `D₀(1 - D₀^{-δ})` at the vertices of a set `A` (no lower bound
elsewhere).  Then for every family `𝒯` of test sets inside `A` with local size bounds there is a
matching `M ⊆ G₁` leaving at most a `D₀^{-c}` proportion of every large test set uncovered.

Proof: every copy `f` becomes the simple `(r+1)`-set `ends f ∪ {f}` (this separates parallel
copies); the resulting simple hypergraph is made `D₀`-regular outside `A` by the layered
construction `liftE` of `Pending/Regularize.lean` (deficit `0` at `A`), and the local nibble
`RefinedAbsorption.Nibble.localNibble` is applied with the test sets placed in layer `(0,0)`.
The copies whose layer-`(0,0)` lift is in the matching form `M`; a vertex `a ∈ A` of layer
`(0,0)` is covered only by such lifts, since there are no fibre edges over `A`.
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset RefinedAbsorption.Nibble RefinedAbsorption.Faithful2024

section Hedge

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- The simple `(r+1)`-set attached to the copy `f`. -/
def hedge (ends : E → Finset V) (f : E) : Finset (V ⊕ E) :=
  insert (Sum.inr f) ((ends f).map Function.Embedding.inl)

theorem mem_hedge_inl {ends : E → Finset V} {f : E} {v : V} :
    Sum.inl v ∈ hedge ends f ↔ v ∈ ends f := by
  unfold hedge; simp

theorem mem_hedge_inr {ends : E → Finset V} {f g : E} :
    Sum.inr g ∈ hedge ends f ↔ g = f := by
  unfold hedge; simp

theorem card_hedge (ends : E → Finset V) (f : E) : (hedge ends f).card = (ends f).card + 1 := by
  unfold hedge
  rw [card_insert_of_notMem (by simp), card_map]

theorem hedge_injective (ends : E → Finset V) : Function.Injective (hedge ends) := by
  intro f g h
  have : Sum.inr f ∈ hedge ends g := h ▸ (mem_insert_self _ _)
  exact (mem_hedge_inr.1 this)

end Hedge

/-- **Local nibble for labelled multi-hypergraphs, near-regular only on `A`.** -/
theorem multiNibbleA (r : ℕ) (hr : 2 ≤ r) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ Δ₀ : ℝ, ∀ D₀ : ℕ, Δ₀ ≤ D₀ →
    ∀ (V E : Type) [DecidableEq V] [DecidableEq E] (ends : E → Finset V) (G₁ : Finset E)
      (A : Finset V) (𝒯 : Finset (Finset V)),
      (∀ f ∈ G₁, (ends f).card = r) →
      (∀ f ∈ G₁, ∀ v ∈ ends f, vdeg ends G₁ v ≤ D₀) →
      (∀ a ∈ A, (D₀ : ℝ) * (1 - (D₀ : ℝ) ^ (-δ)) ≤ vdeg ends G₁ a) →
      (∀ u v, u ≠ v → (codeg2 ends G₁ u v : ℝ) ≤ (D₀ : ℝ) ^ (1 - δ)) →
      (∀ T ∈ 𝒯, T ⊆ A) → (∀ T ∈ 𝒯, (T.card : ℝ) ≤ (D₀ : ℝ) ^ K) →
      (∀ v, ((𝒯.filter (fun T => v ∈ T)).card : ℝ) ≤ (D₀ : ℝ) ^ K) →
      ∃ M ⊆ G₁, IsMatchingL ends M ∧ ∀ T ∈ 𝒯, (D₀ : ℝ) ^ δ ≤ T.card →
        ((T.filter (fun a => ∀ f ∈ M, a ∉ ends f)).card : ℝ) ≤ (D₀ : ℝ) ^ (-c) * T.card := by
  obtain ⟨c, hc, Δ₀, hNib⟩ := localNibble (r + 1) (by omega) δ hδ hδ1 K
  refine ⟨c, hc, max Δ₀ 2, ?_⟩
  intro D₀ hD₀ V E _ _ ends G₁ A 𝒯 hcard hdegup hdegA hcod h𝒯A h𝒯size h𝒯mult
  have hD₀2 : (2 : ℝ) ≤ D₀ := le_trans (le_max_right _ _) hD₀
  have hD₀1 : 1 ≤ D₀ := by exact_mod_cast (show (1 : ℝ) ≤ D₀ by linarith)
  have hD₀pos : (0 : ℝ) < D₀ := by linarith
  set k := r + 1 with hk
  -- the prime modulus
  obtain ⟨M, hMge, hMprime⟩ := Nat.exists_infinite_primes (D₀ + k + 1)
  haveI : Fact M.Prime := ⟨hMprime⟩
  haveI : NeZero M := ⟨hMprime.ne_zero⟩
  have hkM : k < M := by omega
  -- the simple hypergraph `H'`
  set H' : Finset (Finset (V ⊕ E)) := G₁.image (hedge ends) with hH'
  set Bs : Finset (V ⊕ E) := G₁.biUnion (hedge ends) with hBs
  let d : V ⊕ E → ℕ := fun x => match x with
    | Sum.inl v => if v ∈ A then 0 else D₀ - vdeg ends G₁ v
    | Sum.inr _ => D₀ - 1
  have hdM : ∀ x, d x ≤ M := by
    intro x; cases x with
    | inl v => show (if v ∈ A then 0 else D₀ - vdeg ends G₁ v) ≤ M; split_ifs <;> omega
    | inr f => show D₀ - 1 ≤ M; omega
  have hH'card : ∀ F ∈ H', F.card = k := by
    intro F hF
    obtain ⟨f, hf, rfl⟩ := mem_image.1 hF
    rw [card_hedge, hcard f hf]
  have hH'Bs : ∀ F ∈ H', F ⊆ Bs := by
    intro F hF
    obtain ⟨f, hf, rfl⟩ := mem_image.1 hF
    exact subset_biUnion_of_mem _ hf
  -- degrees in `H'`
  have hstar_inl : ∀ v : V, (Nibble.star H' (Sum.inl v)).card = vdeg ends G₁ v := by
    intro v
    have : Nibble.star H' (Sum.inl v) = (G₁.filter (fun f => v ∈ ends f)).image (hedge ends) := by
      ext F
      simp only [Nibble.star, hH', mem_filter, mem_image]
      constructor
      · rintro ⟨⟨f, hf, rfl⟩, hv⟩; exact ⟨f, ⟨hf, mem_hedge_inl.1 hv⟩, rfl⟩
      · rintro ⟨f, ⟨hf, hv⟩, rfl⟩; exact ⟨⟨f, hf, rfl⟩, mem_hedge_inl.2 hv⟩
    rw [this, card_image_of_injective _ (hedge_injective ends)]
    rfl
  have hstar_inr : ∀ f ∈ G₁, (Nibble.star H' (Sum.inr f)).card = 1 := by
    intro f hf
    rw [card_eq_one]
    refine ⟨hedge ends f, ?_⟩
    ext F
    simp only [Nibble.star, hH', mem_filter, mem_image, mem_singleton]
    constructor
    · rintro ⟨⟨g, hg, rfl⟩, hv⟩; rw [mem_hedge_inr.1 hv]
    · rintro rfl; exact ⟨⟨f, hf, rfl⟩, mem_insert_self _ _⟩
  have hmemBs : ∀ x ∈ Bs, (∃ v, x = Sum.inl v ∧ ∃ f ∈ G₁, v ∈ ends f) ∨
      (∃ f, x = Sum.inr f ∧ f ∈ G₁) := by
    intro x hx
    obtain ⟨f, hf, hxf⟩ := mem_biUnion.1 hx
    cases x with
    | inl v => exact Or.inl ⟨v, rfl, f, hf, mem_hedge_inl.1 hxf⟩
    | inr g => exact Or.inr ⟨g, rfl, (mem_hedge_inr.1 hxf) ▸ hf⟩
  -- codegrees in `H'`
  have hDδ1 : (1 : ℝ) ≤ (D₀ : ℝ) ^ (1 - δ) := Real.one_le_rpow (by linarith) (by linarith)
  have hcodH' : ∀ x y : V ⊕ E, x ≠ y → (codeg H' x y : ℝ) ≤ (D₀ : ℝ) ^ (1 - δ) := by
    intro x y hxy
    have hsub : ∀ (P : Finset (V ⊕ E) → Prop) [DecidablePred P],
        (H'.filter P).card = (G₁.filter (fun f => P (hedge ends f))).card := by
      intro P _
      rw [hH', filter_image, card_image_of_injective _ (hedge_injective ends)]
    unfold codeg
    rw [hsub]
    cases x with
    | inl u =>
      cases y with
      | inl v =>
        have huv : u ≠ v := fun h => hxy (h ▸ rfl)
        refine le_trans ?_ (hcod u v huv)
        exact_mod_cast (card_le_card fun f hf => by
          simp only [mem_filter, mem_hedge_inl] at hf ⊢; exact hf)
      | inr g =>
        refine le_trans ?_ hDδ1
        exact_mod_cast card_le_one.2 fun f hf f' hf' => by
          simp only [mem_filter, mem_hedge_inr] at hf hf'
          exact hf.2.2.symm.trans hf'.2.2
    | inr g =>
      refine le_trans ?_ hDδ1
      exact_mod_cast card_le_one.2 fun f hf f' hf' => by
        simp only [mem_filter, mem_hedge_inr] at hf hf'
        exact hf.2.1.symm.trans hf'.2.1
  -- the regularised hypergraph
  set Es := liftE (k := k) (M := M) H' Bs d with hEs
  set Vs := Bs ×ˢ (univ : Finset (Fin k × ZMod M)) with hVs
  have hEscard : ∀ F ∈ Es, F.card = k := liftE_card hH'card
  have hEsV : ∀ F ∈ Es, F ⊆ Vs := liftE_subset hH'Bs
  have hk2 : 2 ≤ k := by omega
  have hEsdeg : ∀ v ∈ Vs, (D₀ : ℝ) * (1 - (D₀ : ℝ) ^ (-δ)) ≤ (Nibble.star Es v).card ∧
      ((Nibble.star Es v).card : ℝ) ≤ D₀ := by
    intro v hv
    have hvB : v.1 ∈ Bs := (mem_product.1 hv).1
    rw [hEs, liftE_star hk2 hH'card hdM hvB]
    have hlow : (D₀ : ℝ) * (1 - (D₀ : ℝ) ^ (-δ)) ≤ D₀ := by
      have : (0 : ℝ) ≤ (D₀ : ℝ) ^ (-δ) := by positivity
      nlinarith
    rcases hmemBs _ hvB with ⟨u, hu, f, hf, huf⟩ | ⟨f, hf, hfG⟩
    · rw [hu, hstar_inl]
      have hup := hdegup f hf u huf
      show _ ≤ ((vdeg ends G₁ u + (if u ∈ A then 0 else D₀ - vdeg ends G₁ u) : ℕ) : ℝ) ∧
        ((vdeg ends G₁ u + (if u ∈ A then 0 else D₀ - vdeg ends G₁ u) : ℕ) : ℝ) ≤ D₀
      by_cases huA : u ∈ A
      · rw [if_pos huA, add_zero]
        exact ⟨hdegA u huA, by exact_mod_cast hup⟩
      · rw [if_neg huA, Nat.add_sub_cancel' hup]
        exact ⟨hlow, le_rfl⟩
    · rw [hf, hstar_inr f hfG]
      show _ ≤ ((1 + (D₀ - 1) : ℕ) : ℝ) ∧ ((1 + (D₀ - 1) : ℕ) : ℝ) ≤ D₀
      rw [Nat.add_sub_cancel' hD₀1]
      exact ⟨hlow, le_rfl⟩
  have hEscod : ∀ u v, u ≠ v → (codeg Es u v : ℝ) ≤ (D₀ : ℝ) ^ (1 - δ) := by
    intro u v huv
    have h := liftE_codeg (H := H') (Bs := Bs) hkM hdM huv
    split_ifs at h with hb
    · exact le_trans (by exact_mod_cast h) hDδ1
    · exact le_trans (by exact_mod_cast h) (hcodH' _ _ hb)
  -- the test sets in layer `(0,0)`
  let emb0 : V ↪ (V ⊕ E) × Fin k × ZMod M :=
    ⟨fun a => (Sum.inl a, (0 : Fin k), (0 : ZMod M)), fun a b h => by
      simp only [Prod.mk.injEq, Sum.inl.injEq] at h; exact h.1⟩
  set 𝒯s := 𝒯.image (fun T => T.map emb0) with h𝒯s
  have h𝒯ssize : ∀ T ∈ 𝒯s, (T.card : ℝ) ≤ (D₀ : ℝ) ^ K := by
    intro T hT
    obtain ⟨T', hT', rfl⟩ := mem_image.1 hT
    rw [card_map]; exact h𝒯size T' hT'
  have h𝒯smult : ∀ w, ((𝒯s.filter (fun T => w ∈ T)).card : ℝ) ≤ (D₀ : ℝ) ^ K := by
    intro w
    have h1 : (𝒯s.filter (fun T => w ∈ T)).card ≤
        (𝒯.filter (fun T => w ∈ T.map emb0)).card := by
      rw [h𝒯s, filter_image]; exact card_image_le
    by_cases hw : ∃ v, emb0 v = w
    · obtain ⟨v, rfl⟩ := hw
      have h2 : 𝒯.filter (fun T => emb0 v ∈ T.map emb0) = 𝒯.filter (fun T => v ∈ T) := by
        ext T; simp only [mem_filter, mem_map_equiv, mem_map' emb0]
      rw [h2] at h1
      exact le_trans (by exact_mod_cast h1) (h𝒯mult v)
    · have h2 : 𝒯.filter (fun T => w ∈ T.map emb0) = ∅ := by
        rw [filter_eq_empty_iff]
        intro T _ hwT
        obtain ⟨v, -, hv⟩ := mem_map.1 hwT
        exact hw ⟨v, hv⟩
      rw [h2, card_empty] at h1
      have : (𝒯s.filter (fun T => w ∈ T)).card = 0 := by omega
      rw [this, Nat.cast_zero]; positivity
  obtain ⟨Ms, hMsE, hMsdisj, hMsT⟩ := hNib D₀ (le_trans (le_max_left _ _) hD₀) _ Es Vs 𝒯s
    hEscard hEsV hEsdeg hEscod h𝒯ssize h𝒯smult
  -- the matching of `G₁`
  set M₁ := G₁.filter (fun f => liftReal (hedge ends f) ((0 : Fin k), (0 : ZMod M)) ∈ Ms)
    with hM₁
  -- coverage of `A` in layer `(0,0)`
  have hcovA : ∀ a ∈ A, emb0 a ∈ cov Ms → ∃ f ∈ M₁, a ∈ ends f := by
    intro a ha hcov
    obtain ⟨e, he, hae⟩ := mem_biUnion.1 hcov
    have heE := hMsE he
    rw [hEs, liftE, mem_union] at heE
    rcases heE with heE | heE
    · obtain ⟨p, hp, rfl⟩ := mem_image.1 heE
      rw [id_eq, mem_liftReal] at hae
      obtain ⟨f, hf, hpf⟩ := mem_image.1 (mem_product.1 hp).1
      have hp2 : p.2 = ((0 : Fin k), (0 : ZMod M)) := hae.2.symm
      refine ⟨f, mem_filter.2 ⟨hf, ?_⟩, ?_⟩
      · rw [hpf, ← hp2]; exact he
      · rw [← mem_hedge_inl, hpf]; exact hae.1
    · obtain ⟨p, hp, rfl⟩ := mem_image.1 heE
      rw [id_eq, mem_liftFib] at hae
      rw [mem_filter] at hp
      have hdp := hp.2
      rw [← hae.1] at hdp
      change p.2.1 < (if a ∈ A then 0 else D₀ - vdeg ends G₁ a) at hdp
      rw [if_pos ha] at hdp
      exact absurd hdp (Nat.not_lt_zero _)
  have hcovA' : ∀ a, (∃ f ∈ M₁, a ∈ ends f) → emb0 a ∈ cov Ms := by
    rintro a ⟨f, hf, haf⟩
    exact mem_biUnion.2 ⟨_, (mem_filter.1 hf).2, (mem_liftReal (v := emb0 a)).2
      ⟨mem_hedge_inl.2 haf, rfl⟩⟩
  refine ⟨M₁, filter_subset _ _, ?_, ?_⟩
  · intro f hf g hg hfg
    rw [disjoint_left]
    intro v hvf hvg
    have h1 := (mem_filter.1 hf).2
    have h2 := (mem_filter.1 hg).2
    have hne : liftReal (hedge ends f) ((0 : Fin k), (0 : ZMod M)) ≠
        liftReal (hedge ends g) ((0 : Fin k), (0 : ZMod M)) :=
      fun h => hfg (hedge_injective ends (liftReal_injective _ h))
    have := hMsdisj _ h1 _ h2 hne
    exact disjoint_left.1 this ((mem_liftReal (v := emb0 v)).2 ⟨mem_hedge_inl.2 hvf, rfl⟩)
      ((mem_liftReal (v := emb0 v)).2 ⟨mem_hedge_inl.2 hvg, rfl⟩)
  · intro T hT hTbig
    have hTs : T.map emb0 ∈ 𝒯s := mem_image.2 ⟨T, hT, rfl⟩
    have hTV : T.map emb0 ∩ Vs = T.map emb0 := by
      refine inter_eq_left.2 fun w hw => ?_
      obtain ⟨a, ha, rfl⟩ := mem_map.1 hw
      have haA := h𝒯A T hT ha
      have hpos : (0 : ℝ) < vdeg ends G₁ a := by
        refine lt_of_lt_of_le ?_ (hdegA a haA)
        have : (D₀ : ℝ) ^ (-δ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith)
          (by linarith)
        nlinarith
      have hpos' : 0 < vdeg ends G₁ a := by exact_mod_cast hpos
      obtain ⟨f, hf⟩ := card_pos.1 hpos'
      rw [mem_filter] at hf
      exact mem_product.2 ⟨mem_biUnion.2 ⟨f, hf.1, mem_hedge_inl.2 hf.2⟩, mem_univ _⟩
    have h := hMsT _ hTs (by rw [hTV, card_map]; exact hTbig)
    rw [hTV, card_map] at h
    have heq : (T.map emb0 \ cov Ms).card = (T.filter (fun a => ∀ f ∈ M₁, a ∉ ends f)).card := by
      have : T.map emb0 \ cov Ms = (T.filter (fun a => ∀ f ∈ M₁, a ∉ ends f)).map emb0 := by
        ext w
        simp only [mem_sdiff, mem_map, mem_filter]
        constructor
        · rintro ⟨⟨a, ha, rfl⟩, hnc⟩
          refine ⟨a, ⟨ha, fun f hf haf => hnc (hcovA' a ⟨f, hf, haf⟩)⟩, rfl⟩
        · rintro ⟨a, ⟨ha, hnf⟩, rfl⟩
          refine ⟨⟨a, ha, rfl⟩, fun hc => ?_⟩
          obtain ⟨f, hf, haf⟩ := hcovA a (h𝒯A T hT ha) hc
          exact hnf f hf haf
      rw [this, card_map]
    rw [heq] at h
    exact h

end RefinedAbsorption.Pending
