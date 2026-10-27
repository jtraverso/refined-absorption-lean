module
public import RequestProject.Absorber17.Theorem

/-!
# Attaching absorbers to the pieces of a refiner family

Using Theorem 1.7 we attach to every member `W` of a family `𝒲` of `K_q^r`-divisible subgraphs
of `X ∪ R` a private `K_q^r`-absorber on fresh vertices.  The absorbers are pairwise
edge-disjoint and edge-disjoint from `X ∪ R`, i.e. they are attached absorbers in the sense of
`IsAttachedAbsorbers`.  (No degree bound is claimed: the new vertices are taken outside the
original vertex set.)
-/

@[expose] public section

namespace RefinedAbsorption.Absorber17

open Finset

/-- **Absorbers on fresh vertices.**  Every `K_q^r`-divisible `r`-graph `L` on `V` has a
`K_q^r`-absorber on `V ⊕ ℕ` every edge of which contains a new vertex. -/
theorem exists_absorber_fresh {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) {V : Type} [DecidableEq V]
    {L : Finset (Finset V)} (hL : IsRGraph r L) (hdiv : IsDivisible q r L) :
    ∃ A : Finset (Finset (V ⊕ ℕ)), IsAbsorber q r (gmap Function.Embedding.inl L) A ∧
      ∀ f ∈ A, ∃ n : ℕ, (Sum.inr n : V ⊕ ℕ) ∈ f := by
  classical
  set S := vertexSet L with hS
  set k := S.card with hk
  let ψ : Fin k ↪ V := ⟨fun i => (S.equivFin.symm i).1, fun i j h =>
    S.equivFin.symm.injective (Subtype.val_injective h)⟩
  have hψS : ∀ i, ψ i ∈ S := fun i => (S.equivFin.symm i).2
  have hrange : ∀ x ∈ S, ∃ i, ψ i = x := fun x hx =>
    ⟨S.equivFin ⟨x, hx⟩, by simp [ψ]⟩
  have hpre : ∀ e ∈ L, (e.preimage ψ ψ.injective.injOn).map ψ = e := by
    intro e he
    ext x
    simp only [mem_map, mem_preimage]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      obtain ⟨i, rfl⟩ := hrange x (subset_vertexSet he hx)
      exact ⟨i, hx, rfl⟩
  set LS : Finset (Finset (Fin k)) := L.image (fun e => e.preimage ψ ψ.injective.injOn) with hLSdef
  have hLS : gmap ψ LS = L := by
    ext e
    simp only [mem_gmap, hLSdef, mem_image]
    constructor
    · rintro ⟨e₀, ⟨e', he', rfl⟩, rfl⟩; rw [hpre e' he']; exact he'
    · intro he; exact ⟨_, ⟨e, he, rfl⟩, hpre e he⟩
  have hLSr : IsRGraph r LS := by
    intro e₀ he₀
    rw [← card_map ψ]
    exact hL _ (hLS ▸ map_mem_gmap.2 he₀)
  have hLSd : IsDivisible q r LS := by
    intro S₀ hS₀
    rw [← deg_gmap_map ψ, hLS]
    have := hdiv (S₀.map ψ) (by rwa [card_map])
    rwa [card_map] at this
  obtain ⟨N, hN, A', habs⟩ := absorberExistence q r hr hrq k LS hLSr hLSd
  let φ : Fin N ↪ V ⊕ ℕ := ⟨fun i => if h : i.1 < k then Sum.inl (ψ ⟨i.1, h⟩) else Sum.inr i.1,
    fun i j h => by
      by_cases hi : i.1 < k <;> by_cases hj : j.1 < k <;> simp only [hi, hj, dif_pos, dif_neg,
        not_false_eq_true, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
      · exact Fin.ext (Fin.mk.inj_iff.1 (ψ.injective h))
      · exact Fin.ext h⟩
  have hφ : (Fin.castLEEmb hN).trans φ = ψ.trans Function.Embedding.inl := by
    ext i
    simp [φ, i.2]
  refine ⟨gmap φ A', ?_, ?_⟩
  · have h := habs.gmap φ
    change IsAbsorber q r (gmap φ (gmap (Fin.castLEEmb hN) LS)) _ at h
    rw [gmap_gmap, hφ, ← gmap_gmap, hLS] at h
    exact h
  · intro f hf
    obtain ⟨f', hf', rfl⟩ := mem_gmap.1 hf
    by_contra hno
    push_neg at hno
    apply habs.independent f' hf'
    intro x hx
    have hxk : x.1 < k := by
      by_contra h
      apply hno x.1
      refine mem_map.2 ⟨x, hx, ?_⟩
      simp [φ, h]
    change x ∈ vertexSet (gmap (Fin.castLEEmb hN) LS)
    rw [vertexSet_gmap]
    refine mem_map.2 ⟨⟨x.1, hxk⟩, ?_, Fin.ext rfl⟩
    obtain ⟨e, he, hxe⟩ := mem_sup.1 (hψS ⟨x.1, hxk⟩)
    refine mem_sup.2 ⟨e.preimage ψ ψ.injective.injOn, mem_image.2 ⟨e, he, rfl⟩, ?_⟩
    simpa [mem_preimage] using hxe

/-- Tagging the fresh vertices of the absorber attached to `W` by `W`. -/
def tagE {V : Type} [DecidableEq V] (W : Finset (Finset V)) :
    V ⊕ ℕ ↪ V ⊕ (Finset (Finset V) × ℕ) :=
  ⟨Sum.elim Sum.inl (fun n => Sum.inr (W, n)), fun x y h => by
    cases x <;> cases y <;> simp_all⟩

/-- **Attached absorbers on fresh vertices.**  For every family `𝒲` of `K_q^r`-divisible
subgraphs of the `r`-graph `X ∪ R`, private absorbers (Theorem 1.7) on new vertices can be attached
to all members of `𝒲`: they are pairwise edge-disjoint and edge-disjoint from `X ∪ R`. -/
theorem exists_attachedAbsorbers_fresh {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) {V : Type}
    [DecidableEq V] {X R : Finset (Finset V)} {𝒲 : Finset (Finset (Finset V))}
    (hrg : IsRGraph r (X ∪ R)) (hsub : ∀ W ∈ 𝒲, W ⊆ X ∪ R)
    (hdiv : ∀ W ∈ 𝒲, IsDivisible q r W) :
    ∃ A Qon Qoff : Finset (Finset (V ⊕ (Finset (Finset V) × ℕ))) →
        Finset (Finset (V ⊕ (Finset (Finset V) × ℕ))),
      IsAttachedAbsorbers q r (gmap Function.Embedding.inl X) (gmap Function.Embedding.inl R)
        (𝒲.image (gmap Function.Embedding.inl)) A Qon Qoff := by
  classical
  have hW : ∀ W ∈ 𝒲, ∃ A : Finset (Finset (V ⊕ ℕ)),
      IsAbsorber q r (gmap Function.Embedding.inl W) A ∧ ∀ f ∈ A, ∃ n : ℕ, (Sum.inr n : V ⊕ ℕ) ∈ f :=
    fun W hW => exists_absorber_fresh hr hrq (fun e he => hrg e (hsub W hW he)) (hdiv W hW)
  choose! Aw hAw hfresh using hW
  let pre : Finset (Finset (V ⊕ (Finset (Finset V) × ℕ))) → Finset (Finset V) := fun W' =>
    if h : ∃ W ∈ 𝒲, gmap Function.Embedding.inl W = W' then Classical.choose h else ∅
  have hinj : ∀ W₁ W₂ : Finset (Finset V),
      gmap (Function.Embedding.inl : V ↪ V ⊕ (Finset (Finset V) × ℕ)) W₁ =
        gmap Function.Embedding.inl W₂ → W₁ = W₂ := fun W₁ W₂ h => map_injective _ h
  have hpre : ∀ W ∈ 𝒲, pre (gmap Function.Embedding.inl W) = W := by
    intro W hW
    have h : ∃ W₀ ∈ 𝒲, gmap (Function.Embedding.inl : V ↪ V ⊕ (Finset (Finset V) × ℕ)) W₀ =
        gmap Function.Embedding.inl W := ⟨W, hW, rfl⟩
    simp only [pre, dif_pos h]
    exact hinj _ _ (Classical.choose_spec h).2
  let A : Finset (Finset (V ⊕ (Finset (Finset V) × ℕ))) → Finset (Finset (V ⊕ (Finset (Finset V) × ℕ))) :=
    fun W' => gmap (tagE (pre W')) (Aw (pre W'))
  have htagL : ∀ W : Finset (Finset V), gmap (tagE W) (gmap Function.Embedding.inl W) =
      gmap Function.Embedding.inl W := by
    intro W
    rw [gmap_gmap]
    congr 1
  have hon : ∀ W ∈ 𝒲, HasDecomposition q r (A (gmap Function.Embedding.inl W) ∪
      gmap Function.Embedding.inl W) := by
    intro W hW
    obtain ⟨𝒬, h𝒬⟩ := (hAw W hW).decomp_union
    have := h𝒬.gmap (tagE W)
    rw [gmap_union, htagL] at this
    simp only [A, hpre W hW]
    exact ⟨_, this⟩
  have hoff : ∀ W ∈ 𝒲, HasDecomposition q r (A (gmap Function.Embedding.inl W)) := by
    intro W hW
    obtain ⟨𝒬, h𝒬⟩ := (hAw W hW).decomp
    simp only [A, hpre W hW]
    exact ⟨_, h𝒬.gmap (tagE W)⟩
  have hfr : ∀ W ∈ 𝒲, ∀ f ∈ A (gmap Function.Embedding.inl W),
      ∃ n : ℕ, (Sum.inr (W, n) : V ⊕ (Finset (Finset V) × ℕ)) ∈ f := by
    intro W hW f hf
    simp only [A, hpre W hW] at hf
    obtain ⟨f₀, hf₀, rfl⟩ := mem_gmap.1 hf
    obtain ⟨n, hn⟩ := hfresh W hW f₀ hf₀
    exact ⟨n, mem_map.2 ⟨Sum.inr n, hn, rfl⟩⟩
  have htag : ∀ W ∈ 𝒲, ∀ f ∈ A (gmap Function.Embedding.inl W), ∀ W₁ n,
      (Sum.inr (W₁, n) : V ⊕ (Finset (Finset V) × ℕ)) ∈ f → W₁ = W := by
    intro W hW f hf W₁ n hn
    simp only [A, hpre W hW] at hf
    obtain ⟨f₀, -, rfl⟩ := mem_gmap.1 hf
    obtain ⟨y, -, hy⟩ := mem_map.1 hn
    cases y with
    | inl y => simp [tagE] at hy
    | inr y =>
      simp only [tagE, Function.Embedding.coeFn_mk, Sum.elim_inr, Sum.inr.injEq,
        Prod.mk.injEq] at hy
      exact hy.1.symm
  refine ⟨A, fun W' => if h : HasDecomposition q r (A W' ∪ W') then Classical.choose h else ∅,
    fun W' => if h : HasDecomposition q r (A W') then Classical.choose h else ∅, ?_⟩
  refine ⟨fun W' hW' => ?_, fun W' hW' => ?_, fun W₁' hW₁' W₂' hW₂' hne => ?_,
    fun W' hW' => ?_, fun W' hW' => ?_⟩
  · obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    obtain ⟨𝒬, h𝒬⟩ := hoff W hW
    exact h𝒬.rgraph
  · obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    rw [disjoint_left]
    intro f hf hfXR
    obtain ⟨n, hn⟩ := hfr W hW f hf
    rw [← gmap_union] at hfXR
    obtain ⟨f₀, -, rfl⟩ := mem_gmap.1 hfXR
    obtain ⟨y, -, hy⟩ := mem_map.1 hn
    simp at hy
  · obtain ⟨W₁, hW₁, rfl⟩ := mem_image.1 hW₁'
    obtain ⟨W₂, hW₂, rfl⟩ := mem_image.1 hW₂'
    rw [disjoint_left]
    intro f hf₁ hf₂
    obtain ⟨n, hn⟩ := hfr W₁ hW₁ f hf₁
    exact hne (congrArg _ (htag W₂ hW₂ f hf₂ W₁ n hn))
  · obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    have h := hon W hW
    simp only [dif_pos h]
    exact Classical.choose_spec h
  · obtain ⟨W, hW, rfl⟩ := mem_image.1 hW'
    have h := hoff W hW
    simp only [dif_pos h]
    exact Classical.choose_spec h

end RefinedAbsorption.Absorber17
