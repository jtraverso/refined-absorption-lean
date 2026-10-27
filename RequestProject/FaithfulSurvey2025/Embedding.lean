module
public import RequestProject.GeneralEmbedding.Main

/-!
# Survey arXiv:2510.19978v1, Definition 3.7 and Lemma 3.8: the notions of embedding

L. Postle, *Refined Absorption: A New Proof of the Existence Conjecture and its Applications to
Extremal and Probabilistic Design Theory*, arXiv:2510.19978v1.  **All numbers in this namespace are
those of the survey.**

The existing formalization (`RefinedAbsorption.GeneralEmbeddingLemma`,
`RefinedAbsorption.generalEmbeddingLemma`, file `GeneralEmbedding/Defs.lean`) uses, for every
`H ∈ ℋ`, a separate map `φ H : Fin (m H) → Fin n` of the new vertices of `W_H`, requires it to be
injective and to avoid `V(H)` (*per-piece injectivity*), and adds in the conclusion that new edges
of different supergraphs have distinct images (*new-edge distinctness*).

The printed Definition 3.7 instead asks for **one** map `φ : V(⋃𝒲) ↪ V(G)` fixing `V(J)`, i.e. a
map injective on the whole vertex set of the union of the supergraphs (*global injectivity*).
Here the three notions are defined separately and compared:

* `IsGlobalEmbedding` — the literal Definition 3.7 (in the representation of the project: the
  vertex set of `⋃𝒲` is `(⋃_{H ∈ ℋ} V(H)) ⊔ {(H, i) : H ∈ ℋ, i < m_H}`, the old vertices are
  fixed);
* `IsPiecewiseHostEmbedding` — per-piece injectivity (plus avoidance of `E(J) ∖ E(H)`), the notion
  used by the project;
* `NewEdgesDistinct` — distinct images of the new edges of different supergraphs.

Results:

* `isGlobalEmbedding_iff`: global injectivity is exactly per-piece injectivity, plus pairwise
  disjoint images of new vertices of different supergraphs, plus new vertices avoiding every
  `V(H')`, `H' ∈ ℋ` (and edge preservation);
* `IsGlobalEmbedding.injective_piece`, `IsGlobalEmbedding.newEdgesDistinct`: global ⇒ per-piece
  and global ⇒ new-edge distinctness;
* the converse fails: on the instance used for `not_generalEmbeddingLemmaLiteral` no global
  embedding exists, while the per-piece variant (`generalEmbedding_piecewise`) is proved;
* `not_generalEmbeddingLemmaLiteral`: **the literal reading of Lemma 3.8 (with the global
  injectivity of Definition 3.7) is false**: for `C = 3`, `r = 2`, `γ = 1/2` and every `C'`, a
  perfect matching `J` on `n ≥ max(4, C')` vertices, `ℋ` = its single edges and `W_H` = a triangle
  on `H` satisfy all hypotheses, but `V(J) = V(K_n)` leaves no vertex for the new vertices;
* `generalEmbedding_piecewise`: the existing `generalEmbeddingLemma`, restated with the names
  of this file (per-piece embedding + new-edge distinctness): a proved **variant**.
-/

@[expose] public section

namespace RefinedAbsorption.FaithfulSurvey2025

open Finset RefinedAbsorption

variable {n : ℕ} {ι : Type*} [DecidableEq ι]

/-- The vertex map of a system embedding: old vertices fixed, the new vertex `i` of `W_H` sent to
`Ψ H i`. -/
def sysMap (m : Finset ι → ℕ) (Ψ : (H : Finset ι) → Fin (m H) → Fin n) :
    Fin n ⊕ (Σ H : Finset ι, Fin (m H)) → Fin n :=
  Sum.elim id fun p => Ψ p.1 p.2

/-- The vertex set `V(⋃𝒲)` of the union of the supergraphs: the old vertices `⋃_{H ∈ ℋ} V(H)`
(which contain every old vertex of every `W_H`, by `IsSupergraphSystem.roots`) and the new
vertices `(H, i)` of the supergraphs `W_H`, `H ∈ ℋ`. -/
def sysVerts (ends : ι → Finset (Fin n)) (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ) :
    Set (Fin n ⊕ (Σ H : Finset ι, Fin (m H))) :=
  {x | (∃ a, x = Sum.inl a ∧ ∃ H ∈ ℋ, a ∈ subVerts ends H) ∨ (∃ p, x = Sum.inr p ∧ p.1 ∈ ℋ)}

/-- **Definition 3.7 of the survey, literally**: an embedding of the supergraph system `𝒲` into `G`
is a map `φ : V(⋃𝒲) ↪ V(G)` (injective on all of `V(⋃𝒲)`) fixing `V(J)` and preserving edges. -/
def IsGlobalEmbedding (G : Finset (Finset (Fin n))) (ends : ι → Finset (Fin n))
    (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
    (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))
    (Ψ : (H : Finset ι) → Fin (m H) → Fin n) : Prop :=
  Set.InjOn (sysMap m Ψ) (sysVerts ends ℋ m) ∧ ∀ H ∈ ℋ, ∀ e ∈ W H, embedEdge (Ψ H) e ∈ G

/-- Per-piece embeddings into `G ∖ (E(J) ∖ E(H))` (the notion of the project, Definition 3.7 for
the single supergraph `W_H`). -/
def IsPiecewiseHostEmbedding (G : Finset (Finset (Fin n))) (ends : ι → Finset (Fin n))
    (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
    (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))
    (φ : (H : Finset ι) → Fin (m H) → Fin n) : Prop :=
  ∀ H ∈ ℋ, IsHostEmbedding G ends H (W H) (φ H)

/-- The new edges of different supergraphs have distinct images. -/
def NewEdgesDistinct (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
    (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))
    (φ : (H : Finset ι) → Fin (m H) → Fin n) : Prop :=
  ∀ H₁ ∈ ℋ, ∀ H₂ ∈ ℋ, H₁ ≠ H₂ → ∀ e₁ ∈ W H₁, ∀ e₂ ∈ W H₂,
    e₁.toRight.Nonempty → e₂.toRight.Nonempty → embedEdge (φ H₁) e₁ ≠ embedEdge (φ H₂) e₂

/-- **Global injectivity, unfolded.** -/
theorem isGlobalEmbedding_iff {G : Finset (Finset (Fin n))} {ends : ι → Finset (Fin n)}
    {ℋ : Finset (Finset ι)} {m : Finset ι → ℕ}
    {W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))}
    {Ψ : (H : Finset ι) → Fin (m H) → Fin n} :
    IsGlobalEmbedding G ends ℋ m W Ψ ↔
      (∀ H ∈ ℋ, Function.Injective (Ψ H)) ∧
      (∀ H₁ ∈ ℋ, ∀ H₂ ∈ ℋ, H₁ ≠ H₂ → ∀ i j, Ψ H₁ i ≠ Ψ H₂ j) ∧
      (∀ H ∈ ℋ, ∀ i, ∀ H' ∈ ℋ, Ψ H i ∉ subVerts ends H') ∧
      (∀ H ∈ ℋ, ∀ e ∈ W H, embedEdge (Ψ H) e ∈ G) := by
  constructor
  · rintro ⟨hinj, hG⟩
    refine ⟨?_, ?_, ?_, hG⟩
    · intro H hH i j hij
      have := hinj (Or.inr ⟨⟨H, i⟩, rfl, hH⟩) (Or.inr ⟨⟨H, j⟩, rfl, hH⟩) hij
      simpa using this
    · intro H₁ h₁ H₂ h₂ hne i j hij
      have := hinj (Or.inr ⟨⟨H₁, i⟩, rfl, h₁⟩) (Or.inr ⟨⟨H₂, j⟩, rfl, h₂⟩) hij
      simp only [Sum.inr.injEq, Sigma.mk.injEq] at this
      exact hne this.1
    · intro H hH i H' hH' hmem
      have := hinj (Or.inr ⟨⟨H, i⟩, rfl, hH⟩) (Or.inl ⟨Ψ H i, rfl, H', hH', hmem⟩) rfl
      exact Sum.inr_ne_inl this
  · rintro ⟨h1, h2, h3, hG⟩
    refine ⟨?_, hG⟩
    rintro x (⟨a, rfl, Ha, hHa, ha⟩ | ⟨⟨H, i⟩, rfl, hH⟩) y
      (⟨b, rfl, Hb, hHb, hb⟩ | ⟨⟨H', j⟩, rfl, hH'⟩) hxy
    · exact congrArg Sum.inl hxy
    · simp only [sysMap, Sum.elim_inl, Sum.elim_inr, id] at hxy
      exact absurd (hxy ▸ ha) (h3 H' hH' j Ha hHa)
    · simp only [sysMap, Sum.elim_inl, Sum.elim_inr, id] at hxy
      exact absurd (hxy.symm ▸ hb) (h3 H hH i Hb hHb)
    · simp only [sysMap, Sum.elim_inr] at hxy
      by_cases hHH : H = H'
      · subst hHH
        rw [h1 H hH hxy]
      · exact absurd hxy (h2 H hH H' hH' hHH i j)

/-- Global ⇒ per-piece injectivity (each `Ψ H` is injective and avoids `V(H)`). -/
theorem IsGlobalEmbedding.injective_piece {G : Finset (Finset (Fin n))}
    {ends : ι → Finset (Fin n)} {ℋ : Finset (Finset ι)} {m : Finset ι → ℕ}
    {W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))}
    {Ψ : (H : Finset ι) → Fin (m H) → Fin n} (h : IsGlobalEmbedding G ends ℋ m W Ψ) :
    ∀ H ∈ ℋ, Function.Injective (Ψ H) ∧ ∀ i, Ψ H i ∉ subVerts ends H := by
  obtain ⟨h1, -, h3, -⟩ := isGlobalEmbedding_iff.1 h
  exact fun H hH => ⟨h1 H hH, fun i => h3 H hH i H hH⟩

/-- Global ⇒ new-edge distinctness (for a supergraph system). -/
theorem IsGlobalEmbedding.newEdgesDistinct {r : ℕ} {G : Finset (Finset (Fin n))}
    {ends : ι → Finset (Fin n)} {ℋ : Finset (Finset ι)} {m : Finset ι → ℕ}
    {W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))}
    {Ψ : (H : Finset ι) → Fin (m H) → Fin n} (h : IsGlobalEmbedding G ends ℋ m W Ψ)
    (hW : IsSupergraphSystem r ends ℋ m W) : NewEdgesDistinct ℋ m W Ψ := by
  obtain ⟨-, h2, h3, -⟩ := isGlobalEmbedding_iff.1 h
  intro H₁ h₁ H₂ h₂ hne e₁ he₁ e₂ he₂ hr₁ _ heq
  obtain ⟨i, hi⟩ := hr₁
  have hmem : Ψ H₁ i ∈ embedEdge (Ψ H₂) e₂ := by
    rw [← heq]
    exact mem_image.2 ⟨Sum.inr i, mem_toRight.1 hi, rfl⟩
  obtain ⟨x, hx, hxi⟩ := mem_image.1 hmem
  rcases x with a | j
  · have ha : a ∈ subVerts ends H₂ := hW.roots H₂ h₂ e₂ he₂ (mem_toLeft.2 hx)
    simp only [Sum.elim_inl, id] at hxi
    exact h3 H₁ h₁ i H₂ h₂ (hxi ▸ ha)
  · exact h2 H₁ h₁ H₂ h₂ hne i j hxi.symm

section Literal

open Classical in
/-- `Δ_{r-1}(J)` of the multi-`r`-graph `J` (all copies of the finite label type, counted with
multiplicity). -/
noncomputable def jMaxDeg (r : ℕ) {ι : Type*} [Fintype ι] (ends : ι → Finset (Fin n)) : ℕ :=
  ((univ : Finset (Finset (Fin n))).filter fun S => S.card + 1 = r).sup fun S =>
    (univ.filter fun x => S ⊆ ends x).card

open Classical in
/-- **Lemma 3.8 of the survey, read literally** (with Definition 3.7 as printed: one map
`φ : V(⋃𝒲) ↪ V(G)` fixing `V(J)`): `∀ C > r ≥ 1, γ ∈ (0,1] ∃ C' ≥ 1`: for `G ⊆ K_n^r`, a
multi-`r`-graph `J` with `Simple(J) ⊆ G` and `Δ(J) ≤ n/C'`, a `C`-refined family `ℋ` of subgraphs of
`J` and a `C`-bounded edge-intersecting supergraph system `𝒲` for `ℋ` such that every `W_H` has at
least `γ n^{|V(W_H) ∖ V(H)|}` embeddings into `G ∖ (E(J) ∖ E(H))`, there is an embedding `φ` of `𝒲`
into `G` with `Δ_{r-1}(φ(𝒲)) ≤ C' Δ_{r-1}(J)`.  **This statement is false**
(`not_generalEmbeddingLemmaLiteral`). -/
def GeneralEmbeddingLemmaLiteral : Prop :=
  ∀ (C r : ℕ), 1 ≤ r → r < C → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∃ C' : ℝ, 1 ≤ C' ∧
    ∀ (n : ℕ) (G : Finset (Finset (Fin n))) (ι : Type) [Fintype ι] [DecidableEq ι]
      (ends : ι → Finset (Fin n)) (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
      (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))),
      1 ≤ n → IsRGraph r G → (∀ x, (ends x).card = r) → (∀ x, ends x ∈ G) →
      (jMaxDeg r ends : ℝ) ≤ n / C' →
      IsCRefinedFamily C ℋ → IsSupergraphSystem r ends ℋ m W → IsEdgeIntersecting ends ℋ m W →
      IsCBounded C ends ℋ m W →
      (∀ H ∈ ℋ, γ * (n : ℝ) ^ (m H) ≤
        ((univ.filter (fun f : Fin (m H) → Fin n => IsHostEmbedding G ends H (W H) f)).card : ℝ)) →
      ∃ Ψ : (H : Finset ι) → Fin (m H) → Fin n,
        IsGlobalEmbedding G ends ℋ m W Ψ ∧
        ∀ S : Finset (Fin n), S.card + 1 = r →
          (((systemImage ℋ m W Ψ).filter (fun f => S ⊆ f)).card : ℝ) ≤ C' * jMaxDeg r ends

/-- The perfect matching on `Fin (2k)`: the `i`-th edge is `{2i, 2i+1}`. -/
def pmEnds (k : ℕ) (i : Fin k) : Finset (Fin (2 * k)) := univ.filter fun v => v.val / 2 = i.val

theorem mem_pmEnds {k : ℕ} {i : Fin k} {v : Fin (2 * k)} : v ∈ pmEnds k i ↔ v.val / 2 = i.val := by
  simp [pmEnds]

theorem card_pmEnds (k : ℕ) (i : Fin k) : (pmEnds k i).card = 2 := by
  have : pmEnds k i = {⟨2 * i.val, by omega⟩, ⟨2 * i.val + 1, by omega⟩} := by
    ext v
    simp only [mem_pmEnds, mem_insert, mem_singleton, Fin.ext_iff]
    omega
  rw [this, card_pair]
  simp [Fin.ext_iff]

/-- The triangle supergraphs over the edges of the matching. -/
def pmW (k : ℕ) (H : Finset (Fin k)) : Finset (Finset (Fin (2 * k) ⊕ Fin 1)) :=
  H.image (fun i => (pmEnds k i).map Function.Embedding.inl) ∪
    (subVerts (pmEnds k) H).image fun a => {Sum.inl a, Sum.inr 0}

theorem subVerts_pm_singleton {k : ℕ} (i : Fin k) : subVerts (pmEnds k) {i} = pmEnds k i := by
  simp [subVerts]

theorem embedEdge_map_inl {m : ℕ} (f : Fin m → Fin n) (s : Finset (Fin n)) :
    embedEdge f (s.map Function.Embedding.inl) = s := by
  ext a; simp [embedEdge]

theorem embedEdge_pair {m : ℕ} (f : Fin m → Fin n) (a : Fin n) (j : Fin m) :
    embedEdge f {Sum.inl a, Sum.inr j} = {a, f j} := by
  simp [embedEdge, image_insert]

/-- **The literal reading of Lemma 3.8 of the survey is false.**  Take `C = 3`, `r = 2`,
`γ = 1/2`.  For any `C'`, let `k = ⌈C'⌉ + 2`, `n = 2k`, `G = K_n^2`, `J` the perfect matching,
`ℋ` the single edges of `J` and `W_H` the triangle on `H` with one new vertex.  All hypotheses
hold (`Δ(J) = 1 ≤ n/C'`, each `W_H` has `n - 2 ≥ n/2` embeddings into `G ∖ (E(J) ∖ E(H))`), but an
injective map on `V(⋃𝒲) ⊇ V(J) = Fin n` fixing `V(J)` has no room for any new vertex. -/
theorem not_generalEmbeddingLemmaLiteral : ¬ GeneralEmbeddingLemmaLiteral := by
  intro hL
  obtain ⟨C', hC'1, hC'⟩ := hL 3 2 (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
  classical
  set k := ⌈C'⌉₊ + 2 with hk
  have hk2 : 2 ≤ k := by omega
  have hCk : C' ≤ 2 * k := by
    have := Nat.le_ceil C'
    have h2 : ((⌈C'⌉₊ : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : ⌈C'⌉₊ ≤ 2 * k)
    push_cast at h2
    linarith
  set ℋ : Finset (Finset (Fin k)) := univ.image fun i => ({i} : Finset (Fin k)) with hℋ
  have hℋmem : ∀ H ∈ ℋ, ∃ i, H = {i} := by
    intro H hH
    obtain ⟨i, -, rfl⟩ := mem_image.1 hH
    exact ⟨i, rfl⟩
  have hG2 : ∀ x, pmEnds k x ∈ powersetCard 2 (univ : Finset (Fin (2 * k))) :=
    fun x => mem_powersetCard.2 ⟨subset_univ _, card_pmEnds k x⟩
  refine (fun hex => ?_) (hC' (2 * k) (powersetCard 2 univ) (Fin k) (pmEnds k) ℋ (fun _ => 1)
    (pmW k) (by omega) (fun e he => (mem_powersetCard.1 he).2) (card_pmEnds k) hG2 ?_ ?_ ?_ ?_ ?_ ?_)
  · -- no global embedding
    obtain ⟨Ψ, hΨ, -⟩ := hex
    obtain ⟨-, -, h3, -⟩ := isGlobalEmbedding_iff.1 hΨ
    set v := Ψ {⟨0, by omega⟩} 0 with hv
    refine h3 {⟨0, by omega⟩} (mem_image.2 ⟨_, mem_univ _, rfl⟩) 0 {⟨v.val / 2, by omega⟩}
      (mem_image.2 ⟨_, mem_univ _, rfl⟩) ?_
    rw [subVerts_pm_singleton, mem_pmEnds]
  · -- `Δ(J) = 1 ≤ n / C'`
    have h1 : jMaxDeg 2 (pmEnds k) ≤ 1 := by
      refine Finset.sup_le fun S hS => card_le_one.2 fun x hx y hy => ?_
      have hS1 : S.card = 1 := by have := (mem_filter.1 hS).2; omega
      obtain ⟨v, rfl⟩ := card_eq_one.1 hS1
      have hx' := mem_pmEnds.1 ((mem_filter.1 hx).2 (mem_singleton_self v))
      have hy' := mem_pmEnds.1 ((mem_filter.1 hy).2 (mem_singleton_self v))
      exact Fin.ext (by omega)
    have h1' : (jMaxDeg 2 (pmEnds k) : ℝ) ≤ 1 := by exact_mod_cast h1
    have hpos : (0 : ℝ) < C' := by linarith
    refine h1'.trans ?_
    rw [le_div_iff₀ hpos, one_mul]
    exact_mod_cast hCk
  · -- `C`-refined
    intro x
    refine le_trans (card_le_one.2 fun H hH H' hH' => ?_) (by norm_num)
    obtain ⟨hH, hxH⟩ := mem_filter.1 hH
    obtain ⟨hH', hxH'⟩ := mem_filter.1 hH'
    obtain ⟨i, rfl⟩ := hℋmem _ hH
    obtain ⟨i', rfl⟩ := hℋmem _ hH'
    rw [mem_singleton] at hxH hxH'
    rw [← hxH, ← hxH']
  · -- supergraph system
    refine ⟨fun H _ e he => ?_, fun H _ x hx => ?_, fun H _ e he => ?_⟩
    · rcases mem_union.1 he with he | he
      · obtain ⟨i, -, rfl⟩ := mem_image.1 he
        rw [card_map, card_pmEnds]
      · obtain ⟨a, -, rfl⟩ := mem_image.1 he
        rw [card_pair (by simp)]
    · exact mem_union_left _ (mem_image_of_mem _ hx)
    · rcases mem_union.1 he with he | he
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 he
        intro a ha
        rw [mem_toLeft, mem_map] at ha
        obtain ⟨b, hb, hba⟩ := ha
        rw [Function.Embedding.inl_apply, Sum.inl.injEq] at hba
        exact mem_biUnion.2 ⟨i, hi, hba ▸ hb⟩
      · obtain ⟨a, ha, rfl⟩ := mem_image.1 he
        intro b hb
        rw [mem_toLeft] at hb
        simp only [mem_insert, Sum.inl.injEq, mem_singleton, reduceCtorEq, or_false] at hb
        exact hb ▸ ha
  · -- edge-intersecting
    intro H _ e he
    rcases mem_union.1 he with he | he
    · obtain ⟨i, hi, rfl⟩ := mem_image.1 he
      refine ⟨i, hi, fun a ha => ?_⟩
      rw [mem_toLeft, mem_map] at ha
      obtain ⟨b, hb, hba⟩ := ha
      rw [Function.Embedding.inl_apply, Sum.inl.injEq] at hba
      exact hba ▸ hb
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 he
      obtain ⟨i, hi, hai⟩ := mem_biUnion.1 ha
      refine ⟨i, hi, fun b hb => ?_⟩
      rw [mem_toLeft] at hb
      simp only [mem_insert, Sum.inl.injEq, mem_singleton, reduceCtorEq, or_false] at hb
      exact hb ▸ hai
  · -- `C`-bounded
    intro H hH
    obtain ⟨i, rfl⟩ := hℋmem H hH
    refine ⟨(card_union_le _ _).trans ?_, ?_⟩
    · refine (Nat.add_le_add card_image_le card_image_le).trans ?_
      rw [card_singleton, subVerts_pm_singleton, card_pmEnds]
    · rw [subVerts_pm_singleton, card_pmEnds]
      norm_num
  · -- many embeddings of every `W_H`
    intro H hH
    obtain ⟨i, rfl⟩ := hℋmem H hH
    set Good := (univ.filter fun v : Fin (2 * k) => v ∉ pmEnds k i).image
      fun v => fun _ : Fin 1 => v with hGood
    have hGoodc : Good.card = 2 * k - 2 := by
      rw [hGood, card_image_of_injective _ (fun v w h => congrFun h 0), filter_not,
        card_sdiff_of_subset (filter_subset _ _), card_univ, Fintype.card_fin]
      congr 1
      rw [show (univ.filter fun v : Fin (2 * k) => v ∈ pmEnds k i) = pmEnds k i by
        ext; simp, card_pmEnds]
    have hsub : Good ⊆ univ.filter fun f : Fin 1 → Fin (2 * k) =>
        IsHostEmbedding (powersetCard 2 univ) (pmEnds k) {i} (pmW k {i}) f := by
      intro f hf
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hf
      have hvi : v ∉ pmEnds k i := (mem_filter.1 hv).2
      refine mem_filter.2 ⟨mem_univ _, fun a b _ => Subsingleton.elim a b, ?_, ?_⟩
      · intro j; rw [subVerts_pm_singleton]; exact hvi
      · intro e he
        rcases mem_union.1 he with he | he
        · obtain ⟨i', hi', rfl⟩ := mem_image.1 he
          rw [mem_singleton] at hi'
          subst hi'
          refine ⟨by rw [embedEdge_map_inl]; exact hG2 _, fun hne => ?_⟩
          obtain ⟨j, hj⟩ := hne
          rw [mem_toRight, mem_map] at hj
          obtain ⟨b, -, hb⟩ := hj
          exact absurd hb Sum.inl_ne_inr
        · obtain ⟨a, ha, rfl⟩ := mem_image.1 he
          rw [subVerts_pm_singleton] at ha
          have hav : a ≠ v := fun h => hvi (h ▸ ha)
          rw [embedEdge_pair]
          refine ⟨mem_powersetCard.2 ⟨subset_univ _, card_pair hav⟩, fun _ y hy => ?_⟩
          have h1 : a ∈ pmEnds k y := hy ▸ mem_insert_self _ _
          have h2 : v ∈ pmEnds k y := hy ▸ mem_insert_of_mem (mem_singleton_self _)
          rw [mem_pmEnds] at h1 h2 ha
          exact hvi (mem_pmEnds.2 (by omega))
    have := card_le_card hsub
    rw [hGoodc] at this
    have h' : ((2 * k - 2 : ℕ) : ℝ) ≤ ((univ.filter fun f : Fin 1 → Fin (2 * k) =>
        IsHostEmbedding (powersetCard 2 univ) (pmEnds k) {i} (pmW k {i}) f).card : ℝ) := by
      exact_mod_cast this
    refine le_trans ?_ h'
    rw [Nat.cast_sub (by omega)]
    have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    push_cast
    nlinarith

open Classical in
/-- **Lemma 3.8 of the survey, per-piece variant** (the notion of the project, restated with the
names of this file): the conclusion asks for per-piece embeddings (each `φ H` injective, avoiding
`V(H)` and `E(J) ∖ E(H)`) with distinct images of the new edges of different supergraphs, instead
of the global injectivity of the printed Definition 3.7. -/
def GeneralEmbeddingLemmaPiecewise : Prop :=
  ∀ (C r : ℕ), 1 ≤ r → r < C → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∃ C' : ℝ, 1 ≤ C' ∧
    ∀ (n : ℕ) (G : Finset (Finset (Fin n))) (ι : Type) [Fintype ι] [DecidableEq ι]
      (ends : ι → Finset (Fin n)) (ℋ : Finset (Finset ι)) (m : Finset ι → ℕ)
      (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))) (D : ℝ),
      1 ≤ n → IsRGraph r G → (∀ x, (ends x).card = r) → (∀ x, ends x ∈ G) →
      (∀ S : Finset (Fin n), S.card + 1 = r →
        ((univ.filter (fun x => S ⊆ ends x)).card : ℝ) ≤ D) →
      D ≤ n / C' →
      IsCRefinedFamily C ℋ → IsSupergraphSystem r ends ℋ m W → IsEdgeIntersecting ends ℋ m W →
      IsCBounded C ends ℋ m W →
      (∀ H ∈ ℋ, γ * (n : ℝ) ^ (m H) ≤
        ((univ.filter (fun f : Fin (m H) → Fin n => IsHostEmbedding G ends H (W H) f)).card : ℝ)) →
      ∃ φ : (H : Finset ι) → Fin (m H) → Fin n,
        IsPiecewiseHostEmbedding G ends ℋ m W φ ∧ NewEdgesDistinct ℋ m W φ ∧
        ∀ S : Finset (Fin n), S.card + 1 = r →
          (((systemImage ℋ m W φ).filter (fun f => S ⊆ f)).card : ℝ) ≤ C' * D

/-- The per-piece variant of Lemma 3.8 is the existing `GeneralEmbeddingLemma` (same statement,
renamed notions). -/
theorem generalEmbeddingLemmaPiecewise_iff : GeneralEmbeddingLemmaPiecewise ↔ GeneralEmbeddingLemma :=
  Iff.rfl

/-- **Lemma 3.8 of the survey, per-piece variant: proved** (adapter from the existing
`RefinedAbsorption.generalEmbeddingLemma`). -/
theorem generalEmbedding_piecewise : GeneralEmbeddingLemmaPiecewise :=
  generalEmbeddingLemmaPiecewise_iff.2 generalEmbeddingLemma

end Literal

end RefinedAbsorption.FaithfulSurvey2025
