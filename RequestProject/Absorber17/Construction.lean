module
public import RequestProject.Absorber17.AntiClique
public import RequestProject.Absorber17.Transfer

/-!
# From a multi-absorber to an absorber (Section 3.1)

Let `L` be an `r`-graph with a `K_q^r`-multi-absorber, given here by two indexed families of
`q`-cliques `P i` (decomposing `A + L`) and `M j` (decomposing `A`).  Every copy of an edge `e`
of `A + L` is replaced by an *anti-edge* on `e` together with `q - r` private new vertices; the
copies of `e` are numbered `0, …, A e + [e ∈ L] - 1`.  The anti-edges of the copies inside a
clique `P i` (or `M j`) form an anti-clique, to which a copy of an anti-clique absorber is
attached.  The union of all anti-edges and all the attached absorbers is a `K_q^r`-absorber
for `L`.
-/

@[expose] public section

namespace RefinedAbsorption.Absorber17

open Finset

/-! ### Ranks in a finite set -/

section rank

variable {α : Type*} [DecidableEq α]

/-- The position of `x` in some fixed enumeration of `s` (and `0` outside `s`). -/
noncomputable def rk (s : Finset α) (x : α) : ℕ :=
  if h : x ∈ s then (s.equivFin ⟨x, h⟩ : ℕ) else 0

theorem rk_lt {s : Finset α} {x : α} (hx : x ∈ s) : rk s x < s.card := by
  rw [rk, dif_pos hx]; exact (s.equivFin ⟨x, hx⟩).2

theorem rk_inj {s : Finset α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) (h : rk s x = rk s y) :
    x = y := by
  rw [rk, dif_pos hx, rk, dif_pos hy] at h
  have := s.equivFin.injective (Fin.ext h)
  exact congrArg Subtype.val this

theorem rk_surj {s : Finset α} {n : ℕ} (hn : n < s.card) : ∃ x ∈ s, rk s x = n := by
  refine ⟨(s.equivFin.symm ⟨n, hn⟩).1, (s.equivFin.symm ⟨n, hn⟩).2, ?_⟩
  rw [rk, dif_pos (s.equivFin.symm ⟨n, hn⟩).2]
  simp

end rank

/-- A multi-absorber for `L`, presented by indexed families of `q`-cliques. -/
structure MultiData (q r : ℕ) (V : Type) [DecidableEq V] (L : Finset (Finset V)) where
  k₁ : ℕ
  k₂ : ℕ
  A : Finset V → ℕ
  P : Fin k₁ → (Fin q ↪ V)
  M : Fin k₂ → (Fin q ↪ V)
  cntP : ∀ e : Finset V, e.card = r →
    (univ.filter (fun i => e ⊆ univ.map (P i))).card = A e + if e ∈ L then 1 else 0
  cntM : ∀ e : Finset V, e.card = r → (univ.filter (fun j => e ⊆ univ.map (M j))).card = A e

theorem gmap_biUnion {U W ι : Type*} [DecidableEq U] [DecidableEq W] [DecidableEq ι]
    (f : U ↪ W) (s : Finset ι) (G : ι → Finset (Finset U)) :
    gmap f (s.biUnion G) = s.biUnion (fun i => gmap f (G i)) := by
  ext e
  simp only [mem_gmap, mem_biUnion]
  constructor
  · rintro ⟨e₀, ⟨i, hi, he₀⟩, rfl⟩; exact ⟨i, hi, e₀, he₀, rfl⟩
  · rintro ⟨i, hi, e₀, he₀, rfl⟩; exact ⟨e₀, ⟨i, hi, he₀⟩, rfl⟩

theorem gmap_singleton {U W : Type*} [DecidableEq U] [DecidableEq W] (f : U ↪ W) (e : Finset U) :
    gmap f {e} = {e.map f} := by
  simp [gmap]

theorem exists_Iset_map {q r : ℕ} {V : Type} [DecidableEq V] {f : Fin q ↪ V} {e : Finset V}
    (he : e ⊆ univ.map f) (hc : e.card = r) : ∃ I ∈ Iset q r, I.map f = e := by
  classical
  refine ⟨e.preimage f f.injective.injOn, ?_, ?_⟩
  · have hmap : (e.preimage f f.injective.injOn).map f = e := by
      ext z
      simp only [mem_map, mem_preimage]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hz
        obtain ⟨i, -, rfl⟩ := mem_map.1 (he hz)
        exact ⟨i, hz, rfl⟩
    rw [mem_Iset, ← card_map f, hmap, hc]
  · ext z
    simp only [mem_map, mem_preimage]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hz
      obtain ⟨i, -, rfl⟩ := mem_map.1 (he hz)
      exact ⟨i, hz, rfl⟩

theorem HasDecomposition.biUnion' {W ι : Type*} [DecidableEq W] [DecidableEq ι] {q r : ℕ}
    (hrq : r ≤ q) (s : Finset ι) (G : ι → Finset (Finset W))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (G i) (G j))
    (h : ∀ i ∈ s, HasDecomposition q r (G i)) : HasDecomposition q r (s.biUnion G) := by
  classical
  choose! 𝒬 h𝒬 using h
  exact ⟨_, IsDecomposition.biUnion hrq s G 𝒬 (fun i hi j hj hij => hdisj i hi j hj hij) h𝒬⟩

theorem HasDecomposition.union' {W : Type*} [DecidableEq W] {q r : ℕ} (hrq : r ≤ q)
    {G H : Finset (Finset W)} (hGH : Disjoint G H) (hG : HasDecomposition q r G)
    (hH : HasDecomposition q r H) : HasDecomposition q r (G ∪ H) := by
  obtain ⟨𝒬, h𝒬⟩ := hG
  obtain ⟨𝒲, h𝒲⟩ := hH
  exact ⟨_, IsDecomposition.union hrq hGH h𝒬 h𝒲⟩

theorem disjoint_of_vertex {W : Type*} [DecidableEq W] {G H : Finset (Finset W)} (p : W → Prop)
    (hG : ∀ f ∈ G, ∃ z ∈ f, p z) (hH : ∀ f ∈ H, ∀ z ∈ f, ¬ p z) : Disjoint G H := by
  rw [disjoint_left]
  intro f hfG hfH
  obtain ⟨z, hz, hp⟩ := hG f hfG
  exact hH f hfH z hz hp

section construction

variable {q r : ℕ} {V : Type} [DecidableEq V] {L : Finset (Finset V)}
  (D : MultiData q r V L) (Z : ACAbsorber q r)

instance (Z : ACAbsorber q r) : DecidableEq Z.T := Z.deq

/-- Vertex type: original vertices, private anti-edge vertices, and the internal vertices of
the attached anti-clique absorbers. -/
abbrev VT : Type :=
  V ⊕ (Finset V × Fin (D.k₁ + 1) × Fin (q - r)) ⊕ ((Fin D.k₁ ⊕ Fin D.k₂) × Z.T)

instance : DecidableEq (VT D Z) := by unfold VT; infer_instance

/-- The vertex enumeration of the clique with index `t`. -/
def emb (t : Fin D.k₁ ⊕ Fin D.k₂) : Fin q ↪ V := Sum.elim D.P D.M t

/-- Indices of the `P`-cliques containing `e`. -/
def PS (e : Finset V) : Finset (Fin D.k₁) := univ.filter (fun i => e ⊆ univ.map (D.P i))

/-- Indices of the `M`-cliques containing `e`. -/
def MS (e : Finset V) : Finset (Fin D.k₂) := univ.filter (fun j => e ⊆ univ.map (D.M j))

/-- Copy number of the edge `I` (in local coordinates) of the clique with index `t`. -/
noncomputable def lab : (Fin D.k₁ ⊕ Fin D.k₂) → Finset (Fin q) → ℕ
  | Sum.inl i, I => rk (PS D (I.map (D.P i))) i
  | Sum.inr j, I => rk (MS D (I.map (D.M j))) j

/-- Copy numbers stored in `Fin (k₁ + 1)` (all copy numbers are at most `k₁`). -/
def cfin (n : ℕ) : Fin (D.k₁ + 1) := ⟨min n D.k₁, by omega⟩

/-- The private vertices of the anti-edge of copy `n` of the edge `e`. -/
def yv (e : Finset V) (n : ℕ) (s : Fin (q - r)) : VT D Z := Sum.inr (Sum.inl (e, cfin D n, s))

def Ys (e : Finset V) (n : ℕ) : Finset (VT D Z) := univ.image (yv D Z e n)

/-- The copy of `e` among the original vertices. -/
def eV (e : Finset V) : Finset (VT D Z) := e.map Function.Embedding.inl

/-- The anti-edge of copy `n` of `e`. -/
def anti (e : Finset V) (n : ℕ) : Finset (Finset (VT D Z)) :=
  cliqueEdges r (eV D Z e ∪ Ys D Z e n) \ {eV D Z e}

open Classical in
/-- Gluing map of the anti-clique absorber attached to the clique with index `t`. -/
noncomputable def gf (t : Fin D.k₁ ⊕ Fin D.k₂) (x : Z.T) : VT D Z :=
  if h : ∃ s, Z.rv s = x then Sum.inl (emb D t (Classical.choose h))
  else if h' : ∃ I ∈ Iset q r, ∃ s, Z.yv I s = x then
    yv D Z ((Classical.choose h').map (emb D t)) (lab D t (Classical.choose h'))
      (Classical.choose (Classical.choose_spec h').2)
  else Sum.inr (Sum.inr (t, x))

theorem gf_rv (t : Fin D.k₁ ⊕ Fin D.k₂) (s : Fin q) :
    gf D Z t (Z.rv s) = Sum.inl (emb D t s) := by
  have h : ∃ s', Z.rv s' = Z.rv s := ⟨s, rfl⟩
  rw [gf, dif_pos h, Z.rv.injective (Classical.choose_spec h)]

theorem gf_yv (t : Fin D.k₁ ⊕ Fin D.k₂) {I : Finset (Fin q)} (hI : I ∈ Iset q r)
    (s : Fin (q - r)) : gf D Z t (Z.yv I s) = yv D Z (I.map (emb D t)) (lab D t I) s := by
  have h1 : ¬ ∃ s', Z.rv s' = Z.yv I s := by
    rintro ⟨s', hs'⟩; exact Z.yv_ne_rv I hI s s' hs'.symm
  have h : ∃ I' ∈ Iset q r, ∃ s', Z.yv I' s' = Z.yv I s := ⟨I, hI, s, rfl⟩
  rw [gf, dif_neg h1, dif_pos h]
  have hs := Classical.choose_spec h
  have hs2 := Classical.choose_spec hs.2
  obtain ⟨hI', hs'⟩ := Z.yv_inj _ hs.1 _ hI _ _ hs2
  congr 1 <;> first | exact hs' | rw [hI']

theorem gf_fresh (t : Fin D.k₁ ⊕ Fin D.k₂) {x : Z.T} (h1 : ∀ s, Z.rv s ≠ x)
    (h2 : ∀ I ∈ Iset q r, ∀ s, Z.yv I s ≠ x) : gf D Z t x = Sum.inr (Sum.inr (t, x)) := by
  have h1' : ¬ ∃ s, Z.rv s = x := fun ⟨s, hs⟩ => h1 s hs
  have h2' : ¬ ∃ I ∈ Iset q r, ∃ s, Z.yv I s = x := fun ⟨I, hI, s, hs⟩ => h2 I hI s hs
  rw [gf, dif_neg h1', dif_neg h2']

theorem ac_kind (x : Z.T) : (∃ s, Z.rv s = x) ∨ (∃ I ∈ Iset q r, ∃ s, Z.yv I s = x) ∨
    ((∀ s, Z.rv s ≠ x) ∧ (∀ I ∈ Iset q r, ∀ s, Z.yv I s ≠ x)) := by
  by_cases h1 : ∃ s, Z.rv s = x
  · exact Or.inl h1
  · by_cases h2 : ∃ I ∈ Iset q r, ∃ s, Z.yv I s = x
    · exact Or.inr (Or.inl h2)
    · push_neg at h1 h2
      exact Or.inr (Or.inr ⟨h1, h2⟩)

theorem gf_injective (t : Fin D.k₁ ⊕ Fin D.k₂) : Function.Injective (gf D Z t) := by
  intro x y h
  rcases ac_kind Z x with ⟨s, rfl⟩ | ⟨I, hI, s, rfl⟩ | ⟨hx1, hx2⟩ <;>
    rcases ac_kind Z y with ⟨s', rfl⟩ | ⟨I', hI', s', rfl⟩ | ⟨hy1, hy2⟩
  · rw [gf_rv, gf_rv] at h
    rw [(emb D t).injective (Sum.inl_injective h)]
  · rw [gf_rv, gf_yv _ _ _ hI'] at h; simp [yv] at h
  · rw [gf_rv, gf_fresh _ _ _ hy1 hy2] at h; simp at h
  · rw [gf_yv _ _ _ hI, gf_rv] at h; simp [yv] at h
  · rw [gf_yv _ _ _ hI, gf_yv _ _ _ hI'] at h
    simp only [yv, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, -, h3⟩ := h
    rw [map_injective _ h1, h3]
  · rw [gf_yv _ _ _ hI, gf_fresh _ _ _ hy1 hy2] at h; simp [yv] at h
  · rw [gf_fresh _ _ _ hx1 hx2, gf_rv] at h; simp at h
  · rw [gf_fresh _ _ _ hx1 hx2, gf_yv _ _ _ hI'] at h; simp [yv] at h
  · rw [gf_fresh _ _ _ hx1 hx2, gf_fresh _ _ _ hy1 hy2] at h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact h.2

/-- The gluing embedding of the absorber attached to the clique with index `t`. -/
noncomputable def gE (t : Fin D.k₁ ⊕ Fin D.k₂) : Z.T ↪ VT D Z := ⟨gf D Z t, gf_injective D Z t⟩

/-- The anti-clique of the anti-clique absorber `Z`. -/
def ACg : Finset (Finset Z.T) :=
  (Iset q r).biUnion (fun I => cliqueEdges r (I.map Z.rv ∪ univ.image (Z.yv I)) \ {I.map Z.rv})

theorem gmap_ACg (t : Fin D.k₁ ⊕ Fin D.k₂) :
    gmap (gE D Z t) (ACg Z) = (Iset q r).biUnion (fun I => anti D Z (I.map (emb D t)) (lab D t I)) := by
  rw [ACg, gmap_biUnion]
  refine biUnion_congr rfl (fun I hI => ?_)
  have hrv : (I.map Z.rv).map (gE D Z t) = eV D Z (I.map (emb D t)) := by
    ext z
    simp [eV, gE, gf_rv]
  have hyv : (univ.image (Z.yv I)).map (gE D Z t) = Ys D Z (I.map (emb D t)) (lab D t I) := by
    ext z
    simp [Ys, gE, gf_yv D Z t hI]
  rw [gmap_sdiff, gmap_cliqueEdges, gmap_singleton, map_union, hrv, hyv, anti]

/-! ### Anti-edges -/

theorem rk_le {α : Type*} [DecidableEq α] (s : Finset α) (x : α) : rk s x ≤ s.card := by
  by_cases hx : x ∈ s
  · exact (rk_lt hx).le
  · rw [rk, dif_neg hx]; exact Nat.zero_le _

theorem cfin_inj {n n' : ℕ} (hn : n ≤ D.k₁) (hn' : n' ≤ D.k₁) (h : cfin D n = cfin D n') :
    n = n' := by
  have := congrArg Fin.val h
  simp only [cfin] at this
  omega

theorem card_eV (e : Finset V) : (eV D Z e).card = e.card := card_map _

theorem yv_injective (e : Finset V) (n : ℕ) : Function.Injective (yv D Z e n) := by
  intro s t h
  simp only [yv, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2.2

theorem card_Ys (e : Finset V) (n : ℕ) : (Ys D Z e n).card = q - r := by
  rw [Ys, card_image_of_injective _ (yv_injective D Z e n), card_univ, Fintype.card_fin]

theorem inl_ne_yv (x : V) (e : Finset V) (n : ℕ) (s : Fin (q - r)) :
    (Sum.inl x : VT D Z) ≠ yv D Z e n s := by simp [yv]

theorem disjoint_eV_Ys (e : Finset V) (n : ℕ) : Disjoint (eV D Z e) (Ys D Z e n) := by
  rw [disjoint_left]
  intro z hz hz'
  obtain ⟨x, -, rfl⟩ := mem_map.1 hz
  obtain ⟨s, -, hs⟩ := mem_image.1 hz'
  exact inl_ne_yv D Z x e n s hs.symm

theorem card_clique (hrq : r ≤ q) {e : Finset V} (he : e.card = r) (n : ℕ) :
    (eV D Z e ∪ Ys D Z e n).card = q := by
  rw [card_union_of_disjoint (disjoint_eV_Ys D Z e n), card_eV, card_Ys, he]; omega

theorem mem_anti {f : Finset (VT D Z)} {e : Finset V} {n : ℕ} :
    f ∈ anti D Z e n ↔ f ⊆ eV D Z e ∪ Ys D Z e n ∧ f.card = r ∧ f ≠ eV D Z e := by
  simp [anti, cliqueEdges, mem_powersetCard, and_assoc]

theorem anti_has_y {e : Finset V} {n : ℕ} {f : Finset (VT D Z)} (he : e.card = r)
    (hf : f ∈ anti D Z e n) : ∃ s, yv D Z e n s ∈ f := by
  rw [mem_anti] at hf
  obtain ⟨hsub, hc, hne⟩ := hf
  by_contra hno
  push_neg at hno
  apply hne
  have : f ⊆ eV D Z e := by
    intro z hz
    rcases mem_union.1 (hsub hz) with h | h
    · exact h
    · obtain ⟨s, -, rfl⟩ := mem_image.1 h; exact absurd hz (hno s)
  exact eq_of_subset_of_card_le this (by rw [card_eV, he, hc])

theorem anti_not_sub_inl {e : Finset V} {n : ℕ} {f : Finset (VT D Z)} (he : e.card = r)
    (hf : f ∈ anti D Z e n) : ¬ ∀ z ∈ f, ∃ x, z = Sum.inl x := by
  intro h
  obtain ⟨s, hs⟩ := anti_has_y D Z he hf
  obtain ⟨x, hx⟩ := h _ hs
  exact inl_ne_yv D Z x e n s hx.symm

/-- Valid anti-edge indices: an `r`-set and a copy number at most `k₁`. -/
def Valid (c : Finset V × ℕ) : Prop := c.1.card = r ∧ c.2 ≤ D.k₁

theorem disjoint_anti {c c' : Finset V × ℕ} (hc : Valid D c) (hc' : Valid D c') (hne : c ≠ c') :
    Disjoint (anti D Z c.1 c.2) (anti D Z c'.1 c'.2) := by
  rw [disjoint_left]
  intro f hf hf'
  obtain ⟨s, hs⟩ := anti_has_y D Z hc.1 hf
  have := ((mem_anti D Z).1 hf').1 hs
  rcases mem_union.1 this with h | h
  · obtain ⟨x, -, hx⟩ := mem_map.1 h
    exact inl_ne_yv D Z x _ _ s hx
  · obtain ⟨s', -, hs'⟩ := mem_image.1 h
    simp only [yv, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at hs'
    obtain ⟨h1, h2, -⟩ := hs'
    exact hne (Prod.ext h1.symm (cfin_inj D hc'.2 hc.2 h2).symm)

/-- Union of the anti-edges with indices in `C`. -/
def antiU (C : Finset (Finset V × ℕ)) : Finset (Finset (VT D Z)) :=
  C.biUnion (fun c => anti D Z c.1 c.2)

theorem disjoint_antiU {C C' : Finset (Finset V × ℕ)} (hC : ∀ c ∈ C, Valid D c)
    (hC' : ∀ c ∈ C', Valid D c) (hCC' : Disjoint C C') :
    Disjoint (antiU D Z C) (antiU D Z C') := by
  rw [antiU, antiU, disjoint_biUnion_left]
  intro c hc
  rw [disjoint_biUnion_right]
  intro c' hc'
  exact disjoint_anti D Z (hC c hc) (hC' c' hc') (fun h => disjoint_left.1 hCC' hc (h ▸ hc'))

theorem antiU_union (C C' : Finset (Finset V × ℕ)) :
    antiU D Z (C ∪ C') = antiU D Z C ∪ antiU D Z C' := union_biUnion

/-! ### Index sets -/

/-- The anti-edge indices of the anti-clique attached to the clique with index `t`. -/
noncomputable def idx (t : Fin D.k₁ ⊕ Fin D.k₂) : Finset (Finset V × ℕ) :=
  (Iset q r).image (fun I => (I.map (emb D t), lab D t I))

theorem gmap_ACg' (t : Fin D.k₁ ⊕ Fin D.k₂) : gmap (gE D Z t) (ACg Z) = antiU D Z (idx D t) := by
  rw [gmap_ACg, antiU, idx, image_biUnion]

theorem card_PS_le (e : Finset V) : (PS D e).card ≤ D.k₁ :=
  (card_le_univ _).trans (by simp)

theorem card_MS (e : Finset V) (he : e.card = r) : (MS D e).card = D.A e := D.cntM e he

theorem card_PS (e : Finset V) (he : e.card = r) :
    (PS D e).card = D.A e + if e ∈ L then 1 else 0 := D.cntP e he

theorem A_le_card_PS (e : Finset V) (he : e.card = r) : D.A e ≤ (PS D e).card := by
  rw [card_PS D e he]; exact Nat.le_add_right _ _

theorem valid_idx (t : Fin D.k₁ ⊕ Fin D.k₂) : ∀ c ∈ idx D t, Valid D c := by
  intro c hc
  obtain ⟨I, hI, rfl⟩ := mem_image.1 hc
  have hcI : (I.map (emb D t)).card = r := by rw [card_map, mem_Iset.1 hI]
  refine ⟨hcI, ?_⟩
  cases t with
  | inl i => exact (rk_le _ _).trans (card_PS_le D _)
  | inr j =>
    refine (rk_le _ _).trans ?_
    change (MS D (I.map (D.M j))).card ≤ D.k₁
    have hcI' : (I.map (D.M j)).card = r := hcI
    rw [card_MS D _ hcI']
    exact (A_le_card_PS D _ hcI').trans (card_PS_le D _)

theorem valid_L (hL : IsRGraph r L) :
    ∀ c ∈ L.image (fun e => (e, D.A e)), Valid D c := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := mem_image.1 hc
  refine ⟨hL e he, ?_⟩
  have := card_PS D e (hL e he)
  rw [if_pos he] at this
  have := card_PS_le D e
  simp only; omega

theorem mem_idxP {c : Finset V × ℕ} :
    c ∈ univ.biUnion (fun i => idx D (Sum.inl i)) ↔ c.1.card = r ∧ c.2 < (PS D c.1).card := by
  constructor
  · intro hc
    obtain ⟨i, -, hc⟩ := mem_biUnion.1 hc
    obtain ⟨I, hI, rfl⟩ := mem_image.1 hc
    refine ⟨by rw [card_map, mem_Iset.1 hI], rk_lt ?_⟩
    exact mem_filter.2 ⟨mem_univ _, map_subset_map.2 (subset_univ I)⟩
  · rintro ⟨hc, hn⟩
    obtain ⟨i, hi, hrk⟩ := rk_surj hn
    obtain ⟨I, hI, hIe⟩ := exists_Iset_map (mem_filter.1 hi).2 hc
    refine mem_biUnion.2 ⟨i, mem_univ _, mem_image.2 ⟨I, hI, ?_⟩⟩
    change (I.map (D.P i), rk (PS D (I.map (D.P i))) i) = c
    rw [hIe, hrk]

theorem mem_idxM_L (hL : IsRGraph r L) {c : Finset V × ℕ} :
    c ∈ univ.biUnion (fun j => idx D (Sum.inr j)) ∪ L.image (fun e => (e, D.A e)) ↔
      c.1.card = r ∧ c.2 < (PS D c.1).card := by
  constructor
  · intro hc
    rcases mem_union.1 hc with hc | hc
    · obtain ⟨j, -, hc⟩ := mem_biUnion.1 hc
      obtain ⟨I, hI, rfl⟩ := mem_image.1 hc
      have hcI : (I.map (D.M j)).card = r := by rw [card_map, mem_Iset.1 hI]
      refine ⟨hcI, ?_⟩
      change rk (MS D (I.map (D.M j))) j < (PS D (I.map (D.M j))).card
      refine lt_of_lt_of_le (rk_lt ?_) ?_
      · exact mem_filter.2 ⟨mem_univ _, map_subset_map.2 (subset_univ I)⟩
      · rw [card_MS D _ hcI]; exact A_le_card_PS D _ hcI
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hc
      refine ⟨hL e he, ?_⟩
      rw [card_PS D e (hL e he), if_pos he]
      exact Nat.lt_succ_self _
  · rintro ⟨hc, hn⟩
    rw [card_PS D _ hc] at hn
    by_cases hA : c.2 < D.A c.1
    · rw [← card_MS D _ hc] at hA
      obtain ⟨j, hj, hrk⟩ := rk_surj hA
      obtain ⟨I, hI, hIe⟩ := exists_Iset_map (mem_filter.1 hj).2 hc
      refine mem_union_left _ (mem_biUnion.2 ⟨j, mem_univ _, mem_image.2 ⟨I, hI, ?_⟩⟩)
      change (I.map (D.M j), rk (MS D (I.map (D.M j))) j) = c
      rw [hIe, hrk]
    · have hcL : c.1 ∈ L := by
        by_contra h
        rw [if_neg h] at hn
        omega
      rw [if_pos hcL] at hn
      refine mem_union_right _ (mem_image.2 ⟨c.1, hcL, ?_⟩)
      exact Prod.ext rfl (by simp only; omega)

theorem idxP_eq_idxM_L (hL : IsRGraph r L) :
    univ.biUnion (fun i => idx D (Sum.inl i)) =
      univ.biUnion (fun j => idx D (Sum.inr j)) ∪ L.image (fun e => (e, D.A e)) := by
  ext c
  rw [mem_idxP, mem_idxM_L D hL]

theorem idx_disjoint {t t' : Fin D.k₁ ⊕ Fin D.k₂} (hne : t ≠ t')
    (hsame : (∃ i i', t = Sum.inl i ∧ t' = Sum.inl i') ∨ (∃ j j', t = Sum.inr j ∧ t' = Sum.inr j')) :
    Disjoint (idx D t) (idx D t') := by
  rw [disjoint_left]
  intro c hc hc'
  obtain ⟨I, hI, rfl⟩ := mem_image.1 hc
  obtain ⟨I', hI', h⟩ := mem_image.1 hc'
  rcases hsame with ⟨i, i', rfl, rfl⟩ | ⟨j, j', rfl, rfl⟩
  · change (I'.map (D.P i'), rk (PS D (I'.map (D.P i'))) i') =
      (I.map (D.P i), rk (PS D (I.map (D.P i))) i) at h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [h1] at h2
    exact hne (congrArg Sum.inl (rk_inj
      (mem_filter.2 ⟨mem_univ _, map_subset_map.2 (subset_univ I)⟩)
      (mem_filter.2 ⟨mem_univ _, h1 ▸ map_subset_map.2 (subset_univ I')⟩) h2.symm))
  · change (I'.map (D.M j'), rk (MS D (I'.map (D.M j'))) j') =
      (I.map (D.M j), rk (MS D (I.map (D.M j))) j) at h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [h1] at h2
    exact hne (congrArg Sum.inr (rk_inj
      (mem_filter.2 ⟨mem_univ _, map_subset_map.2 (subset_univ I)⟩)
      (mem_filter.2 ⟨mem_univ _, h1 ▸ map_subset_map.2 (subset_univ I')⟩) h2.symm))

theorem idxM_disjoint_L (j : Fin D.k₂) :
    Disjoint (idx D (Sum.inr j)) (L.image (fun e => (e, D.A e))) := by
  rw [disjoint_left]
  intro c hc hc'
  obtain ⟨I, hI, rfl⟩ := mem_image.1 hc
  obtain ⟨e, -, h⟩ := mem_image.1 hc'
  have hcI : (I.map (D.M j)).card = r := by rw [card_map, mem_Iset.1 hI]
  change (e, D.A e) = (I.map (D.M j), rk (MS D (I.map (D.M j))) j) at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  have := rk_lt (s := MS D (I.map (D.M j))) (x := j)
    (mem_filter.2 ⟨mem_univ _, map_subset_map.2 (subset_univ I)⟩)
  rw [card_MS D _ hcI, ← h2, h1] at this
  exact lt_irrefl _ this

/-! ### The attached absorbers and the final absorber -/

/-- The copy of the anti-clique absorber's `Rest` attached to the clique with index `t`. -/
noncomputable def RestT (t : Fin D.k₁ ⊕ Fin D.k₂) : Finset (Finset (VT D Z)) :=
  gmap (gE D Z t) Z.Rest

/-- The vertices private to the attached absorber with index `t`. -/
def IsFresh (t : Fin D.k₁ ⊕ Fin D.k₂) (z : VT D Z) : Prop := ∃ x, z = Sum.inr (Sum.inr (t, x))

theorem gf_isFresh {t t' : Fin D.k₁ ⊕ Fin D.k₂} {y : Z.T} (h : IsFresh D Z t (gf D Z t' y)) :
    t = t' := by
  obtain ⟨x, hx⟩ := h
  rcases ac_kind Z y with ⟨s, rfl⟩ | ⟨I, hI, s, rfl⟩ | ⟨hy1, hy2⟩
  · rw [gf_rv] at hx; simp at hx
  · rw [gf_yv _ _ _ hI] at hx; simp [yv] at hx
  · rw [gf_fresh _ _ _ hy1 hy2] at hx
    simp only [Sum.inr.injEq, Prod.mk.injEq] at hx
    exact hx.1.symm

theorem RestT_fresh (t : Fin D.k₁ ⊕ Fin D.k₂) : ∀ f ∈ RestT D Z t, ∃ z ∈ f, IsFresh D Z t z := by
  intro f hf
  obtain ⟨f₀, hf₀, rfl⟩ := mem_gmap.1 hf
  obtain ⟨x, hx, hxn⟩ := not_subset.1 (Z.rest_indep f₀ hf₀)
  have h1 : ∀ s, Z.rv s ≠ x := fun s hs =>
    hxn (mem_union_left _ (hs ▸ mem_map_of_mem _ (mem_univ s)))
  have h2 : ∀ I ∈ Iset q r, ∀ s, Z.yv I s ≠ x := fun I hI s hs =>
    hxn (mem_union_right _ (mem_biUnion.2 ⟨I, hI, hs ▸ mem_image_of_mem _ (mem_univ s)⟩))
  refine ⟨gE D Z t x, mem_map_of_mem _ hx, x, ?_⟩
  exact gf_fresh D Z t h1 h2

theorem RestT_not_fresh {t t' : Fin D.k₁ ⊕ Fin D.k₂} (hne : t ≠ t') :
    ∀ f ∈ RestT D Z t', ∀ z ∈ f, ¬ IsFresh D Z t z := by
  intro f hf z hz hfr
  obtain ⟨f₀, -, rfl⟩ := mem_gmap.1 hf
  obtain ⟨y, -, rfl⟩ := mem_map.1 hz
  exact hne (gf_isFresh D Z hfr)

theorem disjoint_RestT {t t' : Fin D.k₁ ⊕ Fin D.k₂} (hne : t ≠ t') :
    Disjoint (RestT D Z t) (RestT D Z t') :=
  disjoint_of_vertex (IsFresh D Z t) (RestT_fresh D Z t) (RestT_not_fresh D Z hne)

theorem clique_not_fresh (t : Fin D.k₁ ⊕ Fin D.k₂) {e : Finset V} {n : ℕ} {z : VT D Z}
    (hz : z ∈ eV D Z e ∪ Ys D Z e n) : ¬ IsFresh D Z t z := by
  rintro ⟨x, rfl⟩
  rcases mem_union.1 hz with h | h
  · obtain ⟨y, -, hy⟩ := mem_map.1 h; simp at hy
  · obtain ⟨s, -, hs⟩ := mem_image.1 h; simp [yv] at hs

theorem antiU_not_fresh (t : Fin D.k₁ ⊕ Fin D.k₂) (C : Finset (Finset V × ℕ)) :
    ∀ f ∈ antiU D Z C, ∀ z ∈ f, ¬ IsFresh D Z t z := by
  intro f hf z hz
  obtain ⟨c, -, hfc⟩ := mem_biUnion.1 hf
  exact clique_not_fresh D Z t (((mem_anti D Z).1 hfc).1 hz)

theorem disjoint_RestT_antiU (t : Fin D.k₁ ⊕ Fin D.k₂) (C : Finset (Finset V × ℕ)) :
    Disjoint (RestT D Z t) (antiU D Z C) :=
  disjoint_of_vertex (IsFresh D Z t) (RestT_fresh D Z t) (antiU_not_fresh D Z t C)

theorem antiU_biUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → Finset (Finset V × ℕ)) :
    antiU D Z (s.biUnion g) = s.biUnion (fun i => antiU D Z (g i)) := biUnion_biUnion _ _ _

theorem RestT_dec (t : Fin D.k₁ ⊕ Fin D.k₂) : HasDecomposition q r (RestT D Z t) := by
  obtain ⟨𝒬, h𝒬⟩ := Z.rest_dec
  exact ⟨_, h𝒬.gmap (gE D Z t)⟩

theorem RestT_AC_dec (t : Fin D.k₁ ⊕ Fin D.k₂) :
    HasDecomposition q r (RestT D Z t ∪ antiU D Z (idx D t)) := by
  obtain ⟨𝒬, h𝒬⟩ := Z.restAC_dec
  have := h𝒬.gmap (gE D Z t)
  rw [gmap_union] at this
  change IsDecomposition q r (gmap (gE D Z t) Z.Rest ∪ gmap (gE D Z t) (ACg Z)) _ at this
  rw [gmap_ACg'] at this
  exact ⟨_, this⟩

/-- The absorber: all attached absorbers together with all anti-edges. -/
noncomputable def Abs : Finset (Finset (VT D Z)) :=
  univ.biUnion (fun i => RestT D Z (Sum.inl i)) ∪ univ.biUnion (fun j => RestT D Z (Sum.inr j)) ∪
    antiU D Z (univ.biUnion (fun i => idx D (Sum.inl i)))

/-- The copy of `L` on the original vertices. -/
def Lc (L : Finset (Finset V)) : Finset (Finset (VT D Z)) := gmap Function.Embedding.inl L

theorem Abs_dec (hrq : r ≤ q) : HasDecomposition q r (Abs D Z) := by
  have hF₁ : HasDecomposition q r
      (univ.biUnion (fun i => RestT D Z (Sum.inl i) ∪ antiU D Z (idx D (Sum.inl i)))) := by
    refine HasDecomposition.biUnion' hrq _ _ (fun i _ i' _ hne => ?_)
      (fun i _ => RestT_AC_dec D Z _)
    have hne' : (Sum.inl i : Fin D.k₁ ⊕ Fin D.k₂) ≠ Sum.inl i' := fun h => hne (Sum.inl_injective h)
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨disjoint_RestT D Z hne', disjoint_RestT_antiU D Z _ _⟩,
      (disjoint_RestT_antiU D Z _ _).symm,
      disjoint_antiU D Z (valid_idx D _) (valid_idx D _) (idx_disjoint D hne' (Or.inl ⟨i, i', rfl, rfl⟩))⟩
  have hF₂ : HasDecomposition q r (univ.biUnion (fun j => RestT D Z (Sum.inr j))) := by
    refine HasDecomposition.biUnion' hrq _ _ (fun j _ j' _ hne => ?_)
      (fun j _ => RestT_dec D Z _)
    exact disjoint_RestT D Z (fun h => hne (Sum.inr_injective h))
  have hdisj : Disjoint (univ.biUnion (fun i => RestT D Z (Sum.inl i) ∪ antiU D Z (idx D (Sum.inl i))))
      (univ.biUnion (fun j => RestT D Z (Sum.inr j))) := by
    rw [disjoint_biUnion_left]
    intro i _
    rw [disjoint_biUnion_right]
    intro j _
    rw [disjoint_union_left]
    exact ⟨disjoint_RestT D Z (by simp), (disjoint_RestT_antiU D Z _ _).symm⟩
  have := HasDecomposition.union' hrq hdisj hF₁ hF₂
  have heq : univ.biUnion (fun i => RestT D Z (Sum.inl i) ∪ antiU D Z (idx D (Sum.inl i))) ∪
      univ.biUnion (fun j => RestT D Z (Sum.inr j)) = Abs D Z := by
    rw [biUnion_union, Abs, antiU_biUnion]
    ext f; simp only [mem_union]; tauto
  rwa [heq] at this

theorem clique_eq (e : Finset V) (he : e.card = r) (n : ℕ) :
    cliqueEdges r (eV D Z e ∪ Ys D Z e n) = anti D Z e n ∪ {eV D Z e} := by
  rw [anti, sdiff_union_self_eq_union]
  refine (union_eq_left.2 ?_).symm
  rw [singleton_subset_iff, cliqueEdges, mem_powersetCard]
  exact ⟨subset_union_left, by rw [card_eV, he]⟩

theorem Lc_not_y {f : Finset (VT D Z)} (hf : f ∈ Lc D Z L) (e : Finset V) (n : ℕ) (s : Fin (q - r)) :
    yv D Z e n s ∉ f := by
  intro h
  obtain ⟨f₀, -, rfl⟩ := mem_gmap.1 hf
  obtain ⟨x, -, hx⟩ := mem_map.1 h
  exact inl_ne_yv D Z x e n s hx

theorem disjoint_antiU_Lc {C : Finset (Finset V × ℕ)} (hC : ∀ c ∈ C, Valid D c) :
    Disjoint (antiU D Z C) (Lc D Z L) := by
  rw [antiU, disjoint_biUnion_left]
  intro c hc
  rw [disjoint_left]
  intro f hf hfL
  obtain ⟨s, hs⟩ := anti_has_y D Z (hC c hc).1 hf
  exact Lc_not_y D Z hfL _ _ s hs

theorem Lc_not_fresh (t : Fin D.k₁ ⊕ Fin D.k₂) : ∀ f ∈ Lc D Z L, ∀ z ∈ f, ¬ IsFresh D Z t z := by
  intro f hf z hz ⟨x, hx⟩
  obtain ⟨f₀, -, rfl⟩ := mem_gmap.1 hf
  obtain ⟨y, -, rfl⟩ := mem_map.1 hz
  simp at hx

theorem Lcl_eq (hL : IsRGraph r L) :
    L.biUnion (fun e => cliqueEdges r (eV D Z e ∪ Ys D Z e (D.A e))) =
      antiU D Z (L.image (fun e => (e, D.A e))) ∪ Lc D Z L := by
  rw [antiU, image_biUnion]
  have : L.biUnion (fun e => cliqueEdges r (eV D Z e ∪ Ys D Z e (D.A e))) =
      L.biUnion (fun e => anti D Z e (D.A e) ∪ {eV D Z e}) :=
    biUnion_congr rfl (fun e he => clique_eq D Z e (hL e he) _)
  rw [this, biUnion_union]
  congr 1
  ext f
  simp only [mem_biUnion, mem_singleton, Lc, mem_gmap, eV]
  constructor
  · rintro ⟨e, he, rfl⟩; exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩; exact ⟨e, he, rfl⟩

theorem anti_disjoint_eV {e₁ e₂ : Finset V} {n : ℕ} (he₁ : e₁.card = r) :
    Disjoint (anti D Z e₁ n) {eV D Z e₂} := by
  rw [disjoint_singleton_right]
  intro h
  obtain ⟨s, hs⟩ := anti_has_y D Z he₁ h
  obtain ⟨x, -, hx⟩ := mem_map.1 hs
  exact inl_ne_yv D Z x _ _ s hx

theorem Lcl_dec (hrq : r ≤ q) (hL : IsRGraph r L) :
    HasDecomposition q r (L.biUnion (fun e => cliqueEdges r (eV D Z e ∪ Ys D Z e (D.A e)))) := by
  refine HasDecomposition.biUnion' hrq _ _ (fun e he e' he' hne => ?_)
    (fun e he => ?_)
  swap
  · show HasDecomposition q r (cliqueEdges r (eV D Z e ∪ Ys D Z e (D.A e)))
    exact ⟨{eV D Z e ∪ Ys D Z e (D.A e)}, isDecomposition_singleton (card_clique D Z hrq (hL e he) _)⟩
  show Disjoint (cliqueEdges r (eV D Z e ∪ Ys D Z e (D.A e)))
    (cliqueEdges r (eV D Z e' ∪ Ys D Z e' (D.A e')))
  rw [clique_eq D Z e (hL e he), clique_eq D Z e' (hL e' he'), disjoint_union_left,
    disjoint_union_right, disjoint_union_right]
  have hv : Valid D (e, D.A e) := valid_L D hL _ (mem_image_of_mem (fun e => (e, D.A e)) he)
  have hv' : Valid D (e', D.A e') := valid_L D hL _ (mem_image_of_mem (fun e => (e, D.A e)) he')
  have hne' : (e, D.A e) ≠ (e', D.A e') := fun h => hne (congrArg Prod.fst h)
  have h1 := disjoint_anti D Z hv hv' hne'
  dsimp only at h1
  have h2 : Disjoint (anti D Z e (D.A e)) {eV D Z e'} := anti_disjoint_eV D Z (hL e he)
  have h3 : Disjoint {eV D Z e} (anti D Z e' (D.A e')) := (anti_disjoint_eV D Z (hL e' he')).symm
  have h4 : Disjoint ({eV D Z e} : Finset (Finset (VT D Z))) {eV D Z e'} := by
    rw [disjoint_singleton_left, mem_singleton]
    intro h
    apply hne
    have h' : e.map (Function.Embedding.inl : V ↪ VT D Z) = e'.map Function.Embedding.inl := h
    exact map_injective _ h'
  exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem Abs_L_dec (hrq : r < q) (hL : IsRGraph r L) :
    HasDecomposition q r (Abs D Z ∪ Lc D Z L) := by
  have hrq' := hrq.le
  have hF₃ : HasDecomposition q r (univ.biUnion (fun i => RestT D Z (Sum.inl i))) := by
    refine HasDecomposition.biUnion' hrq' _ _ (fun i _ i' _ hne => ?_)
      (fun i _ => RestT_dec D Z _)
    exact disjoint_RestT D Z (fun h => hne (Sum.inl_injective h))
  have hF₄ : HasDecomposition q r
      (univ.biUnion (fun j => RestT D Z (Sum.inr j) ∪ antiU D Z (idx D (Sum.inr j)))) := by
    refine HasDecomposition.biUnion' hrq' _ _ (fun j _ j' _ hne => ?_)
      (fun j _ => RestT_AC_dec D Z _)
    have hne' : (Sum.inr j : Fin D.k₁ ⊕ Fin D.k₂) ≠ Sum.inr j' := fun h => hne (Sum.inr_injective h)
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨disjoint_RestT D Z hne', disjoint_RestT_antiU D Z _ _⟩,
      (disjoint_RestT_antiU D Z _ _).symm,
      disjoint_antiU D Z (valid_idx D _) (valid_idx D _) (idx_disjoint D hne' (Or.inr ⟨j, j', rfl, rfl⟩))⟩
  have hF₅ := Lcl_dec D Z hrq' hL
  rw [Lcl_eq D Z hL] at hF₅
  have h34 : Disjoint (univ.biUnion (fun i => RestT D Z (Sum.inl i)))
      (univ.biUnion (fun j => RestT D Z (Sum.inr j) ∪ antiU D Z (idx D (Sum.inr j)))) := by
    rw [disjoint_biUnion_left]
    intro i _
    rw [disjoint_biUnion_right]
    intro j _
    rw [disjoint_union_right]
    exact ⟨disjoint_RestT D Z (by simp), disjoint_RestT_antiU D Z _ _⟩
  have h345 : Disjoint (univ.biUnion (fun i => RestT D Z (Sum.inl i)) ∪
      univ.biUnion (fun j => RestT D Z (Sum.inr j) ∪ antiU D Z (idx D (Sum.inr j))))
      (antiU D Z (L.image (fun e => (e, D.A e))) ∪ Lc D Z L) := by
    have hR : ∀ t : Fin D.k₁ ⊕ Fin D.k₂,
        Disjoint (RestT D Z t) (antiU D Z (L.image (fun e => (e, D.A e))) ∪ Lc D Z L) := by
      intro t
      rw [disjoint_union_right]
      exact ⟨disjoint_RestT_antiU D Z _ _,
        disjoint_of_vertex (IsFresh D Z t) (RestT_fresh D Z t) (Lc_not_fresh D Z t)⟩
    rw [disjoint_union_left, disjoint_biUnion_left, disjoint_biUnion_left]
    refine ⟨fun i _ => hR _, fun j _ => ?_⟩
    rw [disjoint_union_left]
    refine ⟨hR _, ?_⟩
    rw [disjoint_union_right]
    exact ⟨disjoint_antiU D Z (valid_idx D _) (valid_L D hL) (idxM_disjoint_L D j),
      disjoint_antiU_Lc D Z (valid_idx D _)⟩
  have := HasDecomposition.union' hrq' h345 (HasDecomposition.union' hrq' h34 hF₃ hF₄) hF₅
  have heq : univ.biUnion (fun i => RestT D Z (Sum.inl i)) ∪
      univ.biUnion (fun j => RestT D Z (Sum.inr j) ∪ antiU D Z (idx D (Sum.inr j))) ∪
      (antiU D Z (L.image (fun e => (e, D.A e))) ∪ Lc D Z L) = Abs D Z ∪ Lc D Z L := by
    rw [biUnion_union, Abs, idxP_eq_idxM_L D hL, antiU_union, antiU_biUnion]
    ext f; simp only [mem_union]; tauto
  rwa [heq] at this

theorem Abs_independent :
    ∀ f ∈ Abs D Z, ¬ f ⊆ vertexSet (Lc D Z L) := by
  intro f hf hsub
  rw [Lc, vertexSet_gmap] at hsub
  have hinl : ∀ z ∈ f, ∃ x, z = Sum.inl x := by
    intro z hz
    obtain ⟨x, -, rfl⟩ := mem_map.1 (hsub hz)
    exact ⟨x, rfl⟩
  rcases mem_union.1 hf with hf | hf
  · have : ∃ t, f ∈ RestT D Z t := by
      rcases mem_union.1 hf with hf | hf
      · obtain ⟨i, -, hi⟩ := mem_biUnion.1 hf; exact ⟨_, hi⟩
      · obtain ⟨j, -, hj⟩ := mem_biUnion.1 hf; exact ⟨_, hj⟩
    obtain ⟨t, ht⟩ := this
    obtain ⟨z, hz, x, rfl⟩ := RestT_fresh D Z t f ht
    obtain ⟨y, hy⟩ := hinl _ hz
    simp at hy
  · obtain ⟨c, hc, hfc⟩ := mem_biUnion.1 hf
    have hv : Valid D c := by
      obtain ⟨i, -, hi⟩ := mem_biUnion.1 hc
      exact valid_idx D _ c hi
    exact anti_not_sub_inl D Z hv.1 hfc hinl

/-- **Absorber from a multi-absorber.** -/
theorem isAbsorber_Abs (hrq : r < q) (hL : IsRGraph r L) (hdiv : IsDivisible q r L) :
    IsAbsorber q r (Lc D Z L) (Abs D Z) :=
  ⟨hdiv.gmap _, Abs_independent D Z, Abs_dec D Z hrq.le, Abs_L_dec D Z hrq hL⟩

end construction

end RefinedAbsorption.Absorber17
