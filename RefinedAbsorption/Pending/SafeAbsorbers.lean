module
public import RefinedAbsorption.Pending.RootLight
public import RefinedAbsorption.Pending.SafeEmbed
public import RefinedAbsorption.Placement.Absorbers

/-!
# Attached absorbers whose cliques are safe with respect to a given packing

`safePlacedAttachedAbsorbers`: the attached absorbers of `Placement.placedAttachedAbsorbers`, built
from the root-light library (`rootLightLibrary`, from Lemma 6.4) and placed with the safe Partial
Clique Embedding Lemma (`safePartialCliqueEmbedding`), so that every clique of every on-mode and
off-mode decomposition meets every member of a given `K_q^r`-packing `Pk` in at most `r` vertices.

This is the first modification of Section 6.3 of arXiv:2402.17855v1 (the absorbers).
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset RefinedAbsorption.Absorber17 RefinedAbsorption.Placement

/-- The `(r+1)`-subsets of the members of `Pk`. -/
def packSets {n : ℕ} (r : ℕ) (Pk : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  Pk.biUnion fun P => P.powersetCard (r + 1)

/-- In a packing, a set has at most `q` one-vertex extensions inside `packSets`. -/
theorem card_ext_packSets_le {n q r : ℕ} {Pk : Finset (Finset (Fin n))}
    (hcard : ∀ P ∈ Pk, P.card = q) (hmult : ∀ f : Finset (Fin n), f.card = r → cliqueMult Pk f ≤ 1)
    (T : Finset (Fin n)) :
    (univ.filter fun v => v ∉ T ∧ insert v T ∈ packSets r Pk).card ≤ q := by
  by_cases hne : (univ.filter fun v => v ∉ T ∧ insert v T ∈ packSets r Pk).Nonempty
  · obtain ⟨v₀, hv₀⟩ := hne
    obtain ⟨-, hv₀T, hv₀S⟩ := mem_filter.1 hv₀
    obtain ⟨P₀, hP₀, hsub₀⟩ := mem_biUnion.1 hv₀S
    obtain ⟨hsub₀, hc₀⟩ := mem_powersetCard.1 hsub₀
    have hTc : T.card = r := by
      rw [card_insert_of_notMem hv₀T] at hc₀; omega
    have hsub : (univ.filter fun v => v ∉ T ∧ insert v T ∈ packSets r Pk) ⊆ P₀ := by
      intro v hv
      obtain ⟨-, hvT, hvS⟩ := mem_filter.1 hv
      obtain ⟨P, hP, hsubP⟩ := mem_biUnion.1 hvS
      have hsubP := (mem_powersetCard.1 hsubP).1
      have hPP : P = P₀ := by
        have h1 := hmult T hTc
        unfold cliqueMult at h1
        have hm : P ∈ Pk.filter (fun Q => T ⊆ Q) :=
          mem_filter.2 ⟨hP, (subset_insert v T).trans hsubP⟩
        have hm₀ : P₀ ∈ Pk.filter (fun Q => T ⊆ Q) :=
          mem_filter.2 ⟨hP₀, (subset_insert v₀ T).trans hsub₀⟩
        exact card_le_one.1 h1 P hm P₀ hm₀
      rw [← hPP]
      exact hsubP (mem_insert_self v T)
    exact (card_le_card hsub).trans (hcard P₀ hP₀).le
  · rw [not_nonempty_iff_eq_empty.1 hne]
    exact Nat.zero_le _

/-- Root intersections do not grow under maps sending new vertices to new vertices. -/
theorem card_inter_map_le_gen {α β γ δ : Type*} [Fintype α] [Fintype γ] [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ] (f : α ⊕ β ↪ γ ⊕ δ)
    (hf' : ∀ p, ∃ p', f (Sum.inr p) = Sum.inr p') (P : Finset (α ⊕ β)) :
    (P.map f ∩ univ.map Function.Embedding.inl).card ≤
      (P ∩ univ.map Function.Embedding.inl).card := by
  rw [← card_map f]
  apply card_le_card
  intro y hy
  obtain ⟨hyP, hyl⟩ := mem_inter.1 hy
  obtain ⟨x, hxP, rfl⟩ := mem_map.1 hyP
  obtain ⟨a, -, ha⟩ := mem_map.1 hyl
  refine mem_map_of_mem _ (mem_inter.2 ⟨hxP, ?_⟩)
  rcases x with b | p
  · exact mem_map_of_mem _ (mem_univ b)
  · obtain ⟨p', hp'⟩ := hf' p
    rw [hp'] at ha
    exact absurd ha Sum.inl_ne_inr

/-- **A placed root-light clique is safe.** -/
theorem placeEdge_inter_le {n h r : ℕ} {Pk : Finset (Finset (Fin n))} {R : Finset (Fin n)}
    {φ : Fin h → Fin n} (hφ : ValidPlacement R φ)
    (hsafe : ∀ S ∈ packSets r Pk, S ⊆ R ∪ auxImage φ → S ⊆ R)
    {t : Finset (Fin n ⊕ Fin h)} (ht : (t ∩ univ.map Function.Embedding.inl).card ≤ r)
    (htR : ∀ a, Sum.inl a ∈ t → a ∈ R) :
    ∀ P ∈ Pk, (placeEdge φ t ∩ P).card ≤ r := by
  intro P hP
  by_contra hgt
  push_neg at hgt
  obtain ⟨S, hSsub, hSc⟩ := exists_subset_card_eq (show r + 1 ≤ (placeEdge φ t ∩ P).card by omega)
  have hSmem : S ∈ packSets r Pk :=
    mem_biUnion.2 ⟨P, hP, mem_powersetCard.2 ⟨hSsub.trans inter_subset_right, hSc⟩⟩
  have hplace : placeEdge φ t ⊆ R ∪ auxImage φ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    rcases y with a | p
    · exact mem_union_left _ (htR a hy)
    · exact mem_union_right _ (mem_image_of_mem _ (mem_univ p))
  have hSR := hsafe S hSmem ((hSsub.trans inter_subset_left).trans hplace)
  have hle : (placeEdge φ t ∩ R).card ≤ (t ∩ univ.map Function.Embedding.inl).card := by
    have hsub : placeEdge φ t ∩ R ⊆ (t ∩ univ.map Function.Embedding.inl).image (emb φ) := by
      intro x hx
      obtain ⟨hxt, hxR⟩ := mem_inter.1 hx
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hxt
      rcases y with a | p
      · exact mem_image.2 ⟨Sum.inl a, mem_inter.2 ⟨hy, mem_map_of_mem _ (mem_univ a)⟩, rfl⟩
      · exact absurd hxR (hφ.2 p)
    exact (card_le_card hsub).trans card_image_le
  have : S ⊆ placeEdge φ t ∩ R := fun x hx =>
    mem_inter.2 ⟨(mem_inter.1 (hSsub hx)).1, hSR hx⟩
  have := card_le_card this
  omega

/-- **Root-light rooted templates**: like `exists_rootedTemplate`, with the root-light library. -/
theorem exists_rootLightGadget {q r : ℕ} (c B : ℕ)
    (hB : ∀ (k : ℕ) (LS : Finset (Finset (Fin k))), k ≤ r * c → IsRGraph r LS →
      IsDivisible q r LS → vertexSet LS = univ →
      ∃ A Qon Qoff : Finset (Finset (Fin k ⊕ Fin B)),
        IsAbsorber q r (RefinedAbsorption.gmap Function.Embedding.inl LS) A ∧
        IsDecomposition q r (A ∪ RefinedAbsorption.gmap Function.Embedding.inl LS) Qon ∧
        IsDecomposition q r A Qoff ∧
        ∀ P ∈ Qon ∪ Qoff, (P ∩ univ.map Function.Embedding.inl).card ≤ r)
    {n : ℕ} (W : Finset (Finset (Fin n))) (hW : IsRGraph r W) (hdiv : IsDivisible q r W)
    (hc : W.card ≤ c) (hne : W.Nonempty) :
    ∃ T Ton Toff : Finset (Finset (Fin n ⊕ Fin B)),
      GadgetWF r (r * c) (vertexSet W) T ∧
      (∀ t ∈ Ton ∪ Toff, (t ∩ univ.map Function.Embedding.inl).card ≤ r ∧
        ∀ a, Sum.inl a ∈ t → a ∈ vertexSet W) ∧
      ∀ φ, ValidPlacement (vertexSet W) φ →
        IsDecomposition q r (newEdges T φ ∪ W) (newEdges Ton φ) ∧
        IsDecomposition q r (newEdges T φ) (newEdges Toff φ) := by
  classical
  set Tv := vertexSet W with hTv
  set k := Tv.card with hk
  have hkc : k ≤ r * c := card_vertexSet_le hW hc
  let ψ : Fin k ↪ Fin n := ⟨fun i => (Tv.equivFin.symm i).1, fun i j h =>
    Tv.equivFin.symm.injective (Subtype.val_injective h)⟩
  have hψ : ∀ i, ψ i ∈ Tv := fun i => (Tv.equivFin.symm i).2
  have hrange : ∀ x ∈ Tv, ∃ i, ψ i = x := fun x hx =>
    ⟨Tv.equivFin ⟨x, hx⟩, by
      change ((Tv.equivFin.symm (Tv.equivFin ⟨x, hx⟩)) : Fin n) = x
      simp⟩
  have hpre : ∀ e ∈ W, (e.preimage ψ ψ.injective.injOn).map ψ = e := by
    intro e he
    ext x
    simp only [mem_map, mem_preimage]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      obtain ⟨i, rfl⟩ := hrange x (subset_vertexSet he hx)
      exact ⟨i, hx, rfl⟩
  set LS : Finset (Finset (Fin k)) := W.image (fun e => e.preimage ψ ψ.injective.injOn)
    with hLSdef
  have hLS : RefinedAbsorption.gmap ψ LS = W := by
    ext e
    simp only [mem_gmap, hLSdef, mem_image]
    constructor
    · rintro ⟨e₀, ⟨e', he', rfl⟩, rfl⟩; rw [hpre e' he']; exact he'
    · intro he; exact ⟨_, ⟨e, he, rfl⟩, hpre e he⟩
  have hLSr : IsRGraph r LS := by
    intro e₀ he₀
    rw [← card_map ψ]
    exact hW _ (hLS ▸ map_mem_gmap.2 he₀)
  have hLSd : IsDivisible q r LS := by
    intro S₀ hS₀
    rw [← deg_gmap_map ψ, hLS]
    have := hdiv (S₀.map ψ) (by rwa [card_map])
    rwa [card_map] at this
  have hLSV : vertexSet LS = univ := by
    ext i
    simp only [mem_univ, iff_true]
    obtain ⟨e, he, hie⟩ : ∃ e ∈ W, ψ i ∈ e := by
      have := hψ i
      simp only [hTv, vertexSet, mem_sup, id] at this
      exact this
    refine subset_vertexSet (mem_image_of_mem _ he) ?_
    simpa using hie
  obtain ⟨A, Qon, Qoff, hA, hon, hoff, hlight⟩ := hB k LS hkc hLSr hLSd hLSV
  refine ⟨RefinedAbsorption.gmap (rootSumEmb ψ) A, RefinedAbsorption.gmap (rootSumEmb ψ) Qon,
    RefinedAbsorption.gmap (rootSumEmb ψ) Qoff, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact card_vertexSet_le hW hc
  · obtain ⟨e, he⟩ := hne
    calc r - 1 ≤ e.card := by rw [hW e he]; omega
      _ ≤ _ := card_le_card (subset_vertexSet he)
  · intro t ht
    obtain ⟨e, he, rfl⟩ := mem_gmap.1 ht
    rw [card_map]
    exact hoff.rgraph e he
  · intro t ht a ha
    obtain ⟨e, he, rfl⟩ := mem_gmap.1 ht
    obtain ⟨y, -, hy⟩ := mem_map.1 ha
    rcases y with i | j
    · have : ψ i = a := by simpa [rootSumEmb] using hy
      rw [← this]; exact hψ i
    · simp [rootSumEmb] at hy
  · intro t ht
    obtain ⟨e, he, rfl⟩ := mem_gmap.1 ht
    by_contra hno
    push_neg at hno
    apply hA.independent e he
    intro x hx
    rcases x with i | j
    · rw [vertexSet_gmap, hLSV]
      exact mem_map_of_mem _ (mem_univ i)
    · exact absurd (mem_map_of_mem (rootSumEmb ψ) hx) (hno j)
  · intro t ht
    have hg : ∀ p, ∃ p', (rootSumEmb (B := B) ψ) (Sum.inr p) = Sum.inr p' := fun p => ⟨p, rfl⟩
    have hP : ∃ P ∈ Qon ∪ Qoff, P.map (rootSumEmb ψ) = t := by
      rcases mem_union.1 ht with ht | ht
      · obtain ⟨P, hP, rfl⟩ := mem_gmap.1 ht
        exact ⟨P, mem_union_left _ hP, rfl⟩
      · obtain ⟨P, hP, rfl⟩ := mem_gmap.1 ht
        exact ⟨P, mem_union_right _ hP, rfl⟩
    obtain ⟨P, hP, rfl⟩ := hP
    refine ⟨(card_inter_map_le_gen _ hg P).trans (hlight P hP), fun a ha => ?_⟩
    obtain ⟨y, -, hy⟩ := mem_map.1 ha
    rcases y with i | j
    · have : ψ i = a := by simpa [rootSumEmb] using hy
      rw [← this]; exact hψ i
    · simp [rootSumEmb] at hy
  · rintro φ ⟨hinj, havoid⟩
    let φe : Fin B ↪ Fin n := ⟨φ, hinj⟩
    have hdisj : ∀ i j, ψ i ≠ φe j := fun i j h =>
      havoid j (by rw [← show ψ i = φ j from h]; exact hψ i)
    show IsDecomposition q r (newEdges _ ⇑φe ∪ W) (newEdges _ ⇑φe) ∧
      IsDecomposition q r (newEdges _ ⇑φe) (newEdges _ ⇑φe)
    rw [newEdges_gmap_rootSumEmb ψ φe hdisj, newEdges_gmap_rootSumEmb ψ φe hdisj,
      newEdges_gmap_rootSumEmb ψ φe hdisj]
    have hinl : Function.Embedding.inl.trans (sumElimEmb ψ φe hdisj) = ψ := by ext i; rfl
    refine ⟨?_, hoff.gmap _⟩
    have := hon.gmap (sumElimEmb ψ φe hdisj)
    rwa [gmap_union, gmap_gmap, hinl, hLS] at this

/-- **Safe attached absorbers inside `K_n^r`.**  As `placedAttachedAbsorbers`, with in addition a
`K_q^r`-packing `Pk`: every clique of every on- and off-mode meets every member of `Pk` in at
most `r` vertices. -/
theorem safePlacedAttachedAbsorbers {q r : ℕ} (hr : 1 ≤ r) (hrq : r < q) (c : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ) (X R : Finset (Finset (Fin n)))
      (𝒲 : Finset (Finset (Finset (Fin n)))) (D : ℕ) (Pk : Finset (Finset (Fin n))),
      (∀ W ∈ 𝒲, IsRGraph r W) → (∀ W ∈ 𝒲, IsDivisible q r W) → (∀ W ∈ 𝒲, W.card ≤ c) →
      (∀ S : Finset (Fin n), S.card = r - 1 → C * deg (X ∪ R) S ≤ n) →
      (∀ S : Finset (Fin n), S.card = r - 1 → (𝒲.filter fun W => S ⊆ vertexSet W).card ≤ D) →
      C * D ≤ n → 0 < n →
      (∀ P ∈ Pk, P.card = q) → (∀ f : Finset (Fin n), f.card = r → cliqueMult Pk f ≤ 1) →
      C * q ≤ n →
      ∃ A Qon Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n)),
        IsAttachedAbsorbers q r X R 𝒲 A Qon Qoff ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → deg (𝒲.sup A) S ≤ C * D) ∧
        ∀ W ∈ 𝒲, ∀ Q ∈ Qon W ∪ Qoff W, ∀ P ∈ Pk, (Q ∩ P).card ≤ r := by
  classical
  obtain ⟨B, hB⟩ := rootLightLibrary (q := q) hr hrq (r * c)
  obtain ⟨C, hC, hemb⟩ := safePartialCliqueEmbedding r B (r * c)
  refine ⟨C, hC, ?_⟩
  intro n X R 𝒲 D Pk hrg hdiv hcard hG hD hCD hn hPk hPm hCq
  set I := 𝒲.filter fun W => W.Nonempty
  have hgad : ∀ W ∈ I, ∃ T Ton Toff : Finset (Finset (Fin n ⊕ Fin B)),
      GadgetWF r (r * c) (vertexSet W) T ∧
      (∀ t ∈ Ton ∪ Toff, (t ∩ univ.map Function.Embedding.inl).card ≤ r ∧
        ∀ a, Sum.inl a ∈ t → a ∈ vertexSet W) ∧
      ∀ φ, ValidPlacement (vertexSet W) φ →
        IsDecomposition q r (newEdges T φ ∪ W) (newEdges Ton φ) ∧
        IsDecomposition q r (newEdges T φ) (newEdges Toff φ) := by
    intro W hW
    rw [mem_filter] at hW
    exact exists_rootLightGadget c B hB W (hrg W hW.1) (hdiv W hW.1) (hcard W hW.1) hW.2
  choose! T Ton Toff hTw hTl hTabs using hgad
  obtain ⟨Φ, hvalid, hdisj, hhost, hdeg, hsafe⟩ := hemb n I (fun W => vertexSet W) T (X ∪ R) D q
    (packSets r Pk) hTw hG hCD
    (fun S hS => le_trans (card_le_card (filter_subset_filter _ (filter_subset _ _))) (hD S hS))
    (card_ext_packSets_le hPk hPm) hCq hn
  set A : Finset (Finset (Fin n)) → Finset (Finset (Fin n)) := fun W =>
    if W ∈ I then newEdges (T W) (Φ W) else ∅
  set Qon : Finset (Finset (Fin n)) → Finset (Finset (Fin n)) := fun W =>
    if W ∈ I then newEdges (Ton W) (Φ W) else ∅
  set Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n)) := fun W =>
    if W ∈ I then newEdges (Toff W) (Φ W) else ∅
  have hempty : IsDecomposition q r (∅ : Finset (Finset (Fin n))) ∅ :=
    ⟨fun e he => by simp at he, fun Q hQ => by simp at hQ, fun e _ => by simp [cliqueMult]⟩
  have hdec : ∀ W ∈ 𝒲, IsDecomposition q r (A W ∪ W) (Qon W) ∧
      IsDecomposition q r (A W) (Qoff W) := by
    intro W hW
    by_cases hWI : W ∈ I
    · simp only [A, Qon, Qoff, if_pos hWI]
      exact hTabs W hWI (Φ W) (hvalid W hWI)
    · have hW0 : W = ∅ := by
        by_contra h
        exact hWI (mem_filter.2 ⟨hW, nonempty_iff_ne_empty.2 h⟩)
      simp only [A, Qon, Qoff, if_neg hWI]
      rw [hW0, empty_union]
      exact ⟨hempty, hempty⟩
  refine ⟨A, Qon, Qoff, ⟨fun W hW => (hdec W hW).2.rgraph, ?_, ?_, fun W hW => (hdec W hW).1,
    fun W hW => (hdec W hW).2⟩, ?_, ?_⟩
  · intro W _
    simp only [A]
    split_ifs with hWI
    · exact hhost W hWI
    · exact disjoint_empty_left _
  · intro W hW W' hW' hne
    simp only [A]
    split_ifs with h1 h2 h2
    · exact hdisj W h1 W' h2 hne
    · exact disjoint_empty_right _
    · exact disjoint_empty_left _
    · exact disjoint_empty_left _
  · intro S hS
    have hsup : 𝒲.sup A ⊆ I.biUnion fun W => newEdges (T W) (Φ W) := by
      intro f hf
      obtain ⟨W, hW, hfW⟩ := mem_sup.1 hf
      simp only [A] at hfW
      split_ifs at hfW with hWI
      · exact mem_biUnion.2 ⟨W, hWI, hfW⟩
      · simp at hfW
    refine le_trans ?_ (hdeg S hS)
    unfold deg
    exact card_le_card (filter_subset_filter _ hsup)
  · intro W _ Q hQ P hP
    by_cases hWI : W ∈ I
    · have hQ' : Q ∈ newEdges (Ton W ∪ Toff W) (Φ W) := by
        simp only [Qon, Qoff, if_pos hWI] at hQ
        rcases mem_union.1 hQ with hQ | hQ
        · obtain ⟨t, ht, rfl⟩ := mem_image.1 hQ
          exact mem_image.2 ⟨t, mem_union_left _ ht, rfl⟩
        · obtain ⟨t, ht, rfl⟩ := mem_image.1 hQ
          exact mem_image.2 ⟨t, mem_union_right _ ht, rfl⟩
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hQ'
      obtain ⟨htl, htR⟩ := hTl W hWI t ht
      exact placeEdge_inter_le (hvalid W hWI)
        (fun S hS hsub => hsafe W hWI S hS (by simpa [auxImage] using hsub)) htl htR P hP
    · simp only [Qon, Qoff, if_neg hWI, union_empty] at hQ
      simp at hQ

end RefinedAbsorption.Pending
