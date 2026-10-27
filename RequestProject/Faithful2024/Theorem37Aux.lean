module
public import RequestProject.Faithful2024.MultiGadget

/-!
# Auxiliary facts for the proof of Theorem 3.7 (arXiv:2402.17855v1)

* `injOn_emb`: a valid placement is injective on the roots together with the auxiliary vertices;
* `image_inj_of_injOn`: images of subsets of a set on which a map is injective determine the
  subsets;
* `isCliqueCopy_image`: transport of a labelled `K_q^r`-copy along a vertex map that is injective
  on its vertices and an injective relabelling.
-/

@[expose] public section

namespace RefinedAbsorption.Faithful2024

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Placement

/-- The vertices of a gadget with roots `R`: roots and auxiliary vertices. -/
def gadgetVerts {n h : ℕ} (R : Finset (Fin n)) : Set (Fin n ⊕ Fin h) :=
  {x | ∀ a, x = Sum.inl a → a ∈ R}

theorem injOn_emb {n h : ℕ} {R : Finset (Fin n)} {φ : Fin h → Fin n} (hφ : ValidPlacement R φ) :
    Set.InjOn (emb φ) (gadgetVerts R) := by
  intro x hx y hy hxy
  rcases x with a | p <;> rcases y with b | p'
  · exact congrArg Sum.inl hxy
  · exact absurd (hx a rfl) (by rw [show a = φ p' from hxy]; exact hφ.2 p')
  · exact absurd (hy b rfl) (by rw [show b = φ p from hxy.symm]; exact hφ.2 p)
  · exact congrArg Sum.inr (hφ.1 hxy)

theorem image_inj_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β} {G : Set α}
    (hf : Set.InjOn f G) {s t : Finset α} (hs : (s : Set α) ⊆ G) (ht : (t : Set α) ⊆ G)
    (hst : s.image f = t.image f) : s = t := by
  have key : ∀ {s t : Finset α}, (s : Set α) ⊆ G → (t : Set α) ⊆ G → s.image f = t.image f →
      s ⊆ t := by
    intro s t hs ht hst x hx
    have : f x ∈ t.image f := hst ▸ mem_image_of_mem f hx
    obtain ⟨y, hy, hyx⟩ := mem_image.1 this
    rw [hf (ht hy) (hs hx) hyx] at hy
    exact hy
  exact Subset.antisymm (key hs ht hst) (key ht hs hst.symm)

theorem powersetCard_image_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    {Q : Finset α} (hf : Set.InjOn f Q) (r : ℕ) :
    (Q.powersetCard r).image (image f) = (Q.image f).powersetCard r := by
  ext u
  simp only [mem_image, mem_powersetCard]
  constructor
  · rintro ⟨s, ⟨hsQ, hsr⟩, rfl⟩
    refine ⟨image_subset_image hsQ, ?_⟩
    rw [card_image_of_injOn (hf.mono (by exact_mod_cast hsQ)), hsr]
  · rintro ⟨huQ, hur⟩
    refine ⟨Q.filter fun a => f a ∈ u, ⟨filter_subset _ _, ?_⟩, ?_⟩
    · have himg : (Q.filter fun a => f a ∈ u).image f = u := by
        ext b
        simp only [mem_image, mem_filter]
        constructor
        · rintro ⟨a, ⟨-, hb⟩, rfl⟩; exact hb
        · intro hb
          obtain ⟨a, ha, rfl⟩ := mem_image.1 (huQ hb)
          exact ⟨a, ⟨ha, hb⟩, rfl⟩
      calc (Q.filter fun a => f a ∈ u).card = ((Q.filter fun a => f a ∈ u).image f).card :=
            (card_image_of_injOn (hf.mono (by intro a ha; exact (mem_filter.1 ha).1))).symm
        _ = r := by rw [himg, hur]
    · ext b
      simp only [mem_image, mem_filter]
      constructor
      · rintro ⟨a, ⟨-, hb⟩, rfl⟩; exact hb
      · intro hb
        obtain ⟨a, ha, rfl⟩ := mem_image.1 (huQ hb)
        exact ⟨a, ⟨ha, hb⟩, rfl⟩

/-- **Transport of a labelled `K_q^r`-copy.** -/
theorem isCliqueCopy_image {q r : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q) {α β L L' : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq L] [DecidableEq L'] {f : α → β} {G : Set α}
    (hf : Set.InjOn f G) {ends : L → Finset α} {ends' : L' → Finset β} {ℓ : L → L'}
    {K : Finset L} (hK : IsCliqueCopy q r ends K)
    (hG : ∀ k ∈ K, (ends k : Set α) ⊆ G) (hcomp : ∀ k ∈ K, ends' (ℓ k) = (ends k).image f) :
    IsCliqueCopy q r ends' (K.image ℓ) := by
  obtain ⟨Q, hQ, hinj, himg⟩ := hK
  have hQG : (Q : Set α) ⊆ G := by
    intro x hx
    obtain ⟨u, hxu, huQ, hu⟩ := exists_subsuperset_card_eq (s := {x}) (t := Q) (n := r)
      (singleton_subset_iff.2 hx) (by simpa using hr) (by omega)
    have : u ∈ K.image ends := himg ▸ mem_powersetCard.2 ⟨huQ, hu⟩
    obtain ⟨k, hk, rfl⟩ := mem_image.1 this
    exact hG k hk (by simpa using hxu)
  refine ⟨Q.image f, by rw [card_image_of_injOn (hf.mono hQG), hQ], ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨k, hk, rfl⟩ := mem_image.1 (mem_coe.1 ha)
    obtain ⟨k', hk', rfl⟩ := mem_image.1 (mem_coe.1 hb)
    simp only [hcomp k hk, hcomp k' hk'] at hab
    exact congrArg ℓ (hinj hk hk' (image_inj_of_injOn hf (hG k hk) (hG k' hk') hab))
  · rw [image_image, ← powersetCard_image_of_injOn (hf.mono hQG), ← himg, image_image]
    exact image_congr fun k hk => hcomp k hk

end RefinedAbsorption.Faithful2024
