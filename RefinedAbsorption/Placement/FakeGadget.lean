module
public import RefinedAbsorption.Placement.PlacedDeg
public import RefinedAbsorption.MultiRefiner.Reduction
public import RefinedAbsorption.Absorber17.Library

/-!
# Fake edges as gadgets

The fake edge of an `r`-set `e ⊆ Fin n` (`m = N - 1` anti-edges on `e` with `q - r` new vertices
each, see `RefinedAbsorption.MultiRefiner.fakeEdge`) is a gadget with roots `e` and
`h_f = m (q - r)` auxiliary vertices (`fakeTemplate`).  Every valid placement of it inside `Fin n`
is an `r`-graph whose degrees satisfy, modulo `binom(q - |S|, r - |S|)`,
`deg(S) ≡ [S ⊆ e]` for all `|S| < r` (`deg_placedFake_cast`): a placed fake edge behaves like the
single edge `e` for `K_q^r`-divisibility, even though different placed fake edges may share
vertices.
-/

@[expose] public section

namespace RefinedAbsorption.Placement

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Absorber17

/-- The number of auxiliary vertices of a fake edge. -/
def fakeAux (q r : ℕ) : ℕ := fakeCount q r * (q - r)

/-- Relabelling the new vertices of a single fake edge by `Fin (fakeAux q r)`. -/
def fakeAuxEquiv (q r : ℕ) : Unit × Fin (fakeCount q r) × Fin (q - r) ≃ Fin (fakeAux q r) :=
  (Equiv.uniqueProd _ Unit).trans finProdFinEquiv

/-- The vertex relabelling `XV (Fin n) Unit q r ≃ Fin n ⊕ Fin (fakeAux q r)`. -/
def fakeVEquiv (n q r : ℕ) : XV (Fin n) Unit q r ≃ Fin n ⊕ Fin (fakeAux q r) :=
  Equiv.sumCongr (Equiv.refl _) (fakeAuxEquiv q r)

/-- **The fake-edge gadget** of the `r`-set `e`. -/
def fakeTemplate (q r : ℕ) {n : ℕ} (e : Finset (Fin n)) :
    Finset (Finset (Fin n ⊕ Fin (fakeAux q r))) :=
  RefinedAbsorption.gmap (fakeVEquiv n q r).toEmbedding (fakeEdge q r (fun _ : Unit => e) ())

theorem fakeVEquiv_inl {n q r : ℕ} (a : Fin n) :
    (fakeVEquiv n q r).toEmbedding (Sum.inl a) = Sum.inl a := rfl

theorem fakeVEquiv_inr {n q r : ℕ} (x : Unit × Fin (fakeCount q r) × Fin (q - r)) :
    (fakeVEquiv n q r).toEmbedding (Sum.inr x) = Sum.inr (fakeAuxEquiv q r x) := rfl

theorem fakeTemplate_wf {q r n : ℕ} {e : Finset (Fin n)} (he : e.card = r) :
    GadgetWF r r e (fakeTemplate q r e) where
  roots_le := he.le
  roots_ge := by omega
  edge_card := by
    intro t ht
    obtain ⟨f, hf, rfl⟩ := mem_gmap.1 ht
    rw [card_map]; exact fakeEdge_card_edge hf
  edge_roots := by
    intro t ht a ha
    obtain ⟨f, hf, rfl⟩ := mem_gmap.1 ht
    obtain ⟨y, hy, hya⟩ := mem_map.1 ha
    rcases y with b | x
    · rw [fakeVEquiv_inl] at hya
      cases hya
      exact fakeEdge_inl (ends := fun _ : Unit => e) hf hy
    · rw [fakeVEquiv_inr] at hya; cases hya
  edge_aux := by
    intro t ht
    obtain ⟨f, hf, rfl⟩ := mem_gmap.1 ht
    obtain ⟨j, s, hjs⟩ := fakeEdge_exists_fresh (ends := fun _ : Unit => e) he hf
    exact ⟨fakeAuxEquiv q r ((), j, s), mem_map.2 ⟨_, hjs, rfl⟩⟩

theorem card_fakeTemplate_le {q r n : ℕ} (hrq : r ≤ q) {e : Finset (Fin n)} (he : e.card = r) :
    (fakeTemplate q r e).card ≤ fakeCount q r * q.choose r := by
  rw [fakeTemplate, card_gmap]
  exact card_fakeEdge_le (ends := fun _ : Unit => e) hrq he

/-- The fake-edge template behaves like the edge `e` modulo divisibility. -/
theorem deg_fakeTemplate_cast {q r n : ℕ} (hrq : r ≤ q) {e : Finset (Fin n)} (he : e.card = r)
    (S'' : Finset (Fin n ⊕ Fin (fakeAux q r))) (hS : S''.card < r) :
    ((deg (fakeTemplate q r e) S'' : ℕ) : ZMod ((q - S''.card).choose (r - S''.card))) =
      if S'' ⊆ e.map Function.Embedding.inl then 1 else 0 := by
  set κ := (fakeVEquiv n q r).toEmbedding
  set S := S''.map (fakeVEquiv n q r).symm.toEmbedding
  have hSS : S.map κ = S'' := by
    ext x; simp [S, κ]
  have hcard : S.card = S''.card := card_map _
  rw [← hSS, fakeTemplate, deg_gmap_map, card_map]
  have := fakeEdge_deg_cast (ends := fun _ : Unit => e) (i := ()) hrq he (S := S)
    (by rw [hcard]; exact hS)
  rw [this]
  congr 1
  apply propext
  rw [lift, ← map_subset_map (f := κ)]
  have : (e.map Function.Embedding.inl).map κ = e.map Function.Embedding.inl := by
    ext x
    simp only [mem_map]
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨Sum.inl a, ⟨a, ha, rfl⟩, rfl⟩
  rw [this]

/-- **A placed fake edge behaves like its root edge** modulo divisibility. -/
theorem deg_placedFake_cast {q r n : ℕ} (hrq : r ≤ q) {e : Finset (Fin n)} (he : e.card = r)
    {φ : Fin (fakeAux q r) → Fin n} (hφ : ValidPlacement e φ) (S : Finset (Fin n))
    (hS : S.card < r) :
    ((deg (newEdges (fakeTemplate q r e) φ) S : ℕ) :
        ZMod ((q - S.card).choose (r - S.card))) = if S ⊆ e then 1 else 0 := by
  apply deg_newEdges_cast (fakeTemplate_wf he) hφ S
  intro S'' hS''
  rw [← hS'']
  exact deg_fakeTemplate_cast hrq he S'' (hS'' ▸ hS)

end RefinedAbsorption.Placement
