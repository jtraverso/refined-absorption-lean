module
public import RequestProject.Nibble.Hyper
public import Mathlib.Algebra.Field.ZMod

/-!
# Regularising a hypergraph by layers and fibre progressions

Given a `k`-uniform (simple) hypergraph `H` on `β` with support in `Bs` and a deficit function
`d : β → ℕ`, we build a `k`-uniform hypergraph `liftE` on `β × Fin k × ZMod M`:

* for every layer `l ∈ Fin k × ZMod M`, a copy `liftReal F l` of every edge `F ∈ H`;
* for every `x ∈ Bs` and `s < d x`, `x₀ ∈ ZMod M`, the *fibre edge*
  `liftFib x s x₀ = {(x, j, x₀ + j s) : j < k}`.

Every vertex `(x, i, y)` with `x ∈ Bs` then has degree exactly `deg_H x + d x`, and two distinct
vertices have codegree at most `codeg_H` of their bases (different bases) or at most `1` (same
base), provided `M` is a prime larger than `k` and than all deficits.  Fibre edges only contain
vertices of a single base, so if `d x = 0` the vertices over `x` are covered only by copies of
edges of `H`.
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset RefinedAbsorption.Nibble

variable {β : Type*} [DecidableEq β] {k M : ℕ}

/-- The copy of `F` in the layer `l`. -/
def liftReal (F : Finset β) (l : Fin k × ZMod M) : Finset (β × Fin k × ZMod M) :=
  F.map ⟨fun x => (x, l), fun x y h => (Prod.mk.inj h).1⟩

/-- The fibre edge over `x` with step `s` and start `x₀`. -/
def liftFib [NeZero M] (x : β) (s x₀ : ZMod M) : Finset (β × Fin k × ZMod M) :=
  univ.map ⟨fun j : Fin k => (x, j, x₀ + ((j : ℕ) : ZMod M) * s), fun i j h => by
    simp only [Prod.mk.injEq] at h; exact h.2.1⟩

/-- The regularised hypergraph. -/
def liftE [NeZero M] (H : Finset (Finset β)) (Bs : Finset β) (d : β → ℕ) :
    Finset (Finset (β × Fin k × ZMod M)) :=
  (H ×ˢ (univ : Finset (Fin k × ZMod M))).image (fun p => liftReal p.1 p.2) ∪
    ((Bs ×ˢ (range M ×ˢ (univ : Finset (ZMod M)))).filter (fun p => p.2.1 < d p.1)).image
      (fun p => liftFib p.1 (p.2.1 : ZMod M) p.2.2)

theorem mem_liftReal {F : Finset β} {l : Fin k × ZMod M} {v : β × Fin k × ZMod M} :
    v ∈ liftReal F l ↔ v.1 ∈ F ∧ v.2 = l := by
  unfold liftReal
  rw [mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨hx, rfl⟩
  · rintro ⟨h1, h2⟩; exact ⟨v.1, h1, by simp [← h2]⟩

theorem mem_liftFib [NeZero M] {x : β} {s x₀ : ZMod M} {v : β × Fin k × ZMod M} :
    v ∈ liftFib x s x₀ ↔ v.1 = x ∧ v.2.2 = x₀ + ((v.2.1 : ℕ) : ZMod M) * s := by
  unfold liftFib
  rw [mem_map]
  constructor
  · rintro ⟨j, -, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨v.2.1, mem_univ _, by
      obtain ⟨a, b, c⟩ := v
      change a = x at h1
      change c = x₀ + ((b : ℕ) : ZMod M) * s at h2
      change (x, b, x₀ + ((b : ℕ) : ZMod M) * s) = (a, b, c)
      rw [h1, h2]⟩

theorem card_liftReal (F : Finset β) (l : Fin k × ZMod M) : (liftReal F l).card = F.card := by
  unfold liftReal; rw [card_map]

theorem card_liftFib [NeZero M] (x : β) (s x₀ : ZMod M) : (liftFib (k := k) x s x₀).card = k := by
  unfold liftFib; rw [card_map, card_univ, Fintype.card_fin]

theorem liftReal_injective (l : Fin k × ZMod M) :
    Function.Injective (fun F : Finset β => liftReal F l) := by
  intro F F' h
  exact Finset.map_inj.1 h

theorem liftFib_inj [NeZero M] (hk : 2 ≤ k) {x x' : β} {s s' x₀ x₀' : ZMod M}
    (h : liftFib (k := k) x s x₀ = liftFib x' s' x₀') : x = x' ∧ s = s' ∧ x₀ = x₀' := by
  have h0 : ((x, ⟨0, by omega⟩, x₀) : β × Fin k × ZMod M) ∈ liftFib x' s' x₀' := by
    rw [← h, mem_liftFib]; simp
  have h1 : ((x, ⟨1, by omega⟩, x₀ + s) : β × Fin k × ZMod M) ∈ liftFib x' s' x₀' := by
    rw [← h, mem_liftFib]; simp
  rw [mem_liftFib] at h0 h1
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul] at h0 h1
  refine ⟨h0.1, ?_, h0.2⟩
  have := h1.2
  rw [h0.2] at this
  exact add_left_cancel this

theorem natCast_inj_of_lt {a b : ℕ} (ha : a < M) (hb : b < M) (h : (a : ZMod M) = b) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem liftE_card [NeZero M] {H : Finset (Finset β)} {Bs : Finset β} {d : β → ℕ}
    (hH : ∀ F ∈ H, F.card = k) : ∀ e ∈ liftE (M := M) (k := k) H Bs d, e.card = k := by
  intro e he
  unfold liftE at he
  rcases mem_union.1 he with he | he
  · obtain ⟨p, hp, rfl⟩ := mem_image.1 he
    rw [card_liftReal]; exact hH p.1 (mem_product.1 hp).1
  · obtain ⟨p, -, rfl⟩ := mem_image.1 he
    exact card_liftFib _ _ _

theorem liftE_subset [NeZero M] {H : Finset (Finset β)} {Bs : Finset β} {d : β → ℕ}
    (hH : ∀ F ∈ H, F ⊆ Bs) :
    ∀ e ∈ liftE (M := M) (k := k) H Bs d, e ⊆ Bs ×ˢ (univ : Finset (Fin k × ZMod M)) := by
  intro e he v hv
  unfold liftE at he
  rcases mem_union.1 he with he | he
  · obtain ⟨p, hp, rfl⟩ := mem_image.1 he
    rw [mem_liftReal] at hv
    exact mem_product.2 ⟨hH p.1 (mem_product.1 hp).1 hv.1, mem_univ _⟩
  · obtain ⟨p, hp, rfl⟩ := mem_image.1 he
    rw [mem_liftFib] at hv
    rw [mem_filter, mem_product] at hp
    exact mem_product.2 ⟨hv.1 ▸ hp.1.1, mem_univ _⟩

/-- **Degrees of the regularised hypergraph.** -/
theorem liftE_star [NeZero M] (hk : 2 ≤ k) {H : Finset (Finset β)} {Bs : Finset β}
    {d : β → ℕ} (hH : ∀ F ∈ H, F.card = k) (hd : ∀ x, d x ≤ M)
    {v : β × Fin k × ZMod M} (hv : v.1 ∈ Bs) :
    (Nibble.star (liftE (M := M) H Bs d) v).card = (Nibble.star H v.1).card + d v.1 := by
  obtain ⟨x, i, y⟩ := v
  simp only at hv ⊢
  unfold Nibble.star liftE
  rw [filter_union]
  have hreal : ((H ×ˢ (univ : Finset (Fin k × ZMod M))).image
      (fun p => liftReal p.1 p.2)).filter (fun e => (x, i, y) ∈ e) =
      (H.filter (fun F => x ∈ F)).image (fun F => liftReal F (i, y)) := by
    ext e
    simp only [mem_filter, mem_image, mem_product, mem_univ, and_true]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hmem⟩
      rw [mem_liftReal] at hmem
      exact ⟨p.1, ⟨hp, hmem.1⟩, by rw [← hmem.2]⟩
    · rintro ⟨F, ⟨hF, hx⟩, rfl⟩
      exact ⟨⟨(F, (i, y)), hF, rfl⟩, mem_liftReal.2 ⟨hx, rfl⟩⟩
  have hfib : (((Bs ×ˢ (range M ×ˢ (univ : Finset (ZMod M)))).filter
      (fun p => p.2.1 < d p.1)).image (fun p => liftFib p.1 (p.2.1 : ZMod M) p.2.2)).filter
      (fun e => (x, i, y) ∈ e) =
      (range (d x)).image (fun s : ℕ => liftFib (k := k) x (s : ZMod M) (y - ((i : ℕ) : ZMod M) * s))
      := by
    ext e
    simp only [mem_filter, mem_image, mem_product, mem_range, mem_univ, and_true]
    constructor
    · rintro ⟨⟨p, ⟨⟨hp1, hp2⟩, hp3⟩, rfl⟩, hmem⟩
      rw [mem_liftFib] at hmem
      simp only at hmem
      obtain ⟨h1, h2⟩ := hmem
      subst h1
      refine ⟨p.2.1, hp3, ?_⟩
      rw [h2]; congr 1; ring
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨(x, s, y - ((i : ℕ) : ZMod M) * s), ⟨⟨hv, lt_of_lt_of_le hs (hd x)⟩, hs⟩, rfl⟩, ?_⟩
      rw [mem_liftFib]; simp
  rw [hreal, hfib, card_union_of_disjoint]
  · rw [card_image_of_injective _ (liftReal_injective _), card_image_of_injOn]
    · rw [card_range]
    · intro s hs s' hs' h
      have h' := (liftFib_inj hk h).2.1
      exact natCast_inj_of_lt (lt_of_lt_of_le (mem_range.1 hs) (hd x))
        (lt_of_lt_of_le (mem_range.1 hs') (hd x)) h'
  · rw [disjoint_left]
    intro e he he'
    obtain ⟨F, hF, rfl⟩ := mem_image.1 he
    obtain ⟨s, -, hs⟩ := mem_image.1 he'
    rw [mem_filter] at hF
    have hFk := hH F hF.1
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (show 1 < F.card by omega)
    have h1 : ((a, i, y) : β × Fin k × ZMod M) ∈ liftReal F (i, y) := mem_liftReal.2 ⟨ha, rfl⟩
    have h2 : ((b, i, y) : β × Fin k × ZMod M) ∈ liftReal F (i, y) := mem_liftReal.2 ⟨hb, rfl⟩
    rw [← hs, mem_liftFib] at h1 h2
    exact hab (h1.1.trans h2.1.symm)

/-- **Codegrees of the regularised hypergraph.** -/
theorem liftE_codeg [Fact M.Prime] (hkM : k < M) {H : Finset (Finset β)} {Bs : Finset β}
    {d : β → ℕ} (hd : ∀ x, d x ≤ M) {u v : β × Fin k × ZMod M} (huv : u ≠ v) :
    codeg (liftE (M := M) H Bs d) u v ≤ if u.1 = v.1 then 1 else codeg H u.1 v.1 := by
  obtain ⟨x, i, y⟩ := u
  obtain ⟨x', i', y'⟩ := v
  simp only
  unfold codeg liftE
  rw [filter_union]
  refine (card_union_le _ _).trans ?_
  by_cases hxx : x = x'
  · subst hxx
    rw [if_pos rfl]
    have h1 : ((H ×ˢ (univ : Finset (Fin k × ZMod M))).image
        (fun p => liftReal p.1 p.2)).filter (fun e => (x, i, y) ∈ e ∧ (x, i', y') ∈ e) = ∅ := by
      rw [filter_eq_empty_iff]
      intro e he ⟨h1, h2⟩
      obtain ⟨p, -, rfl⟩ := mem_image.1 he
      rw [mem_liftReal] at h1 h2
      simp only at h1 h2
      apply huv
      rw [show (i, y) = (i', y') from h1.2.trans h2.2.symm]
    rw [h1, card_empty, zero_add]
    refine card_le_one.2 fun e he e' he' => ?_
    rw [mem_filter] at he he'
    obtain ⟨hu, hv⟩ := he.2
    obtain ⟨hu', hv'⟩ := he'.2
    obtain ⟨p, hp, rfl⟩ := mem_image.1 he.1
    obtain ⟨p', hp', rfl⟩ := mem_image.1 he'.1
    rw [mem_liftFib] at hu hv hu' hv'
    simp only at hu hv hu' hv'
    have hii : i ≠ i' := by
      intro hii
      subst hii
      apply huv
      rw [hu.2, hv.2]
    have hne : ((i : ℕ) : ZMod M) - ((i' : ℕ) : ZMod M) ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      exact hii (Fin.ext (natCast_inj_of_lt (lt_trans i.2 hkM) (lt_trans i'.2 hkM) h0))
    have hs : (p.2.1 : ZMod M) = (p'.2.1 : ZMod M) := by
      have e1 : (((i : ℕ) : ZMod M) - ((i' : ℕ) : ZMod M)) * (p.2.1 : ZMod M) = y - y' := by
        rw [hu.2, hv.2]; ring
      have e2 : (((i : ℕ) : ZMod M) - ((i' : ℕ) : ZMod M)) * (p'.2.1 : ZMod M) = y - y' := by
        rw [hu'.2, hv'.2]; ring
      exact mul_left_cancel₀ hne (e1.trans e2.symm)
    have hx0 : p.2.2 = p'.2.2 := by
      have := hu.2.symm.trans hu'.2
      rw [hs] at this
      exact add_right_cancel this
    rw [← hu.1, ← hu'.1, hs, hx0]
  · rw [if_neg hxx]
    have h2 : (((Bs ×ˢ (range M ×ˢ (univ : Finset (ZMod M)))).filter
        (fun p => p.2.1 < d p.1)).image (fun p => liftFib p.1 (p.2.1 : ZMod M) p.2.2)).filter
        (fun e => (x, i, y) ∈ e ∧ (x', i', y') ∈ e) = ∅ := by
      rw [filter_eq_empty_iff]
      intro e he ⟨h1, h2⟩
      obtain ⟨p, -, rfl⟩ := mem_image.1 he
      rw [mem_liftFib] at h1 h2
      exact hxx (h1.1.trans h2.1.symm)
    rw [h2, card_empty, add_zero]
    have hsub : ((H ×ˢ (univ : Finset (Fin k × ZMod M))).image
        (fun p => liftReal p.1 p.2)).filter (fun e => (x, i, y) ∈ e ∧ (x', i', y') ∈ e) ⊆
        (H.filter (fun F => x ∈ F ∧ x' ∈ F)).image (fun F => liftReal F (i, y)) := by
      intro e he
      rw [mem_filter] at he
      obtain ⟨h1, h2⟩ := he.2
      obtain ⟨p, hp, rfl⟩ := mem_image.1 he.1
      rw [mem_liftReal] at h1 h2
      exact mem_image.2 ⟨p.1, mem_filter.2 ⟨(mem_product.1 hp).1, h1.1, h2.1⟩, by rw [← h1.2]⟩
    exact (card_le_card hsub).trans card_image_le

end RefinedAbsorption.Pending
