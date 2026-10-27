module
public import RefinedAbsorption.Local.Chernoff
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Random affine relabellings and the spreading of set systems

Mathematics: the random embedding step of the Refine Down Lemma (M. Delcourt and L. Postle,
arXiv:2402.17855, proof of Lemma 4.1: every local refiner is moved by an independent random
permutation of the new vertices, and the Chernoff bound with the union bound gives a choice for
which all codegrees are small).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

Instead of uniformly random permutations of the set of new vertices we use uniformly random
*affine* maps `z ↦ a z + t` of `ZMod p` (`p` prime), transported to a copy `emb : ZMod p ↪ V` of
`ZMod p` inside the vertex type and extended by the identity (`affMap`).  The affine group is
sharply `2`-transitive, which is all the computation of expectations needs:

* `card_aff_eq_le`: a point is sent to a given point by at most `p - 1` of the `p (p - 1)` maps;
* `card_aff_eq₂_le`: two distinct points are sent to two given points by at most one map.

**`exists_affine_spread`** (the probabilistic core of Lemma 4.1).  Let `A v k` (`v : ι`,
`k : κ v`) be finite set systems inside a finite set `Q ⊇ range emb`, with sets of size `≤ s`,
vertex degrees `≤ Δ` and pair codegrees `≤ μ`.  Then there are
affine maps `g v`, one for each system, such that after moving the system `v` by `g v`, every pair
`{x, y}` with `y ∈ range emb` lies in fewer than

`(e - 1) |ι| (s Δ / p + s Δ / (p - 1)) + μ log (|Q|² + 1)`

of the moved sets altogether.
-/

@[expose] public section

namespace RefinedAbsorption.Local

open Finset

variable {V : Type*} [DecidableEq V] {p : ℕ} [hp : Fact p.Prime]

/-- The affine group of `ZMod p`, as pairs `(a, t)` acting by `z ↦ a z + t`. -/
abbrev AffG (p : ℕ) := (ZMod p)ˣ × ZMod p

open Classical in
/-- The affine map `g` transported along `emb` and extended by the identity. -/
noncomputable def affMap (emb : ZMod p ↪ V) (g : AffG p) (x : V) : V :=
  if h : ∃ z, emb z = x then emb ((g.1 : ZMod p) * h.choose + g.2) else x

theorem affMap_emb (emb : ZMod p ↪ V) (g : AffG p) (z : ZMod p) :
    affMap emb g (emb z) = emb ((g.1 : ZMod p) * z + g.2) := by
  have h : ∃ z', emb z' = emb z := ⟨z, rfl⟩
  unfold affMap
  rw [dif_pos h]
  congr 3
  exact emb.injective h.choose_spec

theorem affMap_of_not (emb : ZMod p ↪ V) (g : AffG p) {x : V} (hx : ¬ ∃ z, emb z = x) :
    affMap emb g x = x := by
  unfold affMap; rw [dif_neg hx]

theorem affMap_injective (emb : ZMod p ↪ V) (g : AffG p) : Function.Injective (affMap emb g) := by
  intro x y hxy
  by_cases hx : ∃ z, emb z = x <;> by_cases hy : ∃ z, emb z = y
  · obtain ⟨z, rfl⟩ := hx; obtain ⟨w, rfl⟩ := hy
    rw [affMap_emb, affMap_emb] at hxy
    have := emb.injective hxy
    have hu : (g.1 : ZMod p) ≠ 0 := g.1.ne_zero
    have : (g.1 : ZMod p) * z = g.1 * w := by linear_combination this
    rw [mul_right_inj' hu] at this
    rw [this]
  · obtain ⟨z, rfl⟩ := hx
    rw [affMap_emb, affMap_of_not emb g hy] at hxy
    exact absurd ⟨_, hxy⟩ hy
  · obtain ⟨w, rfl⟩ := hy
    rw [affMap_emb, affMap_of_not emb g hx] at hxy
    exact absurd ⟨_, hxy.symm⟩ hx
  · rwa [affMap_of_not emb g hx, affMap_of_not emb g hy] at hxy

theorem affMap_surjective (emb : ZMod p ↪ V) (g : AffG p) :
    Function.Surjective (affMap emb g) := by
  intro x
  by_cases hx : ∃ z, emb z = x
  · obtain ⟨w, rfl⟩ := hx
    refine ⟨emb ((g.1⁻¹ : (ZMod p)ˣ) * (w - g.2)), ?_⟩
    rw [affMap_emb]
    congr 1
    have : (g.1 : ZMod p) * ((g.1⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := Units.mul_inv g.1
    linear_combination (w - g.2) * this
  · exact ⟨x, affMap_of_not emb g hx⟩

theorem affMap_mem_range_iff (emb : ZMod p ↪ V) (g : AffG p) (x : V) :
    (∃ z, emb z = affMap emb g x) ↔ ∃ z, emb z = x := by
  constructor
  · rintro ⟨z, hz⟩
    by_contra hx
    rw [affMap_of_not emb g hx] at hz
    exact hx ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, (affMap_emb emb g z).symm⟩

/-! ### Sharp `2`-transitivity -/

theorem card_aff_eq_le (z w : ZMod p) :
    (univ.filter fun g : AffG p => (g.1 : ZMod p) * z + g.2 = w).card ≤ p - 1 := by
  have hc : Fintype.card (ZMod p)ˣ = p - 1 := by rw [Fintype.card_units, ZMod.card]
  rw [← hc, ← card_univ]
  refine card_le_card_of_injOn Prod.fst (fun _ _ => mem_coe.2 (mem_univ _)) ?_
  intro g hg h hh e
  simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hg hh
  refine Prod.ext e ?_
  have : (g.1 : ZMod p) = h.1 := by rw [e]
  rw [this] at hg
  linear_combination hg - hh

theorem card_aff_eq₂_le {z z' : ZMod p} (hz : z ≠ z') (w w' : ZMod p) :
    (univ.filter fun g : AffG p =>
      (g.1 : ZMod p) * z + g.2 = w ∧ (g.1 : ZMod p) * z' + g.2 = w').card ≤ 1 := by
  refine card_le_one.2 fun g hg h hh => ?_
  simp only [mem_filter, mem_univ, true_and] at hg hh
  have hzz : z - z' ≠ 0 := sub_ne_zero.2 hz
  have e1 : ((g.1 : ZMod p) - h.1) * (z - z') = 0 := by
    linear_combination hg.1 - hg.2 - hh.1 + hh.2
  have e2 : (g.1 : ZMod p) = h.1 := by
    rcases mul_eq_zero.1 e1 with h' | h'
    · exact sub_eq_zero.1 h'
    · exact absurd h' hzz
  refine Prod.ext (Units.ext e2) ?_
  rw [e2] at hg
  linear_combination hg.1 - hh.1

/-! ### Expected codegrees of one moved set -/

/-- Pairs with exactly one point in the copy of `ZMod p`. -/
theorem card_aff_pair_one_le (emb : ZMod p ↪ V) (A : Finset V) {x : V} (hx : ¬ ∃ z, emb z = x)
    (w : ZMod p) :
    (univ.filter fun g : AffG p =>
      x ∈ A.image (affMap emb g) ∧ emb w ∈ A.image (affMap emb g)).card ≤
      (if x ∈ A then A.card * (p - 1) else 0) := by
  split_ifs with hxA
  · refine (card_le_card ?_).trans ((card_biUnion_le (s := A)
      (t := fun a => univ.filter fun g : AffG p => affMap emb g a = emb w)).trans ?_)
    · intro g hg
      simp only [mem_filter, mem_univ, true_and, mem_image] at hg
      obtain ⟨-, a, ha, hga⟩ := hg
      exact mem_biUnion.2 ⟨a, ha, mem_filter.2 ⟨mem_univ _, hga⟩⟩
    · refine (sum_le_sum fun a _ => ?_).trans (by rw [sum_const, smul_eq_mul])
      by_cases ha : ∃ z, emb z = a
      · obtain ⟨z, rfl⟩ := ha
        refine le_trans (card_le_card fun g hg => ?_) (card_aff_eq_le z w)
        simp only [mem_filter, mem_univ, true_and, affMap_emb] at hg ⊢
        exact emb.injective hg
      · refine le_of_eq_of_le (card_eq_zero.2 (filter_eq_empty_iff.2 fun g _ hg => ?_))
          (Nat.zero_le _)
        rw [affMap_of_not emb g ha] at hg
        exact ha ⟨w, hg.symm⟩
  · refine le_of_eq (card_eq_zero.2 (filter_eq_empty_iff.2 fun g _ hg => ?_))
    obtain ⟨a, ha, hga⟩ := mem_image.1 hg.1
    by_cases ha' : ∃ z, emb z = a
    · exact hx ((affMap_mem_range_iff emb g a).2 ha' |>.elim fun z hz => ⟨z, hz.trans hga⟩)
    · rw [affMap_of_not emb g ha'] at hga
      exact hxA (hga ▸ ha)

/-- Pairs inside the copy of `ZMod p`. -/
theorem card_aff_pair_two_le (emb : ZMod p ↪ V) (A : Finset V) {w w' : ZMod p} (hw : w ≠ w') :
    (univ.filter fun g : AffG p =>
      emb w ∈ A.image (affMap emb g) ∧ emb w' ∈ A.image (affMap emb g)).card ≤
      (A.filter fun a => ∃ z, emb z = a).card ^ 2 := by
  refine (card_le_card ?_).trans ((card_biUnion_le
    (s := (A.filter fun a => ∃ z, emb z = a) ×ˢ (A.filter fun a => ∃ z, emb z = a))
    (t := fun aa => univ.filter fun g : AffG p =>
      affMap emb g aa.1 = emb w ∧ affMap emb g aa.2 = emb w')).trans ?_)
  · intro g hg
    simp only [mem_filter, mem_univ, true_and, mem_image] at hg
    obtain ⟨⟨a, ha, hga⟩, a', ha', hga'⟩ := hg
    have hra : ∃ z, emb z = a := (affMap_mem_range_iff emb g a).1 ⟨w, hga.symm⟩
    have hra' : ∃ z, emb z = a' := (affMap_mem_range_iff emb g a').1 ⟨w', hga'.symm⟩
    exact mem_biUnion.2 ⟨(a, a'), mem_product.2 ⟨mem_filter.2 ⟨ha, hra⟩, mem_filter.2 ⟨ha', hra'⟩⟩,
      mem_filter.2 ⟨mem_univ _, hga, hga'⟩⟩
  · refine (sum_le_sum fun aa _ => ?_).trans (by rw [sum_const, smul_eq_mul, card_product, sq,
      mul_one])
    by_cases ha : ∃ z, emb z = aa.1 <;> by_cases ha' : ∃ z, emb z = aa.2
    · obtain ⟨z, hz⟩ := ha; obtain ⟨z', hz'⟩ := ha'
      by_cases hzz : z = z'
      · refine le_of_eq_of_le (card_eq_zero.2 (filter_eq_empty_iff.2 fun g _ hg => ?_))
          (Nat.zero_le _)
        rw [← hz, ← hz', hzz] at hg
        exact hw (emb.injective (hg.1.symm.trans hg.2))
      · refine le_trans (card_le_card fun g hg => ?_) (card_aff_eq₂_le hzz w w')
        simp only [mem_filter, mem_univ, true_and, ← hz, ← hz', affMap_emb] at hg ⊢
        exact ⟨emb.injective hg.1, emb.injective hg.2⟩
    all_goals
      refine le_of_eq_of_le (card_eq_zero.2 (filter_eq_empty_iff.2 fun g _ hg => ?_))
        (Nat.zero_le _)
    · rw [affMap_of_not emb g ha'] at hg; exact ha' ⟨w', hg.2.symm⟩
    · rw [affMap_of_not emb g ha] at hg; exact ha ⟨w, hg.1.symm⟩
    · rw [affMap_of_not emb g ha] at hg; exact ha ⟨w, hg.1.symm⟩

theorem mem_image_iff_of_injective {f : V → V} (hf : Function.Injective f) {s : Finset V}
    {a : V} : f a ∈ s.image f ↔ a ∈ s := by
  constructor
  · intro h; obtain ⟨b, hb, e⟩ := mem_image.1 h; exact hf e ▸ hb
  · intro h; exact mem_image_of_mem f h

/-- Moving by a bijection does not change the codegree of a pair (of its preimages). -/
theorem card_moved_pair_le (emb : ZMod p ↪ V) (g : AffG p) {κ : Type*} [Fintype κ]
    (A : κ → Finset V) {μ : ℕ}
    (hcodeg : ∀ x y, x ≠ y → (univ.filter fun k => x ∈ A k ∧ y ∈ A k).card ≤ μ)
    {x y : V} (hxy : x ≠ y) :
    (univ.filter fun k => x ∈ (A k).image (affMap emb g) ∧
      y ∈ (A k).image (affMap emb g)).card ≤ μ := by
  obtain ⟨x', rfl⟩ := affMap_surjective emb g x
  obtain ⟨y', rfl⟩ := affMap_surjective emb g y
  have hinj := affMap_injective emb g
  refine le_trans (le_of_eq ?_) (hcodeg x' y' fun h => hxy (h ▸ rfl))
  congr 1
  refine filter_congr fun k _ => ?_
  rw [mem_image_iff_of_injective hinj, mem_image_iff_of_injective hinj]

/-! ### The spreading lemma -/

section Spread

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ v, Fintype (κ v)]

theorem sum_card_filter_swap {α β : Type*} [Fintype α] [Fintype β] (P : α → β → Prop)
    [∀ a b, Decidable (P a b)] :
    ∑ b, (univ.filter fun a => P a b).card = ∑ a, (univ.filter fun b => P a b).card := by
  simp only [card_filter]; exact sum_comm

theorem card_affG : Fintype.card (AffG p) = (p - 1) * p := by
  rw [Fintype.card_prod, Fintype.card_units, ZMod.card]

/-- The moved load of the pair `(x, y)` in the system `v` after the map `g`. -/
noncomputable def movedLoad (emb : ZMod p ↪ V) (A : ∀ v, κ v → Finset V) (x y : V) (v : ι)
    (g : AffG p) : ℕ :=
  (univ.filter fun k => x ∈ (A v k).image (affMap emb g) ∧ y ∈ (A v k).image (affMap emb g)).card

omit [Fintype ι] [DecidableEq ι] in
/-- The total over all maps of the moved load, in the two cases. -/
theorem sum_movedLoad_le (emb : ZMod p ↪ V) (A : ∀ v, κ v → Finset V) {s Δ : ℕ}
    (hs : ∀ v k, (A v k).card ≤ s) (hdeg : ∀ v x, (univ.filter fun k => x ∈ A v k).card ≤ Δ)
    (v : ι) {x : V} {w : ZMod p} (hxw : x ≠ emb w) :
    (∑ g, movedLoad emb A x (emb w) v g : ℕ) ≤ Δ * s * (p - 1) + s * p * Δ := by
  unfold movedLoad
  rw [sum_card_filter_swap (fun k g => x ∈ (A v k).image (affMap emb g) ∧
    emb w ∈ (A v k).image (affMap emb g))]
  by_cases hx : ∃ z, emb z = x
  · obtain ⟨w', rfl⟩ := hx
    have hww : w' ≠ w := fun h => hxw (h ▸ rfl)
    refine le_trans ?_ (Nat.le_add_left _ _)
    calc ∑ k, (univ.filter fun g : AffG p => emb w' ∈ (A v k).image (affMap emb g) ∧
          emb w ∈ (A v k).image (affMap emb g)).card
        ≤ ∑ k, s * ((A v k).filter fun a => ∃ z, emb z = a).card := sum_le_sum fun k _ => by
          refine (card_aff_pair_two_le emb (A v k) hww).trans ?_
          rw [sq]
          exact Nat.mul_le_mul_right _ ((card_filter_le _ _).trans (hs v k))
      _ = s * ∑ z : ZMod p, (univ.filter fun k => emb z ∈ A v k).card := by
          rw [← mul_sum]
          congr 1
          rw [sum_card_filter_swap (fun k (z : ZMod p) => emb z ∈ A v k)]
          refine sum_congr rfl fun k _ => ?_
          rw [← card_map emb]
          congr 1
          ext a
          simp only [mem_map, mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨ha, z, rfl⟩; exact ⟨z, ha, rfl⟩
          · rintro ⟨z, hz, rfl⟩; exact ⟨hz, z, rfl⟩
      _ ≤ s * (p * Δ) := by
          refine Nat.mul_le_mul_left _ ((sum_le_sum fun z _ => hdeg v (emb z)).trans ?_)
          rw [sum_const, card_univ, ZMod.card, smul_eq_mul]
      _ = s * p * Δ := by ring
  · refine le_trans ?_ (Nat.le_add_right _ _)
    calc ∑ k, (univ.filter fun g : AffG p => x ∈ (A v k).image (affMap emb g) ∧
          emb w ∈ (A v k).image (affMap emb g)).card
        ≤ ∑ k, (if x ∈ A v k then s * (p - 1) else 0) := sum_le_sum fun k _ => by
          refine (card_aff_pair_one_le emb (A v k) hx w).trans ?_
          split_ifs
          · exact Nat.mul_le_mul_right _ (hs v k)
          · exact le_rfl
      _ = (univ.filter fun k => x ∈ A v k).card * (s * (p - 1)) := by
          rw [← sum_filter, sum_const, smul_eq_mul]
      _ ≤ Δ * s * (p - 1) := by
          rw [mul_assoc]; exact Nat.mul_le_mul_right _ (hdeg v x)

/-- **Spreading lemma (random embedding, Lemma 4.1).** -/
theorem exists_affine_spread (emb : ZMod p ↪ V) (A : ∀ v, κ v → Finset V) (Q : Finset V)
    {s Δ μ : ℕ} (hQ : ∀ z, emb z ∈ Q) (hAQ : ∀ v k, A v k ⊆ Q)
    (hs : ∀ v k, (A v k).card ≤ s) (hdeg : ∀ v x, (univ.filter fun k => x ∈ A v k).card ≤ Δ)
    (hcodeg : ∀ v x y, x ≠ y → (univ.filter fun k => x ∈ A v k ∧ y ∈ A v k).card ≤ μ)
    (hμ : 1 ≤ μ) :
    ∃ g : ι → AffG p, ∀ x y : V, x ≠ y → (∃ w, emb w = y) →
      ((∑ v, movedLoad emb A x y v (g v) : ℕ) : ℝ) <
        (Real.exp 1 - 1) * Fintype.card ι *
          ((Δ * s * (p - 1) + s * p * Δ : ℕ) / ((p - 1 : ℕ) * p : ℝ)) +
          μ * Real.log (Q.card ^ 2 + 1) := by
  classical
  have hp2 : 2 ≤ p := hp.out.two_le
  set G : ℝ := ((p - 1 : ℕ) * p : ℝ) with hGdef
  have hGpos : 0 < G := by
    have : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (by omega : 0 < p - 1)
    positivity
  have hcardG : (Fintype.card (AffG p) : ℝ) = G := by rw [card_affG]; push_cast; ring
  set M : ℝ := ((Δ * s * (p - 1) + s * p * Δ : ℕ) : ℝ) / G with hM
  set L : ℝ := Real.log (Q.card ^ 2 + 1) with hL
  set T : ℝ := (Real.exp 1 - 1) * Fintype.card ι * M + μ * L with hT
  have hμpos : (0 : ℝ) < μ := by exact_mod_cast hμ
  have hQpos : (0 : ℝ) < Q.card ^ 2 + 1 := by positivity
  -- the bad events
  set ev := (Q ×ˢ Q).filter fun xy : V × V => xy.1 ≠ xy.2 ∧ ∃ w, emb w = xy.2 with hev
  have hcount : ∀ xy ∈ ev, ((univ.filter fun g : ι → AffG p =>
      T ≤ ∑ v, (movedLoad emb A xy.1 xy.2 v (g v) : ℝ)).card : ℝ) ≤
      (Fintype.card (AffG p) : ℝ) ^ Fintype.card ι / (Q.card ^ 2 + 1) := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨-, hne, w, rfl⟩ := mem_filter.1 hxy
    have hX0 : ∀ v g, (0 : ℝ) ≤ movedLoad emb A x (emb w) v g := fun _ _ => Nat.cast_nonneg _
    have hXb : ∀ v g, (movedLoad emb A x (emb w) v g : ℝ) ≤ μ := fun v g => by
      exact_mod_cast card_moved_pair_le emb g (A v) (hcodeg v) hne
    have hch := card_sum_ge_le (fun v g => (movedLoad emb A x (emb w) v g : ℝ)) hμpos hX0 hXb T
    have hmean : ∀ v, (∑ g, (movedLoad emb A x (emb w) v g : ℝ)) / Fintype.card (AffG p) ≤ M := by
      intro v
      rw [hcardG, hM]
      refine div_le_div_of_nonneg_right ?_ hGpos.le
      rw [← Nat.cast_sum]
      exact_mod_cast sum_movedLoad_le emb A hs hdeg v hne
    have hsum : ∑ v, (∑ g, (movedLoad emb A x (emb w) v g : ℝ)) / Fintype.card (AffG p) ≤
        Fintype.card ι * M := by
      refine (sum_le_sum fun v _ => hmean v).trans ?_
      rw [sum_const, card_univ, nsmul_eq_mul]
    have hexp : (Real.exp 1 - 1) * (∑ v, (∑ g, (movedLoad emb A x (emb w) v g : ℝ)) /
        Fintype.card (AffG p)) / μ - T / μ ≤ -L := by
      have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      rw [div_sub_div_same, div_le_iff₀ hμpos, hT]
      nlinarith [mul_le_mul_of_nonneg_left hsum he]
    refine hch.trans ?_
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc Real.exp _ ≤ Real.exp (-L) := Real.exp_le_exp.2 hexp
      _ = (Q.card ^ 2 + 1 : ℝ)⁻¹ := by rw [Real.exp_neg, hL, Real.exp_log hQpos]
  have hev : (ev.card : ℝ) ≤ Q.card ^ 2 := by
    have := (card_filter_le (Q ×ˢ Q) (fun xy : V × V => xy.1 ≠ xy.2 ∧ ∃ w, emb w = xy.2)).trans
      (le_of_eq (card_product Q Q))
    rw [sq]; exact_mod_cast this
  obtain ⟨g, hg⟩ := exists_good_choice ev (fun xy (g : ι → AffG p) =>
    T ≤ ∑ v, (movedLoad emb A xy.1 xy.2 v (g v) : ℝ)) (by
      have htot : (0 : ℝ) < (Fintype.card (AffG p) : ℝ) ^ Fintype.card ι := by
        rw [hcardG]; positivity
      calc ∑ xy ∈ ev, _ ≤ ∑ _xy ∈ ev,
            (Fintype.card (AffG p) : ℝ) ^ Fintype.card ι / (Q.card ^ 2 + 1) := sum_le_sum hcount
        _ = ev.card * ((Fintype.card (AffG p) : ℝ) ^ Fintype.card ι / (Q.card ^ 2 + 1)) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ Q.card ^ 2 * ((Fintype.card (AffG p) : ℝ) ^ Fintype.card ι / (Q.card ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_right hev (by positivity)
        _ < (Fintype.card (AffG p) : ℝ) ^ Fintype.card ι := by
            rw [mul_div_assoc', div_lt_iff₀ hQpos]; nlinarith)
  refine ⟨g, fun x y hxy hy => ?_⟩
  by_cases hmem : (x, y) ∈ ev
  · have := hg (x, y) hmem
    push_neg at this
    push_cast
    exact this
  · -- a pair outside `Q` is covered by no moved set
    have hzero : ∀ v, movedLoad emb A x y v (g v) = 0 := by
      intro v
      unfold movedLoad
      rw [card_eq_zero, filter_eq_empty_iff]
      rintro k - ⟨hx, hy'⟩
      have hQ' : ∀ u ∈ (A v k).image (affMap emb (g v)), u ∈ Q := by
        intro u hu
        obtain ⟨a, ha, rfl⟩ := mem_image.1 hu
        by_cases har : ∃ z, emb z = a
        · obtain ⟨z, rfl⟩ := har; rw [affMap_emb]; exact hQ _
        · rw [affMap_of_not emb _ har]; exact hAQ v k ha
      exact hmem (mem_filter.2 ⟨mem_product.2 ⟨hQ' x hx, hQ' y hy'⟩, hxy, hy⟩)
    simp only [hzero, sum_const_zero, Nat.cast_zero]
    have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [sq_nonneg (Q.card : ℝ)])
    have hM0 : 0 ≤ M := div_nonneg (Nat.cast_nonneg _) hGpos.le
    have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hL1 : 0 < L := Real.log_pos (by
      have : 0 < Q.card := card_pos.2 ⟨_, hQ 0⟩
      have : (1 : ℝ) ≤ Q.card := by exact_mod_cast this
      nlinarith)
    have := mul_pos hμpos hL1
    have : 0 ≤ (Real.exp 1 - 1) * Fintype.card ι * M := by positivity
    linarith

end Spread

end RefinedAbsorption.Local
