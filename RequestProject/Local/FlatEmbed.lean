module
public import RequestProject.Local.Affine
public import RequestProject.Local.LocalAssembly
public import RequestProject.Sharp.Sparsify
public import Mathlib.NumberTheory.Bertrand

/-!
# Random embedding of flat local refiners (Lemma 4.1, link level `1`, `r = 3`)

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Lemma 4.1 (Refine Down, one step) and
Theorem 4.4 (local multi-refiners), in the case of `3`-graphs and outside parts of size `1`.
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

`FlatGraphRefiners q a` is the input from uniformity `2` that the proof of Theorem 4.4 uses
(Theorem 3.7/3.8 for graphs with the flatness conclusion (2)): every multigraph `L` of bounded
multiplicity with copies inside `Y` and vertex degrees `≤ d` has, for every set `P` of new vertices
disjoint from `Y` with `|Y| ≤ K |P|`, a complete `K_q^2`-multi-refiner inside `Y ∪ P` such that

* every new copy meets `P` (flatness);
* the new copies have vertex degrees `≤ C (d + a |P|)` and multiplicities `≤ C`;
* any two vertices lie together in the spans of at most `C` pieces, and two vertices of `Y` lie
  together in the span of a piece only through an old copy of that piece on these two vertices
  (the pieces of an omni-absorber are cliques, and flatness forbids new copies inside `Y`).

**`flatEmbedTagged`**: from `FlatGraphRefiners (q - 1) (sharpCost 2)`, the residues of a tagged
stage (all inside a common sub-reserve `Z₁`) have complete tagged refiners inside the reserve
`Zo`, with budget `C · (Bd₁ + sharpCost 3 |Zo|)`, where `Bd₁` bounds the lifted degrees of the
residues.  The local refiner of every tag is built on `Z₁ ∪ P₀` (`P₀ ⊆ Zo \ Z₁` a copy of
`ZMod p`) and then moved by a random affine map of `P₀` (`exists_affine_spread`).
-/

@[expose] public section

namespace RefinedAbsorption.Local

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown RefinedAbsorption.LinkSpread RefinedAbsorption.Sharp
  RefinedAbsorption.Window

/-- **Flat local refiners in uniformity `2`** (see the module docstring). -/
def FlatGraphRefiners (q : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ K : ℕ, ∃ C Ch : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
    (Y P : Finset (Fin n)) (L : Finset E) (d : ℕ),
    Disjoint Y P → Y.card ≤ K * P.card → Ch ≤ P.card →
    MIsRGraph 2 ends L → (∀ x ∈ L, ends x ⊆ Y) → (∀ v, mdeg ends L {v} ≤ d) →
    (∀ e, mult ends L e ≤ K) →
    ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
      (R : Finset E') (𝒲 : Finset (Finset E')),
      Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
      IsMultiRefiner q 2 C ends' (L.image g) R 𝒲 ∧
      (∀ c ∈ R, ends' c ⊆ Y ∪ P ∧ (ends' c ∩ P).Nonempty) ∧
      (∀ v, mdeg ends' R {v} ≤ C * (d + a P.card)) ∧
      (∀ e, mult ends' R e ≤ C) ∧
      (∀ x y, x ≠ y →
        (𝒲.filter fun W => x ∈ W.biUnion ends' ∧ y ∈ W.biUnion ends').card ≤ C) ∧
      (∀ W ∈ 𝒲, ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → x ∈ W.biUnion ends' → y ∈ W.biUnion ends' →
        ∃ c ∈ W, c ∈ L.image g ∧ ends' c = {x, y})

/-! ### Auxiliary facts -/

/-- A copy of `ZMod p` (`p` prime) inside a set `A` of at least two vertices, with
`|A| ≤ 2 p + 1` (Bertrand's postulate). -/
theorem exists_prime_emb {n : ℕ} (A : Finset (Fin n)) (hA : 2 ≤ A.card) :
    ∃ p : ℕ, p.Prime ∧ ∃ emb : ZMod p ↪ Fin n, (∀ z, emb z ∈ A) ∧ A.card ≤ 2 * p + 1 := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (A.card / 2) (by omega)
  have hpA : p ≤ A.card := by omega
  obtain ⟨B, hBA, hBc⟩ := exists_subset_card_eq hpA
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact ⟨p, hp, ((ZMod.finEquiv p).symm.toEquiv.toEmbedding).trans
    (B.orderEmbOfFin hBc).toEmbedding, fun z => hBA (B.orderEmbOfFin_mem hBc _), by omega⟩

/-- `log (m² + 1) ≤ 2 (⌊log₂ m⌋ + 1)`. -/
theorem log_sq_add_one_le (m : ℕ) :
    Real.log ((m : ℝ) ^ 2 + 1) ≤ 2 * ((Nat.log 2 m : ℝ) + 1) := by
  have h1 : (m : ℝ) ^ 2 + 1 ≤ ((2 : ℝ) ^ (Nat.log 2 m + 1)) ^ 2 := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
    have : (m : ℝ) + 1 ≤ 2 ^ (Nat.log 2 m + 1) := by exact_mod_cast h
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  calc Real.log ((m : ℝ) ^ 2 + 1) ≤ Real.log (((2 : ℝ) ^ (Nat.log 2 m + 1)) ^ 2) :=
        Real.log_le_log (by positivity) h1
    _ = 2 * ((Nat.log 2 m : ℝ) + 1) * Real.log 2 := by
        rw [Real.log_pow, Real.log_pow]; push_cast; ring
    _ ≤ 2 * ((Nat.log 2 m : ℝ) + 1) := by
        have := Real.log_two_lt_d9
        have h2 : (0 : ℝ) ≤ 2 * ((Nat.log 2 m : ℝ) + 1) := by positivity
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- The logarithmic term is dominated by the sharp cost. -/
theorem log_sq_add_one_le_sharpCost {m : ℕ} (hm : 1 ≤ m) :
    Real.log ((m : ℝ) ^ 2 + 1) ≤ 2 * (sharpCost 3 m : ℝ) := by
  refine (log_sq_add_one_le m).trans ?_
  have h : Nat.log 2 m + 1 ≤ sharpCost 3 m := by
    unfold sharpCost
    exact Nat.le_mul_of_pos_left _ (one_le_winCost 3 hm)
  have : ((Nat.log 2 m : ℝ) + 1) ≤ sharpCost 3 m := by exact_mod_cast h
  linarith

/-- Vertex degrees of a fibre are bounded by the lifted `2`-degrees. -/
theorem mdeg_fibre_singleton_le {n : ℕ} {E₁ : Type} [DecidableEq E₁]
    {tg bd : E₁ → Finset (Fin n)} {Zo : Finset (Fin n)} {X : Finset E₁} {Bd : ℕ}
    (htg : ∀ x, Disjoint (tg x) Zo) (hbd : ∀ x, bd x ⊆ Zo) {T : Finset (Fin n)}
    (hT : T ∈ X.image tg) (htgc : ∀ x ∈ X, (tg x).card = 1)
    (hdeg : ∀ S : Finset (Fin n), S.card = 2 → mdeg (liftEnds tg bd) X S ≤ Bd) (v : Fin n) :
    mdeg bd (fibre tg X T) {v} ≤ Bd := by
  obtain ⟨x₀, hx₀, rfl⟩ := mem_image.1 hT
  by_cases hv : v ∈ tg x₀
  · refine le_of_eq_of_le (card_eq_zero.2 (filter_eq_empty_iff.2 fun x hx hvx => ?_))
      (Nat.zero_le _)
    have hxT := (mem_fibre.1 hx).2
    rw [singleton_subset_iff] at hvx
    exact disjoint_left.1 (htg x) (hxT ▸ hv) (hbd x hvx)
  · have hS : (tg x₀ ∪ {v}).card = 2 := by
      rw [card_union_of_disjoint (disjoint_singleton_right.2 hv), htgc x₀ hx₀, card_singleton]
    refine le_trans (card_le_card fun x hx => ?_) (hdeg _ hS)
    simp only [mem_filter, mem_fibre] at hx ⊢
    obtain ⟨⟨hxX, hxT⟩, hvx⟩ := hx
    refine ⟨hxX, ?_⟩
    unfold liftEnds
    rw [hxT]
    exact union_subset_union subset_rfl hvx

/-- The multiplicities of a `2`-set in the fibres add up to at most its lifted degree. -/
theorem sum_mult_fibre_le {n : ℕ} {E₁ : Type} [DecidableEq E₁]
    {tg bd : E₁ → Finset (Fin n)} {X : Finset E₁} {Bd : ℕ}
    (hdeg : ∀ S : Finset (Fin n), S.card = 2 → mdeg (liftEnds tg bd) X S ≤ Bd)
    {S : Finset (Fin n)} (hS : S.card = 2) :
    ∑ T ∈ X.image tg, mult bd (fibre tg X T) S ≤ Bd := by
  refine le_trans (le_of_eq (b := (X.filter fun x => bd x = S).card) ?_)
    ((card_le_card fun x hx => ?_).trans (hdeg S hS))
  · unfold mult
    rw [card_eq_sum_card_fiberwise (f := tg) (t := X.image tg)
      (fun x hx => mem_image_of_mem _ (mem_filter.1 hx).1)]
    refine sum_congr rfl fun T _ => congrArg card ?_
    ext x
    simp only [mem_filter, fibre]
    tauto
  · simp only [mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    unfold liftEnds
    rw [hx.2]
    exact subset_union_right

/-- The pieces whose span contains a vertex `u` are at most `C` times the degree of `u`. -/
theorem card_pieces_vertex_le {V E : Type*} [DecidableEq V] [DecidableEq E] {q r C : ℕ}
    {ends : E → Finset V} {X R Y : Finset E} {𝒲 : Finset (Finset E)}
    (h : IsResidualMultiRefiner q r C ends X R Y 𝒲) (u : V) :
    (𝒲.filter fun W => u ∈ W.biUnion ends).card ≤ C * mdeg ends (X ∪ R) {u} := by
  refine (card_le_card ?_).trans ((card_biUnion_le (s := (X ∪ R).filter fun c => {u} ⊆ ends c)
    (t := fun c => 𝒲.filter fun W => c ∈ W)).trans ?_)
  · intro W hW
    obtain ⟨hW, hu⟩ := mem_filter.1 hW
    obtain ⟨c, hc, huc⟩ := mem_biUnion.1 hu
    exact mem_biUnion.2 ⟨c, mem_filter.2 ⟨h.subset W hW hc, singleton_subset_iff.2 huc⟩,
      mem_filter.2 ⟨hW, hc⟩⟩
  · refine (sum_le_sum fun c hc => h.mult_le c (mem_filter.1 hc).1).trans ?_
    rw [sum_const, smul_eq_mul, mul_comm]
    rfl

/-- The pieces rooted at an old copy on `{x, y}` are at most `C` times its multiplicity. -/
theorem card_pieces_rooted_le {V E : Type*} [DecidableEq V] [DecidableEq E] {q r C : ℕ}
    {ends : E → Finset V} {X R Y : Finset E} {𝒲 : Finset (Finset E)}
    (h : IsResidualMultiRefiner q r C ends X R Y 𝒲) (P : Finset E → Prop) [DecidablePred P]
    (e : Finset V) (hP : ∀ W ∈ 𝒲, P W → ∃ c ∈ W, c ∈ X ∧ ends c = e) :
    (𝒲.filter P).card ≤ C * mult ends X e := by
  refine (card_le_card ?_).trans ((card_biUnion_le (s := X.filter fun c => ends c = e)
    (t := fun c => 𝒲.filter fun W => c ∈ W)).trans ?_)
  · intro W hW
    obtain ⟨hW, hPW⟩ := mem_filter.1 hW
    obtain ⟨c, hcW, hcX, hce⟩ := hP W hW hPW
    exact mem_biUnion.2 ⟨c, mem_filter.2 ⟨hcX, hce⟩, mem_filter.2 ⟨hW, hcW⟩⟩
  · refine (sum_le_sum fun c hc => h.mult_le c (mem_union_left _ (mem_filter.1 hc).1)).trans ?_
    rw [sum_const, smul_eq_mul, mul_comm]
    rfl

/-- A set avoiding the copy of `ZMod p` is covered by a moved set iff it is covered by the set. -/
theorem subset_image_affMap_iff {V : Type*} [DecidableEq V] {p : ℕ} [Fact p.Prime]
    (emb : ZMod p ↪ V) (g : AffG p) {S A : Finset V} (hS : ∀ x ∈ S, ¬ ∃ z, emb z = x) :
    S ⊆ A.image (affMap emb g) ↔ S ⊆ A := by
  constructor
  · intro h x hx
    obtain ⟨a, ha, hax⟩ := mem_image.1 (h hx)
    by_cases har : ∃ z, emb z = a
    · exact absurd ((affMap_mem_range_iff emb g a).2 har |>.elim fun z hz => ⟨z, hz.trans hax⟩)
        (hS x hx)
    · rw [affMap_of_not emb g har] at hax
      exact hax ▸ ha
  · intro h x hx
    exact mem_image.2 ⟨x, h hx, affMap_of_not emb g (hS x hx)⟩

/-- **Lifted counts.**  For families of sets `B T k ⊆ Zo` attached to distinct single-vertex tags
outside `Zo`, the lifted count of a `2`-set is bounded by the vertex counts of one family (when the
`2`-set contains a tag) or by the summed counts of `2`-sets inside `Zo`. -/
theorem lifted_count_le {n : ℕ} {Zo : Finset (Fin n)} {ι : Type*} [Fintype ι]
    (tag : ι → Finset (Fin n)) (htag1 : ∀ T, (tag T).card = 1) (htagZ : ∀ T, Disjoint (tag T) Zo)
    (htaginj : Function.Injective tag)
    {κ : ι → Type*} (I : ∀ T, Finset (κ T)) (B : ∀ T, κ T → Finset (Fin n))
    (hB : ∀ T, ∀ k ∈ I T, B T k ⊆ Zo) {b₁ b₂ : ℕ}
    (h1 : ∀ T z, ((I T).filter fun k => z ∈ B T k).card ≤ b₁)
    (h2 : ∀ S : Finset (Fin n), S ⊆ Zo → S.card = 2 →
      ∑ T, ((I T).filter fun k => S ⊆ B T k).card ≤ b₂)
    (S : Finset (Fin n)) (hS : S.card = 2) :
    ∑ T, ((I T).filter fun k => S ⊆ tag T ∪ B T k).card ≤ b₁ + b₂ := by
  classical
  by_cases hSZ : S ⊆ Zo
  · refine le_trans (le_of_eq (sum_congr rfl fun T _ => congrArg card (filter_congr
      fun k _ => ?_))) ((h2 S hSZ hS).trans (Nat.le_add_left _ _))
    constructor
    · intro h x hx
      rcases mem_union.1 (h hx) with h' | h'
      · exact absurd (hSZ hx) (disjoint_left.1 (htagZ T) h')
      · exact h'
    · intro h; exact h.trans subset_union_right
  · obtain ⟨v, hvS, hvZ⟩ := not_subset.1 hSZ
    obtain ⟨z, hzS, hzv⟩ : ∃ z ∈ S, z ≠ v := by
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hS
      rcases mem_insert.1 hvS with rfl | h
      · exact ⟨b, by simp, hab.symm⟩
      · rw [mem_singleton] at h; subst h; exact ⟨a, by simp, hab⟩
    have hterm : ∀ T, ((I T).filter fun k => S ⊆ tag T ∪ B T k).card ≤
        if v ∈ tag T then b₁ else 0 := by
      intro T
      split_ifs with hvT
      · refine le_trans (card_le_card fun k hk => ?_) (h1 T z)
        obtain ⟨hk, hSk⟩ := mem_filter.1 hk
        refine mem_filter.2 ⟨hk, ?_⟩
        rcases mem_union.1 (hSk hzS) with h' | h'
        · obtain ⟨t, ht⟩ := card_eq_one.1 (htag1 T)
          rw [ht, mem_singleton] at h' hvT
          exact absurd (h'.trans hvT.symm) hzv
        · exact h'
      · refine le_of_eq (card_eq_zero.2 (filter_eq_empty_iff.2 fun k hk hSk => ?_))
        rcases mem_union.1 (hSk hvS) with h' | h'
        · exact hvT h'
        · exact hvZ (hB T k hk h')
    refine (sum_le_sum fun T _ => hterm T).trans ?_
    rw [← sum_filter, sum_const, smul_eq_mul]
    have hone : (univ.filter fun T => v ∈ tag T).card ≤ 1 := by
      refine card_le_one.2 fun T hT T' hT' => htaginj ?_
      have h1' := (mem_filter.1 hT).2
      have h2' := (mem_filter.1 hT').2
      obtain ⟨t, ht⟩ := card_eq_one.1 (htag1 T)
      obtain ⟨t', ht'⟩ := card_eq_one.1 (htag1 T')
      rw [ht, mem_singleton] at h1'
      rw [ht', mem_singleton] at h2'
      rw [ht, ht', ← h1', ← h2']
    calc (univ.filter fun T => v ∈ tag T).card * b₁ ≤ 1 * b₁ := Nat.mul_le_mul_right _ hone
      _ ≤ b₁ + b₂ := by omega

/-- Counting a predicate of the sets of a system indexed by `R ⊕ 𝒲`. -/
theorem card_univ_filter_sum {α β γ : Type*} (s : Finset α) (t : Finset β) (f : α → γ)
    (g : β → γ) (Φ : γ → Prop) [DecidablePred Φ] :
    (univ.filter fun k : {a // a ∈ s} ⊕ {b // b ∈ t} =>
      Φ (Sum.elim (fun a => f a.1) (fun b => g b.1) k)).card =
      (s.filter fun a => Φ (f a)).card + (t.filter fun b => Φ (g b)).card := by
  classical
  simp only [card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  exact congrArg₂ Nat.add (sum_coe_sort s (fun a => if Φ (f a) then 1 else 0))
    (sum_coe_sort t (fun b => if Φ (g b) then 1 else 0))

end RefinedAbsorption.Local
