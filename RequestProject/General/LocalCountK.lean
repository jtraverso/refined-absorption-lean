module
public import RequestProject.General.SpreadCore
public import RequestProject.SparseChain.FlatEmbedS

/-!
# Local counts for flat clique refiners in uniformity `k`

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Lemma 4.1 (the counts behind
Claim 4.1.1).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

* `mdeg_le_pow_of_deg`: in a `k`-multigraph inside `Zo` with `(k-1)`-degrees `≤ d`, a set of size
  `z ≤ k - 1` lies in at most `|Zo|^(k-1-z) d` copies.
* `card_pieces_sub_le`: in a refiner whose pieces are cliques, the nonempty pieces whose span
  contains a set `Q` with `|Q| ≤ k` are at most `C` times the degree of `Q`.
* `mdeg_fibre_le_gen`, `sum_mult_fibre_tags_le`: degrees of the fibres of a tagged multigraph.
-/

@[expose] public section

namespace RefinedAbsorption.General

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LinkSpread

section Counts

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- Small sets have few copies through them. -/
theorem mdeg_le_pow_of_deg {n k : ℕ} {ends : E → Finset (Fin n)} {F : Finset E}
    {Zo : Finset (Fin n)} (hF : ∀ c ∈ F, ends c ⊆ Zo ∧ (ends c).card = k) {d : ℕ}
    (hd : ∀ U : Finset (Fin n), U.card = k - 1 → mdeg ends F U ≤ d)
    (Q : Finset (Fin n)) (hQ : Q.card ≤ k - 1) :
    mdeg ends F Q ≤ Zo.card ^ (k - 1 - Q.card) * d := by
  classical
  set 𝒰 := (Zo.powersetCard (k - 1)).filter fun U => Q ⊆ U with h𝒰
  have h𝒰c : 𝒰.card ≤ Zo.card ^ (k - 1 - Q.card) :=
    card_tags_containing_le (Zo.powersetCard (k - 1)) Zo
      (fun T hT => mem_powersetCard.1 hT) Q hQ
  refine (card_le_card (t := 𝒰.biUnion fun U => F.filter fun c => U ⊆ ends c) ?_).trans
    (card_biUnion_le.trans ?_)
  · intro c hc
    obtain ⟨hcF, hQc⟩ := mem_filter.1 hc
    obtain ⟨hcZ, hck⟩ := hF c hcF
    obtain ⟨U, hQU, hUc, hUcard⟩ := exists_subsuperset_card_eq hQc hQ (by omega)
    exact mem_biUnion.2 ⟨U, mem_filter.2 ⟨mem_powersetCard.2 ⟨hUc.trans hcZ, hUcard⟩, hQU⟩,
      mem_filter.2 ⟨hcF, hUc⟩⟩
  · calc ∑ U ∈ 𝒰, (F.filter fun c => U ⊆ ends c).card ≤ ∑ _U ∈ 𝒰, d :=
          sum_le_sum fun U hU => hd U (mem_powersetCard.1 (mem_filter.1 hU).1).2
      _ = 𝒰.card * d := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ h𝒰c

/-- Nonempty clique pieces through a set of size `≤ k`. -/
theorem card_pieces_sub_le {q k C : ℕ} {ends : E → Finset V} {X R Y : Finset E}
    {𝒲 : Finset (Finset E)} (h : IsResidualMultiRefiner q k C ends X R Y 𝒲)
    (hcl : ∀ W ∈ 𝒲, ∀ S ⊆ W.biUnion ends, S.card = k → ∃ c ∈ W, ends c = S)
    (Q : Finset V) (hQ : Q.card ≤ k) :
    (𝒲.filter fun W => Q ⊆ W.biUnion ends ∧ (W.biUnion ends).Nonempty).card ≤
      C * mdeg ends (X ∪ R) Q := by
  refine (card_le_card ?_).trans ((card_biUnion_le (s := (X ∪ R).filter fun c => Q ⊆ ends c)
    (t := fun c => 𝒲.filter fun W => c ∈ W)).trans ?_)
  · intro W hW
    obtain ⟨hW, hQW, hne⟩ := mem_filter.1 hW
    obtain ⟨v, hv⟩ := hne
    obtain ⟨c₀, hc₀, -⟩ := mem_biUnion.1 hv
    have hk : k ≤ (W.biUnion ends).card := by
      rw [← h.rgraph c₀ (h.subset W hW hc₀)]
      exact card_le_card (subset_biUnion_of_mem ends hc₀)
    obtain ⟨U, hQU, hUW, hUc⟩ := exists_subsuperset_card_eq hQW hQ hk
    obtain ⟨c, hcW, hcU⟩ := hcl W hW U hUW hUc
    exact mem_biUnion.2 ⟨c, mem_filter.2 ⟨h.subset W hW hcW, hcU ▸ hQU⟩, mem_filter.2 ⟨hW, hcW⟩⟩
  · refine (sum_le_sum fun c hc => h.mult_le c (mem_filter.1 hc).1).trans ?_
    rw [sum_const, smul_eq_mul, mul_comm]
    rfl

end Counts

section Fibres

variable {n : ℕ} {E₁ : Type} [DecidableEq E₁] {tg bd : E₁ → Finset (Fin n)} {X : Finset E₁}
  {Zo : Finset (Fin n)}

omit [DecidableEq E₁] in
/-- `(k-1)`-degrees of a fibre are bounded by the lifted `(r-1)`-degrees. -/
theorem mdeg_fibre_le_gen {i k r Bd : ℕ} (hikr : i + (k - 1) = r - 1)
    (htg : ∀ x, Disjoint (tg x) Zo) (hbd : ∀ x, bd x ⊆ Zo) {T : Finset (Fin n)}
    (hT : T ∈ X.image tg) (htgc : ∀ x ∈ X, (tg x).card = i)
    (hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ Bd)
    (U : Finset (Fin n)) (hU : U.card = k - 1) :
    mdeg bd (fibre tg X T) U ≤ Bd := by
  obtain ⟨x₀, hx₀, rfl⟩ := mem_image.1 hT
  by_cases hUZ : U ⊆ Zo
  · have hS : (tg x₀ ∪ U).card = r - 1 := by
      rw [card_union_of_disjoint (disjoint_of_subset_right hUZ (htg x₀)), htgc x₀ hx₀, hU, hikr]
    refine le_trans (card_le_card fun x hx => ?_) (hdeg _ hS)
    simp only [mem_filter, mem_fibre] at hx ⊢
    obtain ⟨⟨hxX, hxT⟩, hUx⟩ := hx
    refine ⟨hxX, ?_⟩
    unfold liftEnds
    rw [hxT]
    exact union_subset_union subset_rfl hUx
  · refine le_of_eq_of_le (card_eq_zero.2 (filter_eq_empty_iff.2 fun x _ hUx =>
      hUZ (hUx.trans (hbd x)))) (Nat.zero_le _)

/-- The multiplicities of a `k`-set in the fibres of the tags containing `J` add up to at most
`|Ut|^(i-1-|J|)` times the lifted degree bound. -/
theorem sum_mult_fibre_tags_le {i k r Bd : ℕ} (hi : 1 ≤ i) (hikr : i - 1 + k = r - 1)
    {Ut : Finset (Fin n)} (htU : ∀ x ∈ X, tg x ⊆ Ut) (htg : ∀ x, Disjoint (tg x) Zo)
    (htgc : ∀ x ∈ X, (tg x).card = i)
    (hdeg : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ Bd)
    (J Q : Finset (Fin n)) (hJ : J.card ≤ i - 1) (hQZ : Q ⊆ Zo) (hQ : Q.card = k) :
    ∑ T ∈ (X.image tg).filter (fun T => J ⊆ T), mult bd (fibre tg X T) Q ≤
      Ut.card ^ (i - 1 - J.card) * Bd := by
  classical
  have h1 : ∑ T ∈ (X.image tg).filter (fun T => J ⊆ T), mult bd (fibre tg X T) Q =
      (X.filter fun x => J ⊆ tg x ∧ bd x = Q).card := by
    rw [card_eq_sum_card_fiberwise (f := tg) (t := (X.image tg).filter (fun T => J ⊆ T))
      (fun x hx => mem_filter.2 ⟨mem_image_of_mem _ (mem_filter.1 hx).1, (mem_filter.1 hx).2.1⟩)]
    refine sum_congr rfl fun T hT => congrArg card ?_
    ext x
    simp only [mem_filter, fibre]
    have hJT := (mem_filter.1 hT).2
    constructor
    · rintro ⟨⟨hx, rfl⟩, hb⟩; exact ⟨⟨hx, hJT, hb⟩, rfl⟩
    · rintro ⟨⟨hx, -, hb⟩, rfl⟩; exact ⟨⟨hx, rfl⟩, hb⟩
  rw [h1]
  set 𝒥 := ((Ut \ Zo).powersetCard (i - 1)).filter fun J' => J ⊆ J' with h𝒥
  have h𝒥c : 𝒥.card ≤ Ut.card ^ (i - 1 - J.card) :=
    (card_tags_containing_le ((Ut \ Zo).powersetCard (i - 1)) (Ut \ Zo)
      (fun T hT => mem_powersetCard.1 hT) J hJ).trans
      (Nat.pow_le_pow_left (card_le_card sdiff_subset) _)
  refine (card_le_card (t := 𝒥.biUnion fun J' => X.filter fun x => J' ∪ Q ⊆ liftEnds tg bd x)
    ?_).trans (card_biUnion_le.trans ?_)
  · intro x hx
    obtain ⟨hxX, hJx, hbx⟩ := mem_filter.1 hx
    obtain ⟨J', hJJ', hJ'x, hJ'c⟩ := exists_subsuperset_card_eq hJx hJ
      (by rw [htgc x hxX]; omega)
    refine mem_biUnion.2 ⟨J', mem_filter.2 ⟨mem_powersetCard.2 ⟨fun y hy => mem_sdiff.2
      ⟨htU x hxX (hJ'x hy), disjoint_left.1 (htg x) (hJ'x hy)⟩, hJ'c⟩, hJJ'⟩,
      mem_filter.2 ⟨hxX, ?_⟩⟩
    unfold liftEnds
    rw [hbx]
    exact union_subset_union hJ'x subset_rfl
  · calc ∑ J' ∈ 𝒥, (X.filter fun x => J' ∪ Q ⊆ liftEnds tg bd x).card ≤ ∑ _J' ∈ 𝒥, Bd := by
          refine sum_le_sum fun J' hJ' => hdeg _ ?_
          obtain ⟨hJ'U, hJ'c⟩ := mem_powersetCard.1 (mem_filter.1 hJ').1
          have hdis : Disjoint J' Q := disjoint_of_subset_left hJ'U
            (disjoint_of_subset_right hQZ disjoint_sdiff_self_left)
          rw [card_union_of_disjoint hdis, hJ'c, hQ, hikr]
      _ = 𝒥.card * Bd := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ h𝒥c

end Fibres

end RefinedAbsorption.General
