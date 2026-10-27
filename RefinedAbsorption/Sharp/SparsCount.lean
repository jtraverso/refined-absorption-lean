module
public import RefinedAbsorption.Sharp.CliqueRefiner

/-!
# Degree counting for the Edge Sparsification Lemma

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Lemma 3.12 (the bounds on
`Δ(R₁)` and `Δ(X₃)`).

Fix a partition of the vertices into `k` parts (`φ : V → Fin k`), and for every `r`-multiset `I`
of parts a special set `Sp I` (Lemma 3.19).  The *type* of a copy `x` is the multiset
`ptype φ (ends x)` of the parts of its vertices, and its clique is
`Vx x = ends x ∪ Sp (type x)`.  Assume

* every part meets the window `U` in at most `P` vertices;
* for every `(r-1)`-set `S` and part `i`, at most `Q` copies consist of `S` and a vertex of part
  `i`;
* the special sets are spread: for every multiset `J` of parts and every set `T` with
  `|J| + |T| = r - 1`, at most `B |T|` types `I` satisfy `T ⊆ Sp I` and `J ≤ I`.

Then for every `(r-1)`-set `S`:

* **`card_clique_supersets_le`**: at most `∑_{T ⊆ S} B|T| (rP)^{|T|} (rQ)` cliques contain `S`;
* **`card_clique_link_le`**: at most `∑_{T ⊆ S} B|T| (q-r) + ∑_{∅ ≠ T ⊆ S} B|T| (rP)` vertices
  `v ∉ S` lie in a clique `Vx x ⊇ S ∪ {v}` with `S ∪ {v} ≠ ends x`.
-/

@[expose] public section

namespace RefinedAbsorption.Sharp

open Finset RefinedAbsorption.MultiRefiner

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- The type of a vertex set: the multiset of the parts of its vertices. -/
def ptype {k : ℕ} (φ : V → Fin k) (A : Finset V) : Multiset (Fin k) := A.val.map φ

omit [DecidableEq V] in
theorem ptype_le {k : ℕ} (φ : V → Fin k) {A B : Finset V} (h : A ⊆ B) :
    ptype φ A ≤ ptype φ B :=
  Multiset.map_le_map (Finset.val_le_iff.2 h)

omit [DecidableEq V] in
theorem card_ptype {k : ℕ} (φ : V → Fin k) (A : Finset V) :
    Multiset.card (ptype φ A) = A.card := by
  simp [ptype]

omit [DecidableEq V] in
theorem mem_ptype {k : ℕ} (φ : V → Fin k) {A : Finset V} {v : V} (hv : v ∈ A) :
    φ v ∈ ptype φ A :=
  Multiset.mem_map_of_mem _ hv

/-- The clique of a copy. -/
def sClique {k : ℕ} (ends : E → Finset V) (φ : V → Fin k)
    (Sp : Multiset (Fin k) → Finset V) (x : E) : Finset V :=
  ends x ∪ Sp (ptype φ (ends x))

/-- The types `I` with `T ⊆ Sp I` and `J ≤ I`. -/
def spreadSet {k : ℕ} (ends : E → Finset V) (φ : V → Fin k)
    (Sp : Multiset (Fin k) → Finset V) (X : Finset E) (J : Multiset (Fin k)) (T : Finset V) :
    Finset (Multiset (Fin k)) :=
  (X.image fun x => ptype φ (ends x)).filter fun I => T ⊆ Sp I ∧ J ≤ I

section Count

variable {k r q P Q : ℕ} {ends : E → Finset V} {φ : V → Fin k}
  {Sp : Multiset (Fin k) → Finset V} {X : Finset E} {U : Finset V} {B : ℕ → ℕ}

/-- Vertices of `U` lying in the parts of a type `I` with `|I| = r`. -/
theorem card_parts_le (hpart : ∀ i, (U.filter fun v => φ v = i).card ≤ P)
    {I : Multiset (Fin k)} (hI : Multiset.card I ≤ r) :
    (U.filter fun v => φ v ∈ I).card ≤ r * P := by
  have hsub : U.filter (fun v => φ v ∈ I) ⊆ I.toFinset.biUnion fun i => U.filter fun v => φ v = i := by
    intro v hv
    rw [mem_filter] at hv
    exact mem_biUnion.2 ⟨φ v, Multiset.mem_toFinset.2 hv.2, mem_filter.2 ⟨hv.1, rfl⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  refine (sum_le_sum fun i _ => hpart i).trans ?_
  rw [sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ ((Multiset.toFinset_card_le _).trans hI)

/-- Copies of a fixed type containing a fixed `(r-1-t)`-set. -/
theorem card_type_supersets_le (hXr : MIsRGraph r ends X) (hXU : ∀ x ∈ X, ends x ⊆ U)
    (hpart : ∀ i, (U.filter fun v => φ v = i).card ≤ P)
    (hdegp : ∀ S : Finset V, S.card = r - 1 → ∀ i,
      (X.filter fun x => S ⊆ ends x ∧ ∀ v ∈ ends x \ S, φ v = i).card ≤ Q)
    (hr : 1 ≤ r) {S' : Finset V} {t : ℕ} (hS' : S'.card + t = r - 1) (I : Multiset (Fin k))
    (hI : Multiset.card I = r) :
    (X.filter fun x => ptype φ (ends x) = I ∧ S' ⊆ ends x).card ≤ (r * P) ^ t * (r * Q) := by
  set UI := (U.filter fun v => φ v ∈ I) \ S' with hUI
  have hUIc : UI.card ≤ r * P :=
    (card_le_card sdiff_subset).trans (card_parts_le hpart hI.le)
  have hsub : (X.filter fun x => ptype φ (ends x) = I ∧ S' ⊆ ends x) ⊆
      ((UI.powersetCard t) ×ˢ I.toFinset).biUnion fun p =>
        X.filter fun x => S' ∪ p.1 ⊆ ends x ∧ ∀ v ∈ ends x \ (S' ∪ p.1), φ v = p.2 := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hxX, htype, hS'x⟩ := hx
    set W := ends x \ S' with hW
    have hWc : W.card = t + 1 := by
      rw [hW, card_sdiff_of_subset hS'x, hXr x hxX]; omega
    obtain ⟨v, hv⟩ : W.Nonempty := by rw [← card_pos, hWc]; omega
    have hvx : v ∈ ends x := (mem_sdiff.1 hv).1
    have hvS : v ∉ S' := (mem_sdiff.1 hv).2
    refine mem_biUnion.2 ⟨(W.erase v, φ v), mem_product.2 ⟨mem_powersetCard.2 ⟨?_, ?_⟩, ?_⟩,
      mem_filter.2 ⟨hxX, ?_, ?_⟩⟩
    · intro u hu
      have hu' := mem_sdiff.1 (mem_of_mem_erase hu)
      rw [hUI, mem_sdiff, mem_filter]
      refine ⟨⟨hXU x hxX hu'.1, ?_⟩, hu'.2⟩
      rw [← htype]; exact mem_ptype φ hu'.1
    · rw [card_erase_of_mem hv, hWc]; rfl
    · rw [Multiset.mem_toFinset, ← htype]; exact mem_ptype φ hvx
    · intro u hu
      rcases mem_union.1 hu with h | h
      · exact hS'x h
      · exact (mem_sdiff.1 (mem_of_mem_erase h)).1
    · intro u hu
      rw [mem_sdiff, mem_union, not_or] at hu
      obtain ⟨hux, huS, huW⟩ := hu
      have : u = v := by
        by_contra hne
        exact huW (mem_erase.2 ⟨hne, mem_sdiff.2 ⟨hux, huS⟩⟩)
      rw [this]
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  have hterm : ∀ p ∈ (UI.powersetCard t) ×ˢ I.toFinset,
      (X.filter fun x => S' ∪ p.1 ⊆ ends x ∧ ∀ v ∈ ends x \ (S' ∪ p.1), φ v = p.2).card ≤ Q := by
    intro p hp
    rw [mem_product, mem_powersetCard] at hp
    have hdisj : Disjoint S' p.1 := by
      rw [disjoint_right]
      intro u hu
      exact (mem_sdiff.1 (hp.1.1 hu)).2
    exact hdegp _ (by rw [card_union_of_disjoint hdisj, hp.1.2]; omega) p.2
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, smul_eq_mul, card_product, card_powersetCard]
  have h1 : UI.card.choose t ≤ (r * P) ^ t :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hUIc _)
  have h2 : I.toFinset.card ≤ r := (Multiset.toFinset_card_le _).trans hI.le
  calc UI.card.choose t * I.toFinset.card * Q ≤ (r * P) ^ t * r * Q :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 h2)
    _ = (r * P) ^ t * (r * Q) := by ring

/-- **Number of cliques containing an `(r-1)`-set** (the bound on `Δ(R₁)`). -/
theorem card_clique_supersets_le (hXr : MIsRGraph r ends X) (hXU : ∀ x ∈ X, ends x ⊆ U)
    (hpart : ∀ i, (U.filter fun v => φ v = i).card ≤ P)
    (hdegp : ∀ S : Finset V, S.card = r - 1 → ∀ i,
      (X.filter fun x => S ⊆ ends x ∧ ∀ v ∈ ends x \ S, φ v = i).card ≤ Q)
    (hspread : ∀ (J : Multiset (Fin k)) (T : Finset V), Multiset.card J + T.card = r - 1 →
      (spreadSet ends φ Sp X J T).card ≤ B T.card)
    (hr : 1 ≤ r) {S : Finset V} (hS : S.card = r - 1) :
    (X.filter fun x => S ⊆ sClique ends φ Sp x).card ≤
      ∑ T ∈ S.powerset, B T.card * ((r * P) ^ T.card * (r * Q)) := by
  have hsub : (X.filter fun x => S ⊆ sClique ends φ Sp x) ⊆ S.powerset.biUnion fun T =>
      (spreadSet ends φ Sp X (ptype φ (S \ T)) T).biUnion fun I =>
        X.filter fun x => ptype φ (ends x) = I ∧ S \ T ⊆ ends x := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hxX, hSx⟩ := hx
    set T := S ∩ Sp (ptype φ (ends x)) with hT
    have hST : S \ T ⊆ ends x := by
      intro v hv
      rw [mem_sdiff, hT, mem_inter, not_and] at hv
      rcases mem_union.1 (hSx hv.1) with h | h
      · exact h
      · exact absurd h (hv.2 hv.1)
    refine mem_biUnion.2 ⟨T, mem_powerset.2 inter_subset_left, mem_biUnion.2
      ⟨ptype φ (ends x), ?_, mem_filter.2 ⟨hxX, rfl, hST⟩⟩⟩
    unfold spreadSet
    exact mem_filter.2 ⟨mem_image_of_mem _ hxX, inter_subset_right, ptype_le φ hST⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun T hT => ?_))
  have hTS := mem_powerset.1 hT
  have hcardST : (S \ T).card + T.card = r - 1 := by
    rw [card_sdiff_of_subset hTS]; have := card_le_card hTS; omega
  refine card_biUnion_le.trans ?_
  have hterm : ∀ I ∈ spreadSet ends φ Sp X (ptype φ (S \ T)) T,
      (X.filter fun x => ptype φ (ends x) = I ∧ S \ T ⊆ ends x).card ≤
        (r * P) ^ T.card * (r * Q) := by
    intro I hI
    unfold spreadSet at hI
    obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_filter.1 hI).1
    exact card_type_supersets_le hXr hXU hpart hdegp hr hcardST _
      (by rw [card_ptype, hXr x hx])
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (hspread _ _ (by rw [card_ptype]; exact hcardST))

omit [DecidableEq E] in
/-- **The link of an `(r-1)`-set in the support of the clique refiner** (the bound on
`Δ(X₃)`). -/
theorem card_clique_link_le (hXr : MIsRGraph r ends X)
    (hpart : ∀ i, (U.filter fun v => φ v = i).card ≤ P)
    (hSpc : ∀ x ∈ X, (Sp (ptype φ (ends x))).card ≤ q - r)
    (hspread : ∀ (J : Multiset (Fin k)) (T : Finset V), Multiset.card J + T.card = r - 1 →
      (spreadSet ends φ Sp X J T).card ≤ B T.card)
    {S : Finset V} (hS : S.card = r - 1) (hr : 1 ≤ r) :
    (U.filter fun v => v ∉ S ∧ ∃ x ∈ X, insert v S ⊆ sClique ends φ Sp x ∧
        insert v S ≠ ends x).card ≤
      ∑ T ∈ S.powerset, B T.card * (q - r) +
        ∑ T ∈ S.powerset.filter (fun T => T.Nonempty), B T.card * (r * P) := by
  set A₁ := S.powerset.biUnion fun T =>
    (spreadSet ends φ Sp X (ptype φ (S \ T)) T).biUnion fun I => Sp I with hA₁
  set A₂ := (S.powerset.filter fun T => T.Nonempty).biUnion fun T =>
    (spreadSet ends φ Sp X (ptype φ (S \ T)) T).biUnion fun I => U.filter fun v => φ v ∈ I
    with hA₂
  have hsub : (U.filter fun v => v ∉ S ∧ ∃ x ∈ X, insert v S ⊆ sClique ends φ Sp x ∧
      insert v S ≠ ends x) ⊆ A₁ ∪ A₂ := by
    intro v hv
    rw [mem_filter] at hv
    obtain ⟨hvU, hvS, x, hxX, hsubx, hne⟩ := hv
    set I := ptype φ (ends x) with hI
    set T := S ∩ Sp I with hT
    have hSx : S ⊆ sClique ends φ Sp x := (subset_insert v S).trans hsubx
    have hST : S \ T ⊆ ends x := by
      intro u hu
      rw [mem_sdiff, hT, mem_inter, not_and] at hu
      rcases mem_union.1 (hSx hu.1) with h | h
      · exact h
      · exact absurd h (hu.2 hu.1)
    have hIspread : I ∈ spreadSet ends φ Sp X (ptype φ (S \ T)) T := by
      unfold spreadSet
      exact mem_filter.2 ⟨mem_image_of_mem _ hxX, inter_subset_right, ptype_le φ hST⟩
    have hvcl : v ∈ sClique ends φ Sp x := hsubx (mem_insert_self v S)
    by_cases hvSp : v ∈ Sp I
    · exact mem_union_left _ (mem_biUnion.2 ⟨T, mem_powerset.2 inter_subset_left,
        mem_biUnion.2 ⟨I, hIspread, hvSp⟩⟩)
    · have hvx : v ∈ ends x := by
        rcases mem_union.1 hvcl with h | h
        · exact h
        · exact absurd h hvSp
      have hTne : T.Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro hT0
        apply hne
        have hSx' : S ⊆ ends x := by rw [hT0, sdiff_empty] at hST; exact hST
        refine eq_of_subset_of_card_le (insert_subset hvx hSx') ?_
        rw [card_insert_of_notMem hvS, hXr x hxX, hS]; omega
      exact mem_union_right _ (mem_biUnion.2 ⟨T, mem_filter.2
        ⟨mem_powerset.2 inter_subset_left, hTne⟩, mem_biUnion.2 ⟨I, hIspread,
          mem_filter.2 ⟨hvU, mem_ptype φ hvx⟩⟩⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add ?_ ?_))
  · refine card_biUnion_le.trans (sum_le_sum fun T hT => ?_)
    have hTS := mem_powerset.1 hT
    have hcardST : (S \ T).card + T.card = r - 1 := by
      rw [card_sdiff_of_subset hTS]; have := card_le_card hTS; omega
    refine card_biUnion_le.trans ?_
    have hterm : ∀ I ∈ spreadSet ends φ Sp X (ptype φ (S \ T)) T, (Sp I).card ≤ q - r := by
      intro I hI
      unfold spreadSet at hI
      obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_filter.1 hI).1
      exact hSpc x hx
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (hspread _ _ (by rw [card_ptype]; exact hcardST))
  · refine card_biUnion_le.trans (sum_le_sum fun T hT => ?_)
    have hTS := mem_powerset.1 (mem_filter.1 hT).1
    have hcardST : (S \ T).card + T.card = r - 1 := by
      rw [card_sdiff_of_subset hTS]; have := card_le_card hTS; omega
    refine card_biUnion_le.trans ?_
    have hterm : ∀ I ∈ spreadSet ends φ Sp X (ptype φ (S \ T)) T,
        (U.filter fun v => φ v ∈ I).card ≤ r * P := by
      intro I hI
      unfold spreadSet at hI
      obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_filter.1 hI).1
      exact card_parts_le hpart (by rw [card_ptype, hXr x hx])
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (hspread _ _ (by rw [card_ptype]; exact hcardST))

end Count

end RefinedAbsorption.Sharp
