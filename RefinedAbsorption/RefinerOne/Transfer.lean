module
public import RefinedAbsorption.RefinerOne.Chain
public import RefinedAbsorption.RefinerReductions

/-!
# The chain refiner on an arbitrary vertex type

We transport the label-level chain construction along a map `g : Lab → V` which is injective on
the labels used, and obtain a refined `K_q^1`-refiner (with empty attached absorbers, since all
pieces are single copies of `K_q^1`).
-/

@[expose] public section

namespace RefinedAbsorption.ChainRefiner

open Finset

variable {V : Type*} [DecidableEq V]

/-- The `1`-graph whose edges are the singletons of `S`. -/
def sing (S : Finset V) : Finset (Finset V) := S.image (fun a => {a})

lemma mem_sing {S : Finset V} {e : Finset V} : e ∈ sing S ↔ ∃ a ∈ S, {a} = e := by
  simp [sing]

lemma singleton_mem_sing {S : Finset V} {a : V} : {a} ∈ sing S ↔ a ∈ S := by
  simp [sing]

lemma card_sing (S : Finset V) : (sing S).card = S.card :=
  card_image_of_injective _ (fun _ _ h => singleton_injective h)

lemma sing_union (S T : Finset V) : sing (S ∪ T) = sing S ∪ sing T := image_union _ _

lemma sing_mono {S T : Finset V} (h : S ⊆ T) : sing S ⊆ sing T := image_subset_image h

lemma isRGraph_sing (S : Finset V) : IsRGraph 1 (sing S) := by
  intro e he
  obtain ⟨a, -, rfl⟩ := mem_sing.1 he
  simp

lemma deg_empty (G : Finset (Finset V)) : deg G ∅ = G.card := by
  simp [deg]

/-- A `1`-graph of size `0` or `q` has a `K_q^1`-decomposition. -/
lemma hasDecomposition_sing {q : ℕ} {S : Finset V} (hS : S.card = 0 ∨ S.card = q) :
    HasDecomposition q 1 (sing S) := by
  rcases hS with h | h
  · rw [card_eq_zero] at h
    subst h
    exact ⟨∅, by simp [IsRGraph, sing], by simp, fun e _ => by simp [cliqueMult, sing]⟩
  · refine ⟨{S}, isRGraph_sing S, fun Q hQ => by rw [mem_singleton.1 hQ, h], ?_⟩
    intro e he
    obtain ⟨a, rfl⟩ := card_eq_one.1 he
    simp only [cliqueMult, singleton_mem_sing]
    by_cases ha : a ∈ S
    · simp [ha, filter_singleton]
    · simp [ha, filter_singleton]

/-- A `1`-graph of size `0` or `q` is `K_q^1`-divisible. -/
lemma isDivisible_sing {q : ℕ} {S : Finset V} (hS : S.card = 0 ∨ S.card = q) :
    IsDivisible q 1 (sing S) := by
  intro T hT
  have hT' : T = ∅ := by
    rw [← card_eq_zero]; exact Nat.lt_one_iff.1 hT
  subst hT'
  rw [deg_empty, card_sing]
  simp only [card_empty, Nat.sub_zero, Nat.choose_one_right]
  rcases hS with h | h <;> rw [h]
  · exact dvd_zero q

section Transport

variable (q m : ℕ) (g : Lab → V)

/-- The input `1`-graph. -/
def Xg : Finset (Finset V) := sing ((Xlab m).image g)

/-- The refiner `1`-graph. -/
def Rg : Finset (Finset V) := sing ((Rlab q m).image g)

/-- The `1`-graph of a piece. -/
def Wpiece (x : ℕ × ℕ × Bool) : Finset (Finset V) :=
  sing ((piece q x.1 x.2.1 x.2.2).image g)

/-- The `1`-graph of the final piece. -/
def Wfin : Finset (Finset V) := sing ((finPiece q m).image g)

/-- The family of all pieces. -/
def 𝒲g : Finset (Finset (Finset V)) := (Idx q m).image (Wpiece q g) ∪ {Wfin q m g}

end Transport

variable {q m : ℕ} {g : Lab → V}

lemma mem_image_iff_of_injOn (hg : Set.InjOn g (Ulab q m)) {P : Finset Lab}
    (hP : P ⊆ Ulab q m) {a : Lab} (ha : a ∈ Ulab q m) : g a ∈ P.image g ↔ a ∈ P := by
  constructor
  · intro h
    obtain ⟨b, hb, hba⟩ := mem_image.1 h
    rwa [← hg (hP hb) ha hba]
  · exact mem_image_of_mem g

lemma piece_subset_U (hq : 1 ≤ q) {x : ℕ × ℕ × Bool} (hx : x ∈ Idx q m) :
    piece q x.1 x.2.1 x.2.2 ⊆ Ulab q m := by
  simp only [Idx, mem_product, mem_range, mem_univ, and_true] at hx
  exact (piece_subset hq hx.1 hx.2).trans (Rlab_union_Xlab_subset hq)

lemma finPiece_subset_U (hq : 1 ≤ q) : finPiece q m ⊆ Ulab q m :=
  (finPiece_subset hq).trans (Rlab_union_Xlab_subset hq)

lemma card_piece_cases (hq : 1 ≤ q) {x : ℕ × ℕ × Bool} (hx : x ∈ Idx q m) :
    (piece q x.1 x.2.1 x.2.2).card = 0 ∨ (piece q x.1 x.2.1 x.2.2).card = q := by
  simp only [Idx, mem_product, mem_range, mem_univ, and_true] at hx
  rw [card_piece hq hx.2]
  split_ifs <;> simp

lemma card_finPiece_cases (hq : 1 ≤ q) :
    (finPiece q m).card = 0 ∨ (finPiece q m).card = q := by
  rw [card_finPiece hq]
  split_ifs <;> simp

lemma card_image_cases (hg : Set.InjOn g (Ulab q m)) {P : Finset Lab} (hP : P ⊆ Ulab q m)
    (h : P.card = 0 ∨ P.card = q) : (P.image g).card = 0 ∨ (P.image g).card = q := by
  rwa [card_image_of_injOn (hg.mono (by exact_mod_cast hP))]

/-- Every member of the family is a piece of size `0` or `q` inside the used labels. -/
lemma mem_𝒲g {W : Finset (Finset V)} (hW : W ∈ 𝒲g q m g) :
    ∃ P : Finset Lab, W = sing (P.image g) ∧
      (P = finPiece q m ∨ ∃ x ∈ Idx q m, P = piece q x.1 x.2.1 x.2.2) := by
  simp only [𝒲g, mem_union, mem_image, mem_singleton] at hW
  rcases hW with ⟨x, hx, rfl⟩ | rfl
  · exact ⟨_, rfl, Or.inr ⟨x, hx, rfl⟩⟩
  · exact ⟨_, rfl, Or.inl rfl⟩

lemma mem_𝒲g' (hq : 1 ≤ q) (hg : Set.InjOn g (Ulab q m)) {W : Finset (Finset V)}
    (hW : W ∈ 𝒲g q m g) :
    ∃ P : Finset Lab, W = sing (P.image g) ∧ P ⊆ Rlab q m ∪ Xlab m ∧ P.card ≤ q ∧
      ((P.image g).card = 0 ∨ (P.image g).card = q) := by
  obtain ⟨P, rfl, hP⟩ := mem_𝒲g hW
  rcases hP with rfl | ⟨x, hx, rfl⟩
  · refine ⟨_, rfl, finPiece_subset hq, ?_, card_image_cases hg (finPiece_subset_U hq)
      (card_finPiece_cases hq)⟩
    rcases card_finPiece_cases (m := m) hq with h | h <;> omega
  · have hx' := hx
    simp only [Idx, mem_product, mem_range, mem_univ, and_true] at hx'
    refine ⟨_, rfl, piece_subset hq hx'.1 hx'.2, ?_,
      card_image_cases hg (piece_subset_U hq hx) (card_piece_cases hq hx)⟩
    rcases card_piece_cases hq hx with h | h <;> omega

/-- **The chain refiner.** -/
theorem chain_isRefinedRefiner (hq : 1 ≤ q) (hg : Set.InjOn g (Ulab q m)) {C : ℕ}
    (hC : 4 * q + 1 ≤ C) :
    IsRefinedRefiner q 1 C (Xg m g) (Rg q m g) (𝒲g q m g) := by
  have hU := Rlab_union_Xlab_subset (m := m) hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `1`-graph
    intro e he
    rcases mem_union.1 he with he | he <;> exact isRGraph_sing _ e he
  · -- disjointness
    rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨a, ha, rfl⟩ := mem_sing.1 he
    obtain ⟨l, hl, rfl⟩ := mem_image.1 ha
    rw [Xg, Rg, singleton_mem_sing,
      mem_image_iff_of_injOn hg (Rlab_subset_Ulab hq) (Xlab_subset_Ulab hl)] at *
    rcases lab_cases l with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
    · exact not_mem_Rlab_xl he'
    · exact not_mem_Xlab_zl hl
  · intro W hW
    obtain ⟨P, rfl, -, -, hc⟩ := mem_𝒲g' hq hg hW
    exact isDivisible_sing hc
  · intro W hW
    obtain ⟨P, rfl, hP, -, -⟩ := mem_𝒲g' hq hg hW
    rw [Xg, Rg, ← sing_union, ← image_union]
    exact sing_mono (image_subset_image (hP.trans (by rw [union_comm])))
  · intro W hW
    obtain ⟨P, rfl, -, hcard, -⟩ := mem_𝒲g' hq hg hW
    rw [card_sing]
    exact card_image_le.trans (hcard.trans (by omega))
  · -- multiplicity
    intro e he
    rw [Xg, Rg, ← sing_union, ← image_union] at he
    obtain ⟨a, ha, rfl⟩ := mem_sing.1 he
    obtain ⟨l, hl, rfl⟩ := mem_image.1 ha
    have hlU : l ∈ Ulab q m := by
      apply Rlab_union_Xlab_subset hq
      rcases mem_union.1 hl with h | h
      · exact mem_union_right _ h
      · exact mem_union_left _ h
    calc ((𝒲g q m g).filter (fun W => {g l} ∈ W)).card
        ≤ (((Idx q m).filter (fun x => l ∈ piece q x.1 x.2.1 x.2.2)).image (Wpiece q g) ∪
            {Wfin q m g}).card := by
          apply card_le_card
          intro W hW
          rw [mem_filter] at hW
          simp only [𝒲g, mem_union, mem_image, mem_singleton] at hW
          rcases hW with ⟨⟨x, hx, rfl⟩ | rfl, hmem⟩
          · rw [Wpiece, singleton_mem_sing,
              mem_image_iff_of_injOn hg (piece_subset_U hq hx) hlU] at hmem
            exact mem_union_left _ (mem_image_of_mem _ (mem_filter.2 ⟨hx, hmem⟩))
          · exact mem_union_right _ (mem_singleton_self _)
      _ ≤ _ + 1 := card_union_le _ _
      _ ≤ 4 * q + 1 := by
          gcongr
          exact card_image_le.trans (card_filter_piece_le q m l)
      _ ≤ C := hC
  · -- decomposition
    intro L hL hLdiv
    classical
    set b : ℕ → Bool := fun i => decide ({g (xl i)} ∈ L) with hb
    have hLeq : L = sing ((Llab b m).image g) := by
      ext e
      constructor
      · intro he
        obtain ⟨a, ha, rfl⟩ := mem_sing.1 (hL he)
        obtain ⟨l, hl, rfl⟩ := mem_image.1 ha
        obtain ⟨k, hk, rfl⟩ := mem_image.1 hl
        rw [singleton_mem_sing]
        refine mem_image_of_mem _ (mem_Llab_xl.2 ⟨mem_range.1 hk, ?_⟩)
        simpa [hb] using he
      · intro he
        obtain ⟨a, ha, rfl⟩ := mem_sing.1 he
        obtain ⟨l, hl, rfl⟩ := mem_image.1 ha
        obtain ⟨k, hk, rfl⟩ := mem_image.1 hl
        rw [mem_filter] at hk
        simpa [hb] using hk.2
    have hLsub : Llab b m ⊆ Ulab q m := by
      intro l hl
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hl
      exact mem_Ulab_xl.2 (mem_range.1 (mem_filter.1 hk).1)
    have hdiv : q ∣ cnt b m := by
      have h := hLdiv ∅ (by simp)
      simp only [card_empty, Nat.sub_zero, Nat.choose_one_right, deg_empty] at h
      rwa [cnt_eq_card, ← card_image_of_injOn (hg.mono (by exact_mod_cast hLsub)),
        ← card_sing, ← hLeq]
    have hch : ∀ i < m, chosen q b i ⊆ Ulab q m := fun i hi =>
      piece_subset_U hq (x := (i, tSeq q b i, b i)) (by
        simp [Idx, hi, tSeq_lt hq])
    refine ⟨(range m).image (fun i => sing ((chosen q b i).image g)) ∪ {Wfin q m g},
      ?_, ?_, ?_⟩
    · intro W hW
      simp only [mem_union, mem_image, mem_range, mem_singleton] at hW
      rcases hW with ⟨i, hi, rfl⟩ | rfl
      · refine mem_union_left _ (mem_image.2 ⟨(i, tSeq q b i, b i), ?_, rfl⟩)
        simp [Idx, hi, tSeq_lt hq]
      · exact mem_union_right _ (mem_singleton_self _)
    · intro W hW W' hW' hne
      simp only [coe_union, coe_image, coe_range, coe_singleton, Set.mem_union, Set.mem_image,
        Set.mem_Iio, Set.mem_singleton_iff] at hW hW'
      simp only [Function.onFun, id]
      rw [Finset.disjoint_left]
      intro e he he'
      apply hne
      rcases hW with ⟨i, hi, rfl⟩ | rfl <;> rcases hW' with ⟨i', hi', rfl⟩ | rfl
      · obtain ⟨a, ha, rfl⟩ := mem_sing.1 he
        obtain ⟨l, hl, rfl⟩ := mem_image.1 ha
        rw [singleton_mem_sing, mem_image_iff_of_injOn hg (hch i' hi') (hch i hi hl)] at he'
        rw [chosen_unique hl he']
      · obtain ⟨a, ha, rfl⟩ := mem_sing.1 he
        obtain ⟨l, hl, rfl⟩ := mem_image.1 ha
        rw [Wfin, singleton_mem_sing,
          mem_image_iff_of_injOn hg (finPiece_subset_U hq) (hch i hi hl)] at he'
        exact absurd he' (chosen_not_fin hq hdiv hi hl)
      · obtain ⟨a, ha, rfl⟩ := mem_sing.1 he'
        obtain ⟨l, hl, rfl⟩ := mem_image.1 ha
        rw [Wfin, singleton_mem_sing,
          mem_image_iff_of_injOn hg (finPiece_subset_U hq) (hch i' hi' hl)] at he
        exact absurd he (chosen_not_fin hq hdiv hi' hl)
      · rfl
    · rw [hLeq, Rg, ← sing_union, ← image_union]
      ext e
      simp only [mem_sup, mem_union, mem_image, mem_range, mem_singleton, id]
      constructor
      · rintro ⟨W, hW, he⟩
        rcases hW with ⟨i, hi, rfl⟩ | rfl
        · obtain ⟨a, ha, rfl⟩ := mem_sing.1 he
          obtain ⟨l, hl, rfl⟩ := mem_image.1 ha
          rw [singleton_mem_sing]
          exact mem_image_of_mem _ ((cover hq b m hdiv l).1 (Or.inl ⟨i, hi, hl⟩))
        · obtain ⟨a, ha, rfl⟩ := mem_sing.1 he
          obtain ⟨l, hl, rfl⟩ := mem_image.1 ha
          rw [singleton_mem_sing]
          exact mem_image_of_mem _ ((cover hq b m hdiv l).1 (Or.inr hl))
      · intro he
        obtain ⟨a, ha, rfl⟩ := mem_sing.1 he
        obtain ⟨l, hl, rfl⟩ := mem_image.1 ha
        rcases (cover hq b m hdiv l).2 hl with ⟨i, hi, hli⟩ | hli
        · exact ⟨_, Or.inl ⟨i, hi, rfl⟩, singleton_mem_sing.2 (mem_image_of_mem _ hli)⟩
        · exact ⟨_, Or.inr rfl, singleton_mem_sing.2 (mem_image_of_mem _ hli)⟩

/-- Every member of the chain family has a `K_q^1`-decomposition. -/
theorem chain_hasDecomposition (hq : 1 ≤ q) (hg : Set.InjOn g (Ulab q m))
    {W : Finset (Finset V)} (hW : W ∈ 𝒲g q m g) : HasDecomposition q 1 W := by
  obtain ⟨P, rfl, -, -, hc⟩ := mem_𝒲g' hq hg hW
  exact hasDecomposition_sing hc

lemma card_Rg_le (hq : 1 ≤ q) : (Rg q m g).card ≤ (m + 2) * (q - 1) := by
  rw [Rg, card_sing]
  exact card_image_le.trans (card_Rlab_le hq)

end RefinedAbsorption.ChainRefiner
