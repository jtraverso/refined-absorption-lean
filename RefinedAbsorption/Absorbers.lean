module
public import RefinedAbsorption.Counting

/-!
# Absorbers, omni-absorbers, refinedness, boosters and refiners

Definitions 1.5, 1.6, 1.9, 1.11 and 3.5 of the paper, together with the combinatorial
principles which make them useful:

* `absorption_step`: the final step (4) of the refined absorption proof of the Existence
  Conjecture: a `K_q^r`-packing of `G \ A` covering `G \ (A ∪ X)`, combined with an
  omni-absorber `A` for `X`, yields a `K_q^r`-decomposition of every `K_q^r`-divisible `G`;
* `IsCRefined.card_le`: a `C`-refined omni-absorber has a small decomposition family;
* `booster_swap`: the clique-exchange principle for boosters (Section 1.6).
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {V : Type*} [DecidableEq V]

/-- **Absorber** (Definition 1.5).  For a `K_q^r`-divisible `r`-graph `L`, an `r`-graph `A`
is a `K_q^r`-absorber for `L` if `V(L)` is independent in `A` and both `A` and `A ∪ L` admit
`K_q^r`-decompositions. -/
structure IsAbsorber (q r : ℕ) (L A : Finset (Finset V)) : Prop where
  divisible : IsDivisible q r L
  independent : ∀ e ∈ A, ¬ e ⊆ vertexSet L
  decomp : HasDecomposition q r A
  decomp_union : HasDecomposition q r (A ∪ L)

/-- **Omni-absorber** (Definition 1.6).  An `r`-graph `A` is a `K_q^r`-omni-absorber for an
`r`-graph `X` with decomposition family `F` and decomposition function `QA` if `X` and `A`
are edge-disjoint and for every `K_q^r`-divisible subgraph `L` of `X`, `QA L ⊆ F` is a
`K_q^r`-decomposition of `A ∪ L`. -/
structure IsOmniAbsorber (q r : ℕ) (X A F : Finset (Finset V))
    (QA : Finset (Finset V) → Finset (Finset V)) : Prop where
  rgraph : IsRGraph r X
  disjoint : Disjoint X A
  subset_family : ∀ L ⊆ X, IsDivisible q r L → QA L ⊆ F
  decomp : ∀ L ⊆ X, IsDivisible q r L → IsDecomposition q r (A ∪ L) (QA L)

/-- **`C`-refined** (Definition 1.9).  An omni-absorber `A` for `X` with decomposition family
`F` is `C`-refined if every edge of `X ∪ A` lies in at most `C` elements of `F`. -/
def IsCRefined (C : ℕ) (X A F : Finset (Finset V)) : Prop :=
  ∀ e ∈ X ∪ A, cliqueMult F e ≤ C

/-- **Booster** (Definition 1.11).  A `K_q^r`-booster is an `r`-graph `B` together with two
`K_q^r`-decompositions `Bon`, `Boff` of `B` having no clique in common. -/
structure IsBooster (q r : ℕ) (B Bon Boff : Finset (Finset V)) : Prop where
  on : IsDecomposition q r B Bon
  off : IsDecomposition q r B Boff
  disjoint : Disjoint Bon Boff

/-- **Refiner** (Definition 3.5).  An `r`-graph `R` is a `K_q^r`-refiner of `X` if
`V(X) = V(R)`, `X` and `R` are edge-disjoint, and for every `K_q^r`-divisible `L ⊆ X` there is
a decomposition of `R ∪ L` into `K_q^r`-divisible subgraphs. -/
def IsRefiner (q r : ℕ) (X R : Finset (Finset V)) : Prop :=
  vertexSet X = vertexSet R ∧ Disjoint X R ∧
    ∀ L ⊆ X, IsDivisible q r L → ∃ 𝒲 : Finset (Finset (Finset V)),
      (𝒲 : Set (Finset (Finset V))).PairwiseDisjoint id ∧ 𝒲.sup id = R ∪ L ∧
        ∀ P ∈ 𝒲, IsDivisible q r P

/-! ### Elementary facts about degrees, divisibility and decompositions -/

theorem deg_union_of_disjoint {G H : Finset (Finset V)} (h : Disjoint G H) (S : Finset V) :
    deg (G ∪ H) S = deg G S + deg H S := by
  rw [deg, filter_union, card_union_of_disjoint (disjoint_filter_filter h)]; rfl

theorem isDivisible_empty (q r : ℕ) : IsDivisible q r (∅ : Finset (Finset V)) := by
  intro S _; simp [deg]

/-- If `G ∪ H` (disjoint union) and `H` are divisible then so is `G`. -/
theorem IsDivisible.of_union {q r : ℕ} {G H : Finset (Finset V)} (hGH : Disjoint G H)
    (h : IsDivisible q r (G ∪ H)) (hH : IsDivisible q r H) : IsDivisible q r G := by
  intro S hS
  have := h S hS
  rw [deg_union_of_disjoint hGH] at this
  exact (Nat.dvd_add_left (hH S hS)).1 this

/-- If `G` and `H` are edge-disjoint and divisible, so is `G ∪ H`. -/
theorem IsDivisible.union {q r : ℕ} {G H : Finset (Finset V)} (hGH : Disjoint G H)
    (hG : IsDivisible q r G) (hH : IsDivisible q r H) : IsDivisible q r (G ∪ H) := by
  intro S hS
  rw [deg_union_of_disjoint hGH]
  exact dvd_add (hG S hS) (hH S hS)

theorem IsDecomposition.cliqueEdges_subset {q r : ℕ} {G 𝒬 : Finset (Finset V)}
    (h : IsDecomposition q r G 𝒬) {Q : Finset V} (hQ : Q ∈ 𝒬) : cliqueEdges r Q ⊆ G := by
  intro e he
  rw [cliqueEdges, mem_powersetCard] at he
  have h1 := h.mult_eq e he.2
  have hpos : 0 < cliqueMult 𝒬 e := card_pos.2 ⟨Q, mem_filter.2 ⟨hQ, he.1⟩⟩
  split_ifs at h1 with hG
  · exact hG
  · omega

/-- The union of decompositions of two edge-disjoint `r`-graphs is a decomposition of their
union (for `r ≤ q`). -/
theorem IsDecomposition.union {q r : ℕ} (hrq : r ≤ q) {G H 𝒬 𝒲 : Finset (Finset V)}
    (hGH : Disjoint G H) (hG : IsDecomposition q r G 𝒬) (hH : IsDecomposition q r H 𝒲) :
    IsDecomposition q r (G ∪ H) (𝒬 ∪ 𝒲) := by
  have hdisj : Disjoint 𝒬 𝒲 := by
    rw [disjoint_left]
    intro Q hQ hQ'
    obtain ⟨e, he, hec⟩ := exists_subset_card_eq (s := Q) (n := r) (by rw [hG.card_eq Q hQ]; exact hrq)
    have h1 : e ∈ cliqueEdges r Q := mem_powersetCard.2 ⟨he, hec⟩
    exact disjoint_left.1 hGH (hG.cliqueEdges_subset hQ h1) (hH.cliqueEdges_subset hQ' h1)
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases mem_union.1 he with he | he
    · exact hG.rgraph e he
    · exact hH.rgraph e he
  · intro Q hQ
    rcases mem_union.1 hQ with hQ | hQ
    · exact hG.card_eq Q hQ
    · exact hH.card_eq Q hQ
  · intro e he
    have h1 := hG.mult_eq e he
    have h2 := hH.mult_eq e he
    rw [cliqueMult, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj)]
    rw [cliqueMult] at h1 h2
    rw [h1, h2]
    by_cases heG : e ∈ G
    · have heH : e ∉ H := disjoint_left.1 hGH heG
      simp [heG, heH]
    · by_cases heH : e ∈ H <;> simp [heG, heH]

/-- Removing a clique `S` from a decomposition of `G` gives a decomposition of `G` minus the
edges of `S`. -/
theorem IsDecomposition.erase {q r : ℕ} {G 𝒬 : Finset (Finset V)}
    (h : IsDecomposition q r G 𝒬) {S : Finset V} (hS : S ∈ 𝒬) :
    IsDecomposition q r (G \ cliqueEdges r S) (𝒬.erase S) := by
  refine ⟨fun e he => h.rgraph e (mem_sdiff.1 he).1, fun Q hQ => h.card_eq Q (mem_of_mem_erase hQ),
    fun e he => ?_⟩
  have h1 := h.mult_eq e he
  rw [cliqueMult, filter_erase] at *
  by_cases heS : e ⊆ S
  · have hmem : S ∈ 𝒬.filter (fun Q => e ⊆ Q) := mem_filter.2 ⟨hS, heS⟩
    rw [card_erase_of_mem hmem, h1]
    have heG : e ∈ G := h.cliqueEdges_subset hS (mem_powersetCard.2 ⟨heS, he⟩)
    have : e ∉ G \ cliqueEdges r S := fun h' =>
      (mem_sdiff.1 h').2 (mem_powersetCard.2 ⟨heS, he⟩)
    simp [heG, this]
  · have hmem : S ∉ 𝒬.filter (fun Q => e ⊆ Q) := fun h' => heS (mem_filter.1 h').2
    rw [erase_eq_of_notMem hmem, h1]
    have : e ∉ cliqueEdges r S := fun h' => heS (mem_powersetCard.1 h').1
    simp [mem_sdiff, this]

/-- A `K_q^r`-packing is a `K_q^r`-decomposition of the set of edges it covers. -/
theorem IsPacking.isDecomposition_coveredEdges {q r : ℕ} {G 𝒬 : Finset (Finset V)}
    (h : IsPacking q r G 𝒬) : IsDecomposition q r (coveredEdges r 𝒬) 𝒬 := by
  refine ⟨fun e he => ?_, h.card_eq, fun e he => ?_⟩
  · obtain ⟨Q, -, he⟩ := mem_biUnion.1 he
    exact (mem_powersetCard.1 he).2
  · have h1 := h.mult_le e he
    by_cases hc : e ∈ coveredEdges r 𝒬
    · obtain ⟨Q, hQ, he'⟩ := mem_biUnion.1 hc
      have hpos : 0 < cliqueMult 𝒬 e :=
        card_pos.2 ⟨Q, mem_filter.2 ⟨hQ, (mem_powersetCard.1 he').1⟩⟩
      rw [if_pos hc]; omega
    · rw [if_neg hc, cliqueMult, card_eq_zero, filter_eq_empty_iff]
      intro Q hQ heQ
      exact hc (mem_biUnion.2 ⟨Q, hQ, mem_powersetCard.2 ⟨heQ, he⟩⟩)

theorem IsPacking.coveredEdges_subset {q r : ℕ} {G 𝒬 : Finset (Finset V)}
    (h : IsPacking q r G 𝒬) : coveredEdges r 𝒬 ⊆ G := by
  intro e he
  obtain ⟨Q, hQ, he⟩ := mem_biUnion.1 he
  exact h.sub Q hQ he

/-- An omni-absorber itself admits a `K_q^r`-decomposition (absorb the empty leftover). -/
theorem IsOmniAbsorber.isDecomposition_self {q r : ℕ} {X A F : Finset (Finset V)}
    {QA : Finset (Finset V) → Finset (Finset V)} (h : IsOmniAbsorber q r X A F QA) :
    IsDecomposition q r A (QA ∅) := by
  simpa using h.decomp ∅ (empty_subset _) (isDivisible_empty q r)

/-! ### The absorption step -/

/-- **Absorption step** (step (4) of the refined absorption proof of the Existence Conjecture,
Section 2).  Let `G` be a `K_q^r`-divisible `r`-graph (e.g. `K_n^r`), let `A ⊆ G` where `A`
is a `K_q^r`-omni-absorber for `X`, and let `P` be a `K_q^r`-packing of `G \ A` covering all
edges of `G \ (A ∪ X)`.  Then `G` admits a `K_q^r`-decomposition: the leftover `L ⊆ X` of `P`
is automatically divisible and is absorbed by `A`. -/
theorem absorption_step [Fintype V] {q r : ℕ} (hrq : r ≤ q) {G X A F P : Finset (Finset V)}
    {QA : Finset (Finset V) → Finset (Finset V)} (hG : IsDivisible q r G)
    (hAG : A ⊆ G) (hA : IsOmniAbsorber q r X A F QA)
    (hP : IsPacking q r (G \ A) P) (hcov : G \ (A ∪ X) ⊆ coveredEdges r P) :
    HasDecomposition q r G := by
  set cov := coveredEdges r P
  set L := (G \ A) \ cov with hLdef
  have hcovGA : cov ⊆ G \ A := hP.coveredEdges_subset
  have hLX : L ⊆ X := by
    intro e he
    simp only [hLdef, mem_sdiff] at he
    by_contra hX
    exact he.2 (hcov (mem_sdiff.2 ⟨he.1.1, by simp [he.1.2, hX]⟩))
  have hAL : Disjoint A L := by
    rw [disjoint_left]; intro e heA heL
    exact (mem_sdiff.1 (mem_sdiff.1 heL).1).2 heA
  have hALcov : Disjoint (A ∪ L) cov := by
    rw [disjoint_left]; intro e he hc
    rcases mem_union.1 he with he | he
    · exact (mem_sdiff.1 (hcovGA hc)).2 he
    · exact (mem_sdiff.1 he).2 hc
  have hGeq : G = (A ∪ L) ∪ cov := by
    ext e
    constructor
    · intro he
      by_cases heA : e ∈ A
      · simp [heA]
      · by_cases hc : e ∈ cov
        · simp [hc]
        · simp [hLdef, he, heA, hc]
    · intro he
      rcases mem_union.1 he with he | he
      · rcases mem_union.1 he with he | he
        · exact hAG he
        · exact (mem_sdiff.1 (mem_sdiff.1 he).1).1
      · exact (mem_sdiff.1 (hcovGA he)).1
  have hPdec := hP.isDecomposition_coveredEdges
  have hAdiv : IsDivisible q r A := hA.isDecomposition_self.isDivisible
  have hLdiv : IsDivisible q r L := by
    have h1 : IsDivisible q r (A ∪ L) := by
      rw [hGeq] at hG
      exact hG.of_union hALcov hPdec.isDivisible
    rw [union_comm] at h1
    exact h1.of_union hAL.symm hAdiv
  refine ⟨QA L ∪ P, ?_⟩
  rw [hGeq]
  exact (hA.decomp L hLX hLdiv).union hrq hALcov hPdec

/-! ### Refinedness bounds the size of the decomposition family -/

/-- A `C`-refined omni-absorber has a small decomposition family: if every clique of the
family `F` has all its edges in `X ∪ A`, then `|F| · binom(q, r) ≤ C · e(X ∪ A)`. -/
theorem IsCRefined.card_le {q r C : ℕ} {X A F : Finset (Finset V)}
    (hC : IsCRefined C X A F) (hXA : IsRGraph r (X ∪ A))
    (hF : ∀ Q ∈ F, Q.card = q ∧ cliqueEdges r Q ⊆ X ∪ A) :
    F.card * q.choose r ≤ C * (X ∪ A).card := by
  have hsum : ∑ e ∈ X ∪ A, cliqueMult F e = F.card * q.choose r := by
    simp only [cliqueMult, card_eq_sum_ones, sum_filter]
    rw [sum_comm, sum_mul]
    refine sum_congr rfl fun Q hQ => ?_
    rw [← sum_filter, ← card_eq_sum_ones, one_mul, ← (hF Q hQ).1, ← card_powersetCard]
    congr 1
    ext e
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨he, heQ⟩; exact ⟨heQ, hXA e he⟩
    · rintro ⟨heQ, hc⟩; exact ⟨(hF Q hQ).2 (mem_powersetCard.2 ⟨heQ, hc⟩), heQ⟩
  rw [← hsum, mul_comm C]
  exact sum_le_card_nsmul _ _ _ hC |>.trans (by rw [smul_eq_mul])

/-! ### Boosters -/

/-- In a booster rooted at `S ∈ Boff`, the remaining cliques `Boff \ {S}` decompose `B` minus
the edges of `S`. -/
theorem IsBooster.isDecomposition_off_erase {q r : ℕ} {B Bon Boff : Finset (Finset V)}
    (h : IsBooster q r B Bon Boff) {S : Finset V} (hS : S ∈ Boff) :
    IsDecomposition q r (B \ cliqueEdges r S) (Boff.erase S) :=
  h.off.erase hS

/-- **Booster exchange principle** (Section 1.6).  Let `𝒬` be a `K_q^r`-decomposition of `G`
containing the clique `S`, and let `(B, Bon, Boff)` be a booster rooted at `S ∈ Boff` which is
attached at `S`, i.e. `B \ S` is edge-disjoint from `G`.  Then `G ∪ B` can be decomposed either
by replacing `S` with the cliques of `Bon`, or by keeping `S` and adding `Boff \ {S}`. -/
theorem booster_swap {q r : ℕ} (hrq : r ≤ q) {G 𝒬 B Bon Boff : Finset (Finset V)}
    {S : Finset V} (h𝒬 : IsDecomposition q r G 𝒬) (hS𝒬 : S ∈ 𝒬)
    (hB : IsBooster q r B Bon Boff) (hSB : S ∈ Boff)
    (hdisj : Disjoint G (B \ cliqueEdges r S)) :
    IsDecomposition q r (G ∪ B) ((𝒬.erase S) ∪ Bon) ∧
      IsDecomposition q r (G ∪ B) (𝒬 ∪ Boff.erase S) := by
  have hSG : cliqueEdges r S ⊆ G := h𝒬.cliqueEdges_subset hS𝒬
  have hSB' : cliqueEdges r S ⊆ B := hB.off.cliqueEdges_subset hSB
  constructor
  · have hd : Disjoint (G \ cliqueEdges r S) B := by
      rw [disjoint_left]; intro e he heB
      rw [mem_sdiff] at he
      exact disjoint_left.1 hdisj he.1 (mem_sdiff.2 ⟨heB, he.2⟩)
    have := (h𝒬.erase hS𝒬).union hrq hd hB.on
    convert this using 1
    ext e; simp only [mem_union, mem_sdiff]
    constructor
    · rintro (h | h)
      · by_cases hs : e ∈ cliqueEdges r S
        · exact Or.inr (hSB' hs)
        · exact Or.inl ⟨h, hs⟩
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.1
      · exact Or.inr h
  · have := h𝒬.union hrq hdisj (hB.isDecomposition_off_erase hSB)
    convert this using 1
    ext e; simp only [mem_union, mem_sdiff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hs : e ∈ cliqueEdges r S
        · exact Or.inl (hSG hs)
        · exact Or.inr ⟨h, hs⟩
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.1

end RefinedAbsorption
