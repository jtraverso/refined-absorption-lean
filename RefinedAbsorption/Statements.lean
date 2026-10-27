module
public import RefinedAbsorption.Designs
public import RefinedAbsorption.Absorbers

/-!
# Statements of the main theorems, lemmas and conjectures discussed in the paper

The survey cites a number of deep results (Keevash's theorem, the nibble, the refined efficient
omni-absorber theorem, …) whose proofs span hundreds of pages.  Here they are *stated* as Lean
propositions (`def … : Prop`), so that their precise meaning is fixed; they are **not** proved
in this project.  Where a statement implies another one by a short argument, we prove that
implication (e.g. Theorem 4.5 refutes Conjecture 4.4).

Throughout, the vertex set of `K_n^r` is `Fin n`, and for an `r`-graph `X` the
`(r-1)`-degrees are the numbers `deg X S` for `(r-1)`-sets `S`.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset Filter

/-! ### Auxiliary notions -/

/-- `Δ_{r-1}(X) ≤ D`: every `(r-1)`-set lies in at most `D` edges of `X`. -/
def MaxDegLE {n : ℕ} (r : ℕ) (X : Finset (Finset (Fin n))) (D : ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card + 1 = r → (deg X S : ℝ) ≤ D

/-- `δ_{r-1}(J) ≥ D`: every `(r-1)`-set lies in at least `D` edges of `J`. -/
def MinDegGE {n : ℕ} (r : ℕ) (J : Finset (Finset (Fin n))) (D : ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card + 1 = r → D ≤ (deg J S : ℝ)

/-- `K_q^r(G)`: the copies of `K_q^r` all of whose edges lie in `G`. -/
def cliquesOf {n : ℕ} (q r : ℕ) (G : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (univ.powersetCard q).filter (fun Q => cliqueEdges r Q ⊆ G)

/-- The copies of `K_q^r` in `X ∪ {e}` that contain the edge `e`. -/
def reserveCliques {n : ℕ} (q r : ℕ) (X : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (univ.powersetCard q).filter (fun Q => e ⊆ Q ∧ ∀ f ∈ cliqueEdges r Q, f ≠ e → f ∈ X)

/-- A `(j, i)`-configuration in a family `𝒯` of sets: `i` members of `𝒯` spanning at most `j`
elements. -/
def IsConfiguration {V : Type*} [DecidableEq V] (j i : ℕ) (𝒯 𝒞 : Finset (Finset V)) : Prop :=
  𝒞 ⊆ 𝒯 ∧ 𝒞.card = i ∧ (vertexSet 𝒞).card ≤ j

/-- A `K_q^r`-packing `𝒯` has girth at least `g` if it contains no
`((q-r)i + r, i)`-configuration with `2 ≤ i < g` (Section 5.2). -/
def HasGirthAtLeast {V : Type*} [DecidableEq V] (q r g : ℕ) (𝒯 : Finset (Finset V)) : Prop :=
  ∀ i, 2 ≤ i → i < g → ∀ 𝒞, ¬ IsConfiguration ((q - r) * i + r) i 𝒯 𝒞

/-! ### Section 1: the Existence Conjecture and its ingredients -/

/-- **Conjecture 1.1 (Existence Conjecture)**, proved by Keevash (Theorem 1.2), and again by
Glock–Kühn–Lo–Osthus and by Delcourt–Postle via refined absorption.  For `q > r ≥ 2` and
`λ ≥ 1`, if `n` is large enough and `binom(q-i, r-i) ∣ λ binom(n-i, r-i)` for all
`0 ≤ i ≤ r-1`, then a design with parameters `(n, q, r, λ)` exists. -/
def ExistenceConjecture : Prop :=
  ∀ q r l : ℕ, 2 ≤ r → r < q → 1 ≤ l → ∃ n₀, ∀ n ≥ n₀, DesignDivisibility n q r l →
    ∃ 𝒟 : Finset (Finset (Fin n)), IsDesign q r l 𝒟

/-- **Kirkman's theorem** (1847): an `(n, 3, 2)`-Steiner system (Steiner triple system) exists
whenever `n ≡ 1, 3 (mod 6)`.  (The converse is `IsSteinerSystem.mod_six`.)  This statement
is proved in `RequestProject/Kirkman.lean` (`kirkmanTheorem`). -/
def KirkmanTheorem : Prop :=
  ∀ n : ℕ, (n % 6 = 1 ∨ n % 6 = 3) → ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem 3 2 𝒮

/-- **Theorem 1.3 (Nibble for designs).**  For `q > r ≥ 1` and `β ∈ (0,1)` there is
`α ∈ (0,1)` such that for all large `D`: if `G ⊆ K_n^r` and `H ⊆ K_q^r(G)` are such that every
edge of `G` is in `D(1 ± D^{-β})` cliques of `H` and every pair of edges of `G` is in at most
`D^{1-β}` cliques of `H`, then there is a `K_q^r`-packing of `G` of size at least
`e(G)/binom(q,r) · (1 - D^{-α})`. -/
def NibbleForDesigns : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∀ β : ℝ, 0 < β → β < 1 → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
    ∃ D₀ : ℝ, ∀ D ≥ D₀, ∀ n : ℕ, ∀ G H : Finset (Finset (Fin n)),
      IsRGraph r G → H ⊆ cliquesOf q r G →
      (∀ e ∈ G, |(cliqueMult H e : ℝ) - D| ≤ D ^ (1 - β)) →
      (∀ e ∈ G, ∀ f ∈ G, e ≠ f → (cliqueMult H (e ∪ f) : ℝ) ≤ D ^ (1 - β)) →
      ∃ P, IsPacking q r G P ∧
        (G.card : ℝ) / (q.choose r) * (1 - D ^ (-α)) ≤ P.card

/-- **Theorem 1.7 (existence of absorbers).**  For `q > r ≥ 1`, every `K_q^r`-divisible
`r`-graph `L` has a `K_q^r`-absorber (on a possibly larger vertex set). -/
def AbsorberExistence : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∀ m : ℕ, ∀ L : Finset (Finset (Fin m)),
    IsRGraph r L → IsDivisible q r L →
      ∃ N, ∃ h : m ≤ N, ∃ A : Finset (Finset (Fin N)),
        IsAbsorber q r (L.map (Finset.mapEmbedding (Fin.castLEEmb h)).toEmbedding) A

/-- **Theorem 1.10 (Refined efficient omni-absorber, Delcourt–Postle).**  For `q > r ≥ 1`
there is `C ≥ 1` such that: if `X ⊆ K_n^r` has `Δ_{r-1}(X) ≤ D ≤ n / C`, then there is a
`C`-refined `K_q^r`-omni-absorber `A` for `X` with
`Δ_{r-1}(A) ≤ C · max(D, n^{1-1/r} log n)`.  (Theorem 1.8 is the same statement without
refinedness.)  Not proved here; `RequestProject/OmniFromRefiner.lean` derives it from refined
refiners with attached absorbers (`refinedEfficientOmniAbsorber_of_refinerWithAbsorbers`). -/
def RefinedEfficientOmniAbsorber : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∃ C : ℕ, 1 ≤ C ∧ ∀ n : ℕ, ∀ X : Finset (Finset (Fin n)),
    ∀ D : ℝ, IsRGraph r X → MaxDegLE r X D → D ≤ n / C →
      ∃ A F : Finset (Finset (Fin n)), ∃ QA : Finset (Finset (Fin n)) → Finset (Finset (Fin n)),
        IsOmniAbsorber q r X A F QA ∧ IsCRefined C X A F ∧
          MaxDegLE r A (C * max D ((n : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log n))

/-! ### Section 2: the refined absorption proof of the Existence Conjecture -/

/-- **Lemma 2.1 (Reserves).**  For `q > r ≥ 1` there is `γ ∈ (0,1)` such that for all large
`n` and `p ∈ [n^{-γ}, 1)` there is `X ⊆ K_n^r` with `Δ(X) ≤ 2pn` such that every edge
`e ∉ X` lies in at least `½ p^{binom(q,r)-1} binom(n, q-r)` copies of `K_q^r` in `X ∪ {e}`. -/
def ReservesLemma : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ p : ℝ,
    (n : ℝ) ^ (-γ) ≤ p → p < 1 →
      ∃ X ⊆ completeRGraph (Fin n) r, MaxDegLE r X (2 * p * n) ∧
        ∀ e ∈ completeRGraph (Fin n) r \ X,
          (1 / 2 : ℝ) * p ^ (q.choose r - 1) * (n.choose (q - r)) ≤ (reserveCliques q r X e).card

/-- **Lemma 2.2 (Boost).**  For `q > r ≥ 1` there is `ε ∈ (0,1)` such that for all large `n`:
if `J ⊆ K_n^r` has `δ(J) ≥ (1-ε) n` then there is `H ⊆ K_q^r(J)` such that every edge of `J`
is in `(½ ± n^{-1/3}) binom(n-r, q-r)` cliques of `H`.  (Unlike the other statements here,
this one is proved in this project: `boostLemma` in `RequestProject/Boost.lean`.) -/
def BoostLemma : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ J ⊆ completeRGraph (Fin n) r, MinDegGE r J ((1 - ε) * n) →
      ∃ H ⊆ cliquesOf q r J, ∀ e ∈ J,
        |(cliqueMult H e : ℝ) - (1 / 2) * ((n - r).choose (q - r))|
          ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n - r).choose (q - r))

/-- **Corollary 2.4 (Nibble with reserves for designs).**  For `q > r ≥ 1` and `ρ ∈ (0,1]`
there is `α ∈ (0,1)` such that for all large `n`: let `G ⊆ K_n^r` and `H ⊆ K_q^r(G)` be such
that every edge of `G` is in `(ρ ± n^{-1/3}) binom(n, q-r)` cliques of `H`.  If `X ⊆ K_n^r \ G`
is such that every `e ∈ G` is in at least `n^{q-r-α}` copies of `K_q^r` in `X ∪ {e}`, then there
is a `K_q^r`-packing of `G ∪ X` covering all edges of `G`.  Not proved here;
`RequestProject/NibbleReserves.lean` derives it from the nibble with leftover degree control
(`nibbleWithReserves_of_nibbleLeftoverDegree`). -/
def NibbleWithReserves : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G ⊆ completeRGraph (Fin n) r, ∀ H ⊆ cliquesOf q r G,
      (∀ e ∈ G, |(cliqueMult H e : ℝ) - ρ * (n.choose (q - r))|
          ≤ (n : ℝ) ^ (-(1 / 3 : ℝ)) * (n.choose (q - r))) →
      ∀ X ⊆ completeRGraph (Fin n) r \ G,
        (∀ e ∈ G, (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e).card) →
          ∃ P, IsPacking q r (G ∪ X) P ∧ G ⊆ coveredEdges r P

/-! ### Section 4: Nash-Williams' Conjecture -/

/-- **Conjecture 4.1 (Nash-Williams).**  For large `n`, every `K_3`-divisible graph on `n`
vertices with minimum degree at least `3n/4` has a `K_3`-decomposition. -/
def NashWilliamsConjecture : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : Finset (Finset (Fin n)), IsRGraph 2 G → IsDivisible 3 2 G →
    (∀ v : Fin n, (3 / 4 : ℝ) * n ≤ deg G {v}) → HasDecomposition 3 2 G

/-- **Conjecture 4.4 (folklore).**  For `q ≥ 4` and large `n`, every `K_q`-divisible graph on
`n` vertices with minimum degree at least `(1 - 1/(q+1)) n` has a `K_q`-decomposition.
(Refuted by Delcourt, Henderson, Lesgourgues and Postle, see `FractionalCounterexamples`.) -/
def FolkloreCliqueConjecture : Prop :=
  ∀ q : ℕ, 4 ≤ q → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : Finset (Finset (Fin n)), IsRGraph 2 G →
    IsDivisible q 2 G → (∀ v : Fin n, (1 - 1 / ((q : ℝ) + 1)) * n ≤ deg G {v}) →
      HasDecomposition q 2 G

/-- **Theorem 4.5 (Delcourt, Henderson, Lesgourgues, Postle).**  For every `q ≥ 4` there are
`c > 1` and infinitely many `K_q`-divisible graphs `G` with
`δ(G) ≥ (1 - 1/(c(q+1))) v(G)` and no fractional `K_q`-decomposition. -/
def FractionalCounterexamples : Prop :=
  ∀ q : ℕ, 4 ≤ q → ∃ c : ℝ, 1 < c ∧ ∀ N : ℕ, ∃ n ≥ N, ∃ G : Finset (Finset (Fin n)),
    IsRGraph 2 G ∧ IsDivisible q 2 G ∧
      (∀ v : Fin n, (1 - 1 / (c * ((q : ℝ) + 1))) * n ≤ deg G {v}) ∧
      ¬ HasFractionalDecomposition q 2 G

/-- Theorem 4.5 refutes Conjecture 4.4 (and even its fractional relaxation), since a
decomposition is in particular a fractional decomposition. -/
theorem not_folkloreCliqueConjecture (h : FractionalCounterexamples) :
    ¬ FolkloreCliqueConjecture := by
  intro hc
  obtain ⟨c, hc1, hG⟩ := h 4 le_rfl
  obtain ⟨n₀, hn₀⟩ := hc 4 le_rfl
  obtain ⟨n, hn, G, hG2, hdiv, hdeg, hfrac⟩ := hG n₀
  refine hfrac (HasDecomposition.hasFractionalDecomposition (hn₀ n hn G hG2 hdiv fun v => ?_))
  refine le_trans ?_ (hdeg v)
  gcongr
  have h5 : (0 : ℝ) < 4 + 1 := by norm_num
  push_cast
  nlinarith

/-! ### Section 5: high girth Steiner systems -/

/-- **Conjecture 5.1 (Erdős)**, proved by Kwan, Sah, Sawhney and Simkin (Theorem 5.2).  For
every `g ≥ 3`, every sufficiently large `K_3`-divisible complete graph has a
`K_3`-decomposition of girth at least `g`. -/
def ErdosHighGirthConjecture : Prop :=
  ∀ g : ℕ, 3 ≤ g → ∃ n₀ : ℕ, ∀ n ≥ n₀, IsDivisible 3 2 (completeRGraph (Fin n) 2) →
    ∃ 𝒮, IsDecomposition 3 2 (completeRGraph (Fin n) 2) 𝒮 ∧ HasGirthAtLeast 3 2 g 𝒮

/-- **Conjecture 5.3 (High Girth Existence)**, proved by Delcourt and Postle (Theorem 5.4).
For `q > r ≥ 2` and `g ≥ 3`, every sufficiently large `K_q^r`-divisible complete `r`-graph has
a `K_q^r`-decomposition of girth at least `g`. -/
def HighGirthExistenceConjecture : Prop :=
  ∀ q r g : ℕ, 2 ≤ r → r < q → 3 ≤ g → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    IsDivisible q r (completeRGraph (Fin n) r) →
      ∃ 𝒮, IsDecomposition q r (completeRGraph (Fin n) r) 𝒮 ∧ HasGirthAtLeast q r g 𝒮

/-- **Conjecture 5.8 ("Erdős meets Nash-Williams", Glock–Kühn–Osthus).**  For every `g` and
large `n`, every `K_3`-divisible graph on `n` vertices with `δ(G) ≥ 3n/4` has a
`K_3`-decomposition of girth at least `g`. -/
def ErdosMeetsNashWilliamsConjecture : Prop :=
  ∀ g : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : Finset (Finset (Fin n)), IsRGraph 2 G →
    IsDivisible 3 2 G → (∀ v : Fin n, (3 / 4 : ℝ) * n ≤ deg G {v}) →
      ∃ 𝒮, IsDecomposition 3 2 G 𝒮 ∧ HasGirthAtLeast 3 2 g 𝒮

/-- The high girth version of Nash-Williams' conjecture implies Nash-Williams' conjecture. -/
theorem nashWilliams_of_erdosMeetsNashWilliams (h : ErdosMeetsNashWilliamsConjecture) :
    NashWilliamsConjecture := by
  obtain ⟨n₀, hn₀⟩ := h 0
  exact ⟨n₀, fun n hn G hG hdiv hdeg => (hn₀ n hn G hG hdiv hdeg).elim fun 𝒮 h => ⟨𝒮, h.1⟩⟩

/-- Erdős' conjecture is the case `q = 3`, `r = 2` of the High Girth Existence Conjecture. -/
theorem erdos_of_highGirthExistence (h : HighGirthExistenceConjecture) :
    ErdosHighGirthConjecture := fun g hg => h 3 2 g le_rfl (by norm_num) hg

/-! ### Section 6: thresholds for Steiner systems -/

/-- The probability that the binomial random `q`-graph `G^{(q)}(n, p)` has property `P`. -/
noncomputable def randomHypergraphProb (n q : ℕ) (p : ℝ)
    (P : Finset (Finset (Fin n)) → Prop) [DecidablePred P] : ℝ :=
  ∑ H ∈ ((univ : Finset (Fin n)).powersetCard q).powerset.filter P,
    p ^ H.card * (1 - p) ^ ((n.choose q) - H.card)

open Classical in
/-- **Conjecture 6.2 (Kang, Kelly, Kühn, Methuku, Osthus).**  For `q > r ≥ 1`, if
`p = ω(n^{-(q-r)} log n)` then a.a.s. (along the `n` satisfying the divisibility conditions)
`G^{(q)}(n, p)` contains an `(n, q, r)`-Steiner system. -/
def SteinerThresholdConjecture : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∀ p : ℕ → ℝ, (∀ n, 0 ≤ p n ∧ p n ≤ 1) →
    Tendsto (fun n : ℕ => p n / ((n : ℝ) ^ (-((q : ℝ) - r)) * Real.log n)) atTop atTop →
    Tendsto (fun n : ℕ => randomHypergraphProb n q (p n)
        (fun H => ∃ 𝒮 ⊆ H, IsSteinerSystem q r 𝒮))
      (atTop ⊓ 𝓟 {n | DesignDivisibility n q r 1}) (nhds 1)

end RefinedAbsorption
