module
public import RefinedAbsorption.Dense.Iterate
public import RefinedAbsorption.Placement.Assembly

/-!
# Strong multi-refiners on `K_n^r` with an `o(n)` degree budget

* `stagedRefiner`: the stage lemma, the finite base case and the iteration, combined.
* `topRefiner`: for an `r`-graph `X ⊆ K_n^r` with `(r-1)`-degrees `≤ D` and every `t`, a
  multi-refiner of `X` on `Fin n` whose pieces contain at most one edge of `X` and whose new
  copies have `(r-1)`-degrees `≤ Bd` with `2^t · Bd ≤ 2^t · C_t · D + B · n`.  The refinedness
  constant `C` and `B` do not depend on `t`.  Conditional on placed link refiners at the levels
  `1, …, r - 1`.
* `NativeWeakStrongMultiRefiners q r`: the corresponding strong multi-refiners (the input of the
  final embedding step), with the budget `C_t · D + B · n / 2^t` in place of
  `C · max(D, n^{1-1/r} log n)`.
* **`nativeWeakStrongMultiRefiners_of_levelsA`**, **`nativeWeakStrongMultiRefiners_of_levels`**:
  for every `r ≥ 2`, conditional only on placed link refiners at the intermediate levels
  `1 ≤ i < r - 1` (possibly with a sublinear additive term).  The piece-degree bound is tracked
  through all stages.
* **`nativeWeakStrongMultiRefiners_two`**: proved for `r = 2`.
-/

@[expose] public section

namespace RefinedAbsorption.Dense

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.RefineDown
  RefinedAbsorption.Placement

/-- **Staged refiners inside a reserve**, conditional on placed link refiners. -/
theorem stagedRefiner {q r : ℕ} {a : ℕ → ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hale : ∀ m, a m ≤ m) (hamono : Monotone a)
    (hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelA q r i a) :
    ∃ Cs Cst M C B : ℕ, q + r ≤ Cs ∧ 1 ≤ M ∧ Cst ≤ C ∧ StageProp q r Cs Cst M a ∧
      ∀ t : ℕ, ∃ Ct : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
        (Z : Finset (Fin n)) (X : Finset E) (D : ℕ),
        MIsRGraph r ends X → (∀ x ∈ X, ends x ⊆ Z) → 1 ≤ D →
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends X S ≤ D) →
        ∃ Bd : ℕ, 2 ^ t * Bd ≤ 2 ^ t * Ct * (D + a Z.card) + B * Z.card ∧
          RefinerOut q r C ends Z X Bd := by
  obtain ⟨Cs, Cst, M, hM, hCs, hstage⟩ := multiStage hr hrq hL
  obtain ⟨Cb, Ab, hbase⟩ := baseRefiner q r hr hrq (4 * Cs + 12)
  exact ⟨Cs, Cst, M, Cst + Cb, (Cst + Ab) * M, hCs, hM, by omega, hstage,
    stagedRefiner_of hr hM (by omega) hale hamono hstage hbase⟩

/-- For `r = 2`, the pieces whose vertex set contains a vertex `v` are controlled by the degree
of `v`. -/
theorem pieceDeg_le_of_card_one {V E : Type*} [DecidableEq V] [DecidableEq E] {q r C : ℕ}
    {ends : E → Finset V} {X R Y : Finset E} {𝒲 : Finset (Finset E)}
    (h : IsResidualMultiRefiner q r C ends X R Y 𝒲) {S : Finset V} (hS : S.card = 1) :
    (𝒲.filter fun W => S ⊆ W.biUnion ends).card ≤ C * mdeg ends (X ∪ R) S := by
  obtain ⟨v, rfl⟩ := card_eq_one.1 hS
  have hsub : 𝒲.filter (fun W => {v} ⊆ W.biUnion ends) ⊆
      ((X ∪ R).filter fun c => {v} ⊆ ends c).biUnion fun c => 𝒲.filter fun W => c ∈ W := by
    intro W hW
    obtain ⟨hW𝒲, hvW⟩ := mem_filter.1 hW
    obtain ⟨c, hcW, hvc⟩ := mem_biUnion.1 (hvW (mem_singleton_self v))
    exact mem_biUnion.2 ⟨c, mem_filter.2 ⟨h.subset W hW𝒲 hcW, singleton_subset_iff.2 hvc⟩,
      mem_filter.2 ⟨hW𝒲, hcW⟩⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ c ∈ (X ∪ R).filter (fun c => {v} ⊆ ends c), (𝒲.filter fun W => c ∈ W).card :=
        card_biUnion_le
    _ ≤ ∑ _c ∈ (X ∪ R).filter (fun c => {v} ⊆ ends c), C :=
        sum_le_sum fun c hc => h.mult_le c (mem_filter.1 hc).1
    _ = C * mdeg ends (X ∪ R) {v} := by rw [sum_const, smul_eq_mul, mul_comm]; rfl

set_option maxHeartbeats 1000000 in
/-- **Multi-refiners of `r`-graphs on `Fin n`** with budget `C_t · D + B · n / 2^t`,
conditional on placed link refiners. -/
theorem topRefiner {q r : ℕ} {a : ℕ → ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hale : ∀ m, a m ≤ m) (hamono : Monotone a)
    (hL : ∀ i, 1 ≤ i → i < r → PlacedLinkLevelA q r i a) :
    ∃ C B : ℕ, 1 ≤ C ∧ ∀ t : ℕ, ∃ Ct n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Finset (Fin n)),
      ∀ D : ℕ, IsRGraph r X → 1 ≤ D → (∀ S : Finset (Fin n), S.card = r - 1 → deg X S ≤ D) →
      ∃ (E : Type) (_ : DecidableEq E) (ends : E → Finset (Fin n)) (Xl R : Finset E)
        (𝒲 : Finset (Finset E)) (Bd : ℕ),
        Xl.image ends = X ∧ Set.InjOn ends Xl ∧ 2 ^ t * Bd ≤ 2 ^ t * Ct * (D + a n) + B * n ∧
        IsMultiRefiner q r C ends Xl R 𝒲 ∧ (∀ W ∈ 𝒲, (W.filter (· ∈ Xl)).card ≤ 1) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends Xl S ≤ Bd) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends R S ≤ Bd) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → pdeg ends 𝒲 S ≤ Bd) := by
  obtain ⟨Cs, Cst, M, C, B, hCs, hM, hCstC, hstage, hstaged⟩ :=
    stagedRefiner hr hrq hale hamono hL
  refine ⟨3 * C + 1, B, by omega, fun t => ?_⟩
  obtain ⟨Ct, hCt⟩ := hstaged t
  refine ⟨1 + Cst + Ct * (Cst + 2), 4 * Cs + 12, fun n hn X D hX hD1 hdeg => ?_⟩
  obtain ⟨Z₁, -, hZ₁c⟩ := exists_quarter (univ : Finset (Fin n))
  rw [card_univ, Fintype.card_fin] at hZ₁c
  have hXr : MIsRGraph r (id : Finset (Fin n) → Finset (Fin n)) X := hX
  set D' := D + a n with hD'
  have hDD' : D ≤ D' := Nat.le_add_right _ _
  have haZ₁ : a Z₁.card ≤ a n := hamono (by omega)
  obtain ⟨E₁, _, g₁, ends₁, R₁, Y₁, 𝒲₁, hg₁, hends₁, hR₁f, h₁, hY₁R, hY₁Z, -, -, hdeg₁,
    hone₁, hpd₁⟩ := hstage n id Z₁ univ X D' hXr (fun _ _ => subset_univ _)
      (by rw [card_univ, Fintype.card_fin]; omega) (by omega) (by omega)
      (haZ₁.trans (Nat.le_add_left _ _)) (fun S hS => (hdeg S hS).trans hDD')
  have hY₁r : MIsRGraph r ends₁ Y₁ := fun c hc => h₁.rgraph c (mem_union_right _ (hY₁R hc))
  have hdegY : ∀ S : Finset (Fin n), S.card = r - 1 → mdeg ends₁ Y₁ S ≤ (Cst + 1) * D' :=
    fun S hS => (mdeg_mono _ hY₁R S).trans ((hdeg₁ S hS).trans
      (Nat.mul_le_mul_right _ (by omega)))
  obtain ⟨Bd₂, hBd₂, E₂, _, g₂, ends₂, R₂, 𝒲₂, hg₂, hends₂, hR₂f, h₂, -, hdeg₂, hpd₂⟩ :=
    hCt n ends₁ Z₁ Y₁ ((Cst + 1) * D') hY₁r hY₁Z (by nlinarith) hdegY
  have hpre := IsChainRefiner.prepend_relabel h₁ hY₁R hCstC g₂ hg₂ hends₂ h₂ hR₂f
  have hone := oneX_compose g₂ hg₂ h₁.disjoint hY₁R hone₁ h₂.base hR₂f
  rw [image_image] at hpre hone
  set Bd := D + (Cst * D' + Bd₂) with hBd
  have hendsX : ∀ e, ends₂ ((g₂ ∘ g₁) e) = e := fun e => by simp [hends₂, hends₁]
  refine ⟨E₂, inferInstance, ends₂, X.image (g₂ ∘ g₁), R₁.image g₂ ∪ R₂, _, Bd, ?_, ?_, ?_,
    hpre.base.mono (by omega), hone, ?_, ?_, ?_⟩
  · rw [image_image]
    have : ends₂ ∘ (g₂ ∘ g₁) = id := funext hendsX
    rw [this, image_id]
  · intro a ha b hb hab
    obtain ⟨x, -, rfl⟩ := mem_image.1 (mem_coe.1 ha)
    obtain ⟨y, -, rfl⟩ := mem_image.1 (mem_coe.1 hb)
    rw [hendsX, hendsX] at hab
    rw [hab]
  · have hZ₁n : Z₁.card ≤ n := by omega
    have hD₂ : (Cst + 1) * D' + a Z₁.card ≤ (Cst + 2) * D' := by
      have : a Z₁.card ≤ D' := haZ₁.trans (Nat.le_add_left _ _)
      nlinarith
    have hBd₂' : 2 ^ t * Bd₂ ≤ 2 ^ t * Ct * ((Cst + 2) * D') + B * n :=
      hBd₂.trans (Nat.add_le_add (Nat.mul_le_mul_left _ hD₂) (Nat.mul_le_mul_left _ hZ₁n))
    have e1 : 2 ^ t * Bd = 2 ^ t * D + 2 ^ t * Cst * D' + 2 ^ t * Bd₂ := by rw [hBd]; ring
    have e2 : 2 ^ t * (1 + Cst + Ct * (Cst + 2)) * (D + a n) =
        2 ^ t * D' + 2 ^ t * Cst * D' + 2 ^ t * Ct * ((Cst + 2) * D') := by rw [hD']; ring
    rw [e1, e2]
    have : 2 ^ t * D ≤ 2 ^ t * D' := Nat.mul_le_mul_left _ hDD'
    omega
  · intro S hS
    rw [mdeg_image_eq (A := X) (fun c _ => hendsX c) (hg₂.comp hg₁).injOn subset_rfl]
    exact (hdeg S hS).trans (by omega)
  · intro S hS
    refine (mdeg_union_le _ _ _ S).trans ?_
    rw [mdeg_image_eq (A := R₁) (fun c _ => hends₂ c) hg₂.injOn subset_rfl]
    have := hdeg₁ S hS
    have := hdeg₂ S hS
    omega
  · intro S hS
    refine (pdeg_union_le _ _ _ S).trans ?_
    have := (pdeg_image_le g₂ hends₂ 𝒲₁ S).trans (hpd₁ S hS)
    have := hpd₂ S hS
    omega

/-- **Strong multi-refiners with an `o(n)` budget.**  For `q > r` there are `C ≥ 1` and `B` such
that for every `t` there are `C_t` and `n₀` such that for `n ≥ n₀` every `r`-graph `X ⊆ K_n^r`
with `(r-1)`-degrees `≤ D` (`D ≥ 1`) is the image of the kept part of a strong `C`-refined
multi-refiner on `Fin n` with degree budget `Bd`, where `2^t · Bd ≤ 2^t · C_t · D + B · n`.
(Compare `NativeStrongMultiRefiners`, whose budget is `C · max(D, n^{1-1/r} log n)`.) -/
def NativeWeakStrongMultiRefiners (q r : ℕ) : Prop :=
  ∃ C B : ℕ, 1 ≤ C ∧ ∀ t : ℕ, ∃ Ct n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Finset (Fin n)),
    ∀ D : ℕ, IsRGraph r X → 1 ≤ D → (∀ S : Finset (Fin n), S.card = r - 1 → deg X S ≤ D) →
    ∃ (E : Type) (_ : DecidableEq E) (ends : E → Finset (Fin n)) (K Xl R : Finset E)
      (𝒲 : Finset (Finset E)) (Bd : ℕ),
      Xl.image ends = X ∧ 2 ^ t * Bd ≤ 2 ^ t * Ct * D + B * n ∧
      IsStrongMultiRefiner q r C ends K Xl R 𝒲 Bd

/-- **`NativeWeakStrongMultiRefiners q r` from the intermediate link levels, with an additive
term.**  For `2 ≤ r < q` and a monotone sublinear `a` (`a m ≤ m`, and `k · a m ≤ m` for large `m`,
for every `k`), strong multi-refiners with an `o(n)` budget exist as soon as placed link refiners
with additive term `a |Z|` exist at the levels `1 ≤ i < r - 1` (`PlacedLinkLevelA`; the level
`r - 1` is `placedLinkLevel_last`).  The piece-degree bound `IsStrongMultiRefiner.pieceDeg` is
tracked through every stage of the construction. -/
theorem nativeWeakStrongMultiRefiners_of_levelsA {q r : ℕ} {a : ℕ → ℕ} (hr : 2 ≤ r)
    (hrq : r < q) (hale : ∀ m, a m ≤ m) (hamono : Monotone a)
    (hsub : ∀ k : ℕ, ∃ m₀ : ℕ, ∀ m ≥ m₀, k * a m ≤ m)
    (hL : ∀ i, 1 ≤ i → i < r - 1 → PlacedLinkLevelA q r i a) :
    NativeWeakStrongMultiRefiners q r := by
  obtain ⟨C, B, hC, htop⟩ := topRefiner hr hrq hale hamono (fun i hi hir => by
    rcases Nat.lt_or_ge i (r - 1) with h | h
    · exact hL i hi h
    · obtain rfl : i = r - 1 := by omega
      exact (placedLinkLevel_last q r hr hrq).toA a)
  refine ⟨C, B + 1, hC, fun t => ?_⟩
  obtain ⟨Ct, n₀, h⟩ := htop t
  obtain ⟨m₀, hm₀⟩ := hsub (2 ^ t * Ct)
  refine ⟨Ct, max n₀ m₀, fun n hn X D hX hD1 hdeg => ?_⟩
  obtain ⟨E, _, ends, Xl, R, 𝒲, Bd, hXl, hinj, hBd, href, hone, hdX, hdR, hpd⟩ :=
    h n (le_of_max_le_left hn) X D hX hD1 hdeg
  have ha := hm₀ n (le_of_max_le_right hn)
  have hBd' : 2 ^ t * Bd ≤ 2 ^ t * Ct * D + (B + 1) * n := by
    have e : 2 ^ t * Ct * (D + a n) = 2 ^ t * Ct * D + 2 ^ t * Ct * a n := by ring
    rw [e] at hBd
    nlinarith
  exact ⟨E, inferInstance, ends, Xl, Xl, R, 𝒲, Bd, hXl, hBd',
    { refiner := href
      keep := subset_rfl
      inj := hinj
      oneX := hone
      degX := hdX
      degR := fun S hS => (hdR S hS).trans (Nat.le_mul_of_pos_left _ (by omega))
      pieceDeg := fun S hS => (hpd S hS).trans (Nat.le_mul_of_pos_left _ (by omega)) }⟩

/-- **`NativeWeakStrongMultiRefiners q r` from the intermediate link levels.**  For `2 ≤ r < q`,
strong multi-refiners with an `o(n)` budget exist as soon as placed link refiners exist at the
levels `1 ≤ i < r - 1` (the level `r - 1` is `placedLinkLevel_last`). -/
theorem nativeWeakStrongMultiRefiners_of_levels {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q)
    (hL : ∀ i, 1 ≤ i → i < r - 1 → PlacedLinkLevel q r i) :
    NativeWeakStrongMultiRefiners q r :=
  nativeWeakStrongMultiRefiners_of_levelsA (a := fun _ => 0) hr hrq (fun _ => Nat.zero_le _)
    (fun _ _ _ => le_rfl) (fun _ => ⟨0, fun m _ => by simp⟩) (fun i hi hir => (hL i hi hir).toA _)

/-- **`NativeWeakStrongMultiRefiners q 2` holds**: strong multi-refiners for graphs. -/
theorem nativeWeakStrongMultiRefiners_two {q : ℕ} (hq : 2 < q) :
    NativeWeakStrongMultiRefiners q 2 :=
  nativeWeakStrongMultiRefiners_of_levels le_rfl hq (fun i hi hi2 => by omega)

/-- **`NativeWeakStrongMultiRefiners q 3`** holds as soon as placed link refiners exist at the
single intermediate level `i = 1` (links of single outside vertices, which are graphs). -/
theorem nativeWeakStrongMultiRefiners_three {q : ℕ} (hq : 3 < q)
    (hL : PlacedLinkLevel q 3 1) : NativeWeakStrongMultiRefiners q 3 :=
  nativeWeakStrongMultiRefiners_of_levels (by norm_num) hq (fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact hL)

end RefinedAbsorption.Dense
