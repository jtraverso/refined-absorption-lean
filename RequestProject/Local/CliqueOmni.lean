module
public import RequestProject.Local.LevelOneSharp

/-!
# Flat local refiners from flat clique omni-absorbers for graphs

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, Theorem 3.7 (Refined Multi-Omni-Absorber
Theorem, with the flatness conclusion (2)) for graphs, and Remark 3.9 (the pieces of an
omni-absorber are cliques `K_q`).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

`FlatCliqueOmniAbsorbers q a` is the local form of Theorem 3.7 for graphs that the proof of
Theorem 4.4 uses: every multigraph `L` of bounded multiplicity inside `Y`, with vertex degrees
`≤ d`, has, for every set `P` of new vertices disjoint from `Y` with `|Y| ≤ K |P|`, a complete
`K_q^2`-multi-refiner inside `Y ∪ P` such that

* every new copy meets `P` (flatness, Theorem 3.7 (2));
* the new copies have vertex degrees `≤ C (d + a |P|)` and multiplicities `≤ C`
  (Theorem 3.7 (1));
* every piece is a clique: any two distinct vertices of the span of a piece carry a copy of the
  piece (Remark 3.9).

**`flatGraphRefiners_of_cliqueOmni`**: such clique omni-absorbers are flat local refiners
(`FlatGraphRefiners`); the pair bound and the rooting of the pieces at old copies follow from the
clique property and flatness.

**`nativeStrongMultiRefiners_three_of_cliqueOmni`**: Theorem 3.8 for `3`-graphs (strong
multi-refiners with budget `C · max(D, n^{2/3} log n)`) from flat clique omni-absorbers for graphs
with an additive term dominated by `sharpCost 3`; **`nativeStrongMultiRefiners_three_of_cliqueOmni_two`**
is the case of the additive term `sharpCost 2 m = ⌈m^{1/2}⌉ (⌊log₂ m⌋ + 1)` of Theorem 3.7 for
graphs.
-/

@[expose] public section

namespace RefinedAbsorption.Local

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown RefinedAbsorption.LinkSpread RefinedAbsorption.Sharp
  RefinedAbsorption.Window

/-- **Flat clique omni-absorbers for graphs** (Theorem 3.7 for `r = 2`, local form; see the module
docstring). -/
def FlatCliqueOmniAbsorbers (q : ℕ) (a : ℕ → ℕ) : Prop :=
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
      (∀ W ∈ 𝒲, ∀ x ∈ W.biUnion ends', ∀ y ∈ W.biUnion ends', x ≠ y →
        ∃ c ∈ W, ends' c = {x, y})

/-- The pieces containing a copy on `e` are at most `C` times the multiplicity of `e`. -/
theorem card_pieces_through_le {V E : Type*} [DecidableEq V] [DecidableEq E] {q r C : ℕ}
    {ends : E → Finset V} {X R Y : Finset E} {𝒲 : Finset (Finset E)}
    (h : IsResidualMultiRefiner q r C ends X R Y 𝒲) (P : Finset E → Prop) [DecidablePred P]
    (e : Finset V) (hP : ∀ W ∈ 𝒲, P W → ∃ c ∈ W, ends c = e) :
    (𝒲.filter P).card ≤ C * (mult ends X e + mult ends R e) := by
  refine (card_le_card ?_).trans ((card_biUnion_le (s := (X ∪ R).filter fun c => ends c = e)
    (t := fun c => 𝒲.filter fun W => c ∈ W)).trans ?_)
  · intro W hW
    obtain ⟨hW, hPW⟩ := mem_filter.1 hW
    obtain ⟨c, hcW, hce⟩ := hP W hW hPW
    exact mem_biUnion.2 ⟨c, mem_filter.2 ⟨h.subset W hW hcW, hce⟩, mem_filter.2 ⟨hW, hcW⟩⟩
  · refine (sum_le_sum fun c hc => h.mult_le c (mem_filter.1 hc).1).trans ?_
    rw [sum_const, smul_eq_mul, mul_comm, filter_union,
      card_union_of_disjoint (disjoint_filter_filter h.disjoint)]
    rfl

/-- **Flat clique omni-absorbers are flat local refiners.** -/
theorem flatGraphRefiners_of_cliqueOmni {q : ℕ} {a : ℕ → ℕ} (h : FlatCliqueOmniAbsorbers q a) :
    FlatGraphRefiners q a := by
  intro K
  obtain ⟨C, Ch, hC⟩ := h K
  refine ⟨C * (K + C) + C, Ch, ?_⟩
  intro n E _ ends Y P L d hYP hYK hCh hLr hLY hdeg hmult
  obtain ⟨E', _, g, ends', R, 𝒲, hg, hge, hfr, href, hflat, hdegR, hmultR, hclique⟩ :=
    hC n ends Y P L d hYP hYK hCh hLr hLY hdeg hmult
  have hCC : C ≤ C * (K + C) + C := Nat.le_add_left _ _
  refine ⟨E', inferInstance, g, ends', R, 𝒲, hg, hge, hfr, href.mono hCC, hflat,
    fun v => (hdegR v).trans (Nat.mul_le_mul_right _ hCC), fun e => (hmultR e).trans hCC,
    fun x y hxy => ?_, fun W hW x hx y hy hxy hxW hyW => ?_⟩
  · -- pairs: a piece spanning `x, y` contains a copy on `{x, y}`
    refine (card_pieces_through_le href (fun W => x ∈ W.biUnion ends' ∧ y ∈ W.biUnion ends')
      {x, y} fun W hW hxyW => hclique W hW x hxyW.1 y hxyW.2 hxy).trans ?_
    have h1 := (mult_image_le (fun c _ => hge c) {x, y}).trans (hmult {x, y})
    have h2 := hmultR {x, y}
    calc C * (mult ends' (L.image g) {x, y} + mult ends' R {x, y}) ≤ C * (K + C) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := Nat.le_add_right _ _
  · obtain ⟨c, hcW, hc⟩ := hclique W hW x hxW y hyW hxy
    refine ⟨c, hcW, ?_, hc⟩
    rcases mem_union.1 (href.subset W hW hcW) with hcL | hcR
    · exact hcL
    · exfalso
      obtain ⟨z, hz⟩ := (hflat c hcR).2
      rw [hc] at hz
      obtain ⟨hz1, hz2⟩ := mem_inter.1 hz
      have hzY : z ∈ Y := by
        rcases mem_insert.1 hz1 with rfl | h
        · exact hx
        · rw [mem_singleton] at h; rw [h]; exact hy
      exact disjoint_left.1 hYP hzY hz2

/-- **Theorem 3.8 for `3`-graphs from flat clique omni-absorbers for graphs** (Theorem 3.7 for
`r = 2` with flatness, local form).  Strong multi-refiners with budget `C · max(D, n^{2/3} log n)`
exist for `3`-graphs as soon as flat clique omni-absorbers exist in uniformity `2` with an
additive term dominated by `sharpCost 3`. -/
theorem nativeStrongMultiRefiners_three_of_cliqueOmni {q : ℕ} (hq : 3 < q) (a : ℕ → ℕ)
    (hF : FlatCliqueOmniAbsorbers (q - 1) a) (ha : ∀ m m', m ≤ m' → a m ≤ sharpCost 3 m') :
    NativeStrongMultiRefiners q 3 :=
  nativeStrongMultiRefiners_three_of_flat hq a (flatGraphRefiners_of_cliqueOmni hF) ha

/-- The sharp cost of graphs is dominated by the sharp cost of `3`-graphs. -/
theorem sharpCost_two_le_three {m m' : ℕ} (h : m ≤ m') : sharpCost 2 m ≤ sharpCost 3 m' := by
  have h1 : winCost 2 m ≤ winCost 3 m := by
    unfold winCost
    apply Nat.ceil_mono
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · norm_num
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      exact Real.rpow_le_rpow_of_exponent_le this (by norm_num)
  have h2 := winCost_mono (r := 3) (by norm_num) h
  unfold sharpCost
  exact Nat.mul_le_mul (h1.trans h2) (Nat.succ_le_succ (Nat.log_mono_right h))

/-- **Theorem 3.8 for `3`-graphs from Theorem 3.7 for graphs** (flat clique omni-absorbers with
the additive term `sharpCost 2 m = ⌈m^{1/2}⌉ (⌊log₂ m⌋ + 1)` of the paper). -/
theorem nativeStrongMultiRefiners_three_of_cliqueOmni_two {q : ℕ} (hq : 3 < q)
    (hF : FlatCliqueOmniAbsorbers (q - 1) (sharpCost 2)) : NativeStrongMultiRefiners q 3 :=
  nativeStrongMultiRefiners_three_of_cliqueOmni hq (sharpCost 2) hF
    fun _ _ h => sharpCost_two_le_three h

end RefinedAbsorption.Local
