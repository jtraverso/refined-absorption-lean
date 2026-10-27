module
public import RefinedAbsorption.Pending.Theorem63Final
public import RefinedAbsorption.Extensions.Packing

/-!
# Theorem 6.2 of arXiv:2402.17855v1, proved from Theorems 6.1 and 6.3

The article states that Theorem 6.2 follows from Theorem 6.3 without giving the construction.
The deduction formalized here:

* place `L` on the first `m` vertices of `Fin (m + h)`, inside the set `U` of the first `m'`
  vertices, where `m' ≥ m` and `m + h` are admissible orders and `m + h` is large;
* `A₀ = K_{m+h}^r \ K_U^r` is divisible (both complete graphs are), dense, edge-disjoint from `L`,
  and no edge of `A₀` lies inside `U ⊇ V(L)`;
* Theorem 6.1 gives a decomposition `Q₁` of `A₀`, which is a packing of `G = A₀ ∪ L`;
* Theorem 6.3 applied to `G` and `Q₁` gives a decomposition `Q₂` of `A₀ ∪ L` with
  `|P₁ ∩ P₂| ≤ r` for all `P₁ ∈ Q₁`, `P₂ ∈ Q₂`;
* everything is transported along `Fin m ⊕ Fin h ≃ Fin (m + h)`, fixing the vertices of `L`.

This uses Theorem 6.3 (`theorem_6_3`) and Theorem 6.1 (`Original2024.theorem_6_1`), not
Theorem 6.2.
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset RefinedAbsorption.Extensions RefinedAbsorption.Absorber17

theorem mem_map_castLEEmb {N m : ℕ} (hmN : m ≤ N) (x : Fin N) :
    x ∈ (univ : Finset (Fin m)).map (Fin.castLEEmb hmN) ↔ x.val < m := by
  simp only [mem_map, mem_univ, true_and, Fin.castLEEmb_apply]
  constructor
  · rintro ⟨a, rfl⟩; simp
  · intro hx; exact ⟨⟨x, hx⟩, Fin.ext rfl⟩

/-- **Theorem 6.2 of arXiv:2402.17855v1** (proved). -/
theorem theorem_6_2 : RefinedAbsorption.Faithful2024.Theorem_6_2 := by
  intro q r hr hrq m L hLr hdiv
  classical
  obtain ⟨ε₁, hε₁, n₁, h61⟩ := RefinedAbsorption.Original2024.theorem_6_1 q r hr hrq
  obtain ⟨n₃, ε₃, hε₃, h63⟩ := theorem_6_3 q r hr hrq
  set ε := min ε₁ ε₃ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₃
  -- the admissible order `m'` of the old set `U`
  obtain ⟨m', hm'1, -, hm'div⟩ := exists_admissible_near hrq (max m q) (le_max_right _ _)
  have hmm' : m ≤ m' := by omega
  -- the admissible order of the whole vertex set
  set nb := max (max n₁ n₃) (max (max m' q) ⌈((r : ℝ) + m') / ε⌉₊) with hnb
  obtain ⟨N, hN1, -, hNdiv⟩ := exists_admissible_near hrq nb
    (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _)))
  have hNn₁ : n₁ ≤ N := by omega
  have hNn₃ : n₃ ≤ N := by omega
  have hm'N : m' ≤ N := by omega
  have hqN : q ≤ N := by omega
  have hNε : (r : ℝ) + m' ≤ ε * N := by
    have h1 : ((r : ℝ) + m') / ε ≤ N := by
      have : ⌈((r : ℝ) + m') / ε⌉₊ ≤ N := by omega
      exact (Nat.le_ceil _).trans (by exact_mod_cast this)
    rw [div_le_iff₀ hε] at h1
    linarith
  obtain ⟨h, rfl⟩ : ∃ h, N = m + h := ⟨N - m, by omega⟩
  set n := m + h with hn
  -- the sets and graphs on `Fin n`
  set Uset : Finset (Fin n) := (univ : Finset (Fin m')).map (Fin.castLEEmb hm'N) with hUset
  have hmemU : ∀ x : Fin n, x ∈ Uset ↔ x.val < m' := mem_map_castLEEmb hm'N
  have hUcard : Uset.card = m' := by rw [hUset, card_map, card_univ, Fintype.card_fin]
  set KU := Uset.powersetCard r with hKU
  set K := completeRGraph (Fin n) r with hK
  have hKUK : KU ⊆ K := fun e he =>
    mem_powersetCard.2 ⟨subset_univ _, (mem_powersetCard.1 he).2⟩
  set A₀ := K \ KU with hA₀
  have hA₀KU : Disjoint A₀ KU := sdiff_disjoint
  have hKeq : A₀ ∪ KU = K := sdiff_union_of_subset hKUK
  have hKdiv : IsDivisible q r K := isDivisible_completeRGraph_iff.2 hNdiv
  have hKUdiv : IsDivisible q r KU := by
    intro S hS
    by_cases hSU : S ⊆ Uset
    · rw [deg, hKU, card_powersetCard_filter_superset hSU hS.le, hUcard]
      have := hm'div S.card hS
      rwa [one_mul] at this
    · rw [deg, hKU, card_powersetCard_filter_superset_of_not hSU]
      exact dvd_zero _
  have hA₀div : IsDivisible q r A₀ := IsDivisible.of_union hA₀KU (hKeq ▸ hKdiv) hKUdiv
  have hA₀r : IsRGraph r A₀ := fun e he => (mem_powersetCard.1 (mem_sdiff.1 he).1).2
  -- the old graph
  set e := (finSumFinEquiv : Fin m ⊕ Fin h ≃ Fin n) with he
  set ι : Fin m ↪ Fin n := Function.Embedding.inl.trans e.toEmbedding with hι
  have hιval : ∀ a, (ι a).val = a.val := by
    intro a
    show (e (Sum.inl a)).val = a.val
    rw [he, finSumFinEquiv_apply_left, Fin.val_castAdd]
  set L₀ := RefinedAbsorption.gmap ι L with hL₀
  have hL₀KU : L₀ ⊆ KU := by
    intro f hf
    obtain ⟨f₀, hf₀, rfl⟩ := mem_gmap.1 hf
    refine mem_powersetCard.2 ⟨fun x hx => ?_, by rw [card_map]; exact hLr f₀ hf₀⟩
    obtain ⟨a, -, rfl⟩ := mem_map.1 hx
    rw [hmemU, hιval]
    omega
  have hA₀L₀ : Disjoint A₀ L₀ := disjoint_of_subset_right hL₀KU hA₀KU
  set G := A₀ ∪ L₀ with hG
  have hGr : IsRGraph r G := by
    intro f hf
    rcases mem_union.1 hf with hf | hf
    · exact hA₀r f hf
    · exact (hLr.gmap ι) f hf
  have hGdiv : IsDivisible q r G := hA₀div.union hA₀L₀ (hdiv.gmap ι)
  -- density
  have hA₀deg : ∀ S : Finset (Fin n), S.card + 1 = r → (n : ℝ) - r - m' ≤ deg A₀ S := by
    intro S hS
    have h1 : deg A₀ S + deg KU S = n - S.card := by
      rw [← deg_union_of_disjoint hA₀KU, hKeq, hK, deg_completeRGraph (by omega),
        show r - S.card = 1 by omega, Nat.choose_one_right]
    have h2 : deg KU S ≤ m' := by
      by_cases hSU : S ⊆ Uset
      · rw [deg, hKU, card_powersetCard_filter_superset hSU (by omega), hUcard,
          show r - S.card = 1 by omega, Nat.choose_one_right]
        omega
      · rw [deg, hKU, card_powersetCard_filter_superset_of_not hSU]; omega
    have h3 : (deg A₀ S : ℝ) + m' ≥ n - S.card := by
      have : deg A₀ S + m' ≥ n - S.card := by omega
      have h4 : ((n - S.card : ℕ) : ℝ) = n - S.card := by rw [Nat.cast_sub (by omega)]
      rw [← h4]; exact_mod_cast this
    have h5 : (S.card : ℝ) ≤ r := by exact_mod_cast (show S.card ≤ r by omega)
    linarith
  have hdense : ∀ ε' : ℝ, ε ≤ ε' → ∀ J : Finset (Finset (Fin n)), A₀ ⊆ J →
      MinDegGE r J ((1 - ε') * n) := by
    intro ε' hε' J hJ S hS
    have h1 := hA₀deg S hS
    have h2 : (deg A₀ S : ℝ) ≤ deg J S := by
      exact_mod_cast card_le_card (filter_subset_filter _ hJ)
    have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  -- Theorem 6.1: a decomposition `Q₁'` of `A₀`
  obtain ⟨Q₁', hQ₁'⟩ := h61 n hNn₁ A₀ hA₀r (hdense ε₁ (min_le_left _ _) A₀ subset_rfl) hA₀div
  have hpack : IsPacking q r G Q₁' := by
    refine ⟨hQ₁'.card_eq, fun Q hQ => (hQ₁'.cliqueEdges_subset hQ).trans subset_union_left,
      fun f hf => ?_⟩
    rw [hQ₁'.mult_eq f hf]
    split_ifs <;> omega
  -- Theorem 6.3: a decomposition `Q₂'` of `A₀ ∪ L₀` avoiding `Q₁'`
  obtain ⟨Q₂', hQ₂', hcross⟩ := h63 n hNn₃ G hGr hGdiv
    (hdense ε₃ (min_le_right _ _) G subset_union_left) Q₁' hpack
  -- transport to `Fin m ⊕ Fin h`
  set f : Fin n ↪ Fin m ⊕ Fin h := e.symm.toEmbedding with hf
  have hιf : ι.trans f = Function.Embedding.inl := by
    ext a
    show e.symm (e (Sum.inl a)) = Sum.inl a
    exact e.symm_apply_apply _
  have hLf : RefinedAbsorption.gmap f L₀ = RefinedAbsorption.gmap Function.Embedding.inl L := by
    rw [hL₀, gmap_gmap, hιf]
  have hQ₂f : IsDecomposition q r (RefinedAbsorption.gmap f A₀ ∪
      RefinedAbsorption.gmap Function.Embedding.inl L) (RefinedAbsorption.gmap f Q₂') := by
    have := hQ₂'.gmap f
    rwa [hG, gmap_union, hLf] at this
  refine ⟨h, RefinedAbsorption.gmap f A₀, RefinedAbsorption.gmap f Q₁',
    RefinedAbsorption.gmap f Q₂', ⟨hdiv.gmap _, ?_, ⟨_, hQ₁'.gmap f⟩, ⟨_, hQ₂f⟩⟩, hQ₁'.gmap f,
    hQ₂f, ?_⟩
  · -- independence of the old vertices
    intro t ht hsub
    obtain ⟨t₀, ht₀, rfl⟩ := mem_gmap.1 ht
    have ht₀U : t₀ ⊆ Uset := by
      intro x hx
      have hfx : f x ∈ vertexSet (RefinedAbsorption.gmap Function.Embedding.inl L) :=
        hsub (mem_map_of_mem f hx)
      rw [vertexSet_gmap] at hfx
      obtain ⟨a, -, ha⟩ := mem_map.1 hfx
      have hxa : x = ι a := by
        have : e.symm x = Sum.inl a := by simpa [hf] using ha.symm
        rw [hι]
        show x = e (Sum.inl a)
        rw [← this, e.apply_symm_apply]
      rw [hxa, hmemU, hιval]
      omega
    have : t₀ ∈ KU := mem_powersetCard.2 ⟨ht₀U, hA₀r t₀ ht₀⟩
    exact disjoint_left.1 hA₀KU ht₀ this
  · intro P₁ hP₁ P₂ hP₂
    obtain ⟨P₁', hP₁', rfl⟩ := mem_gmap.1 hP₁
    obtain ⟨P₂', hP₂', rfl⟩ := mem_gmap.1 hP₂
    rw [← map_inter, card_map]
    exact hcross P₁' hP₁' P₂' hP₂'

end RefinedAbsorption.Pending
