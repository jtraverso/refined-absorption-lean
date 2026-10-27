module
public import RequestProject.Pending.SafeAbsorbers
public import RequestProject.Original2024.Host

/-!
# Refined omni-absorbers in a dense host, safe with respect to a given packing

The chain `hostRefinerAbsorbers → hostCore → theorem_1_7_strong_two_le` of `Original2024`, with
the attached absorbers replaced by `safePlacedAttachedAbsorbers`.  The result
(`safeTheorem17`) is Theorem 1.7 in a dense host `G` with the additional property that every
clique of the decomposition family meets every member of a given `K_q^r`-packing `Pk` in at most
`r` vertices (for `n ≥ C q`).
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.Absorber17 RefinedAbsorption.Placement
open RefinedAbsorption.Original2024

/-- **Safe refiner and absorbers avoiding `F`, inside `Fin n`.** -/
theorem safeHostRefinerAbsorbers {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) (C : ℕ) (hC : 1 ≤ C) :
    ∃ Cf : ℕ, 1 ≤ Cf ∧ ∀ (n : ℕ) {E : Type*} [DecidableEq E] (ends : E → Finset (Fin n))
      (K X R : Finset E) (𝒲 : Finset (Finset E)) (D : ℕ) (F : Finset (Finset (Fin n)))
      (Pk : Finset (Finset (Fin n))),
      IsStrongMultiRefiner q r C ends K X R 𝒲 D → Cf * D ≤ n →
      (∀ S : Finset (Fin n), S.card = r - 1 → Cf * (D + deg F S) ≤ n) → 0 < n →
      (∀ P ∈ Pk, P.card = q) → (∀ f : Finset (Fin n), f.card = r → cliqueMult Pk f ≤ 1) →
      Cf * q ≤ n →
      ∃ (R' : Finset (Finset (Fin n))) (𝒲' : Finset (Finset (Finset (Fin n))))
        (A Qon Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
        IsStrongRefiner q r Cf (X.image ends) R' 𝒲' D ∧ Disjoint R' F ∧
        IsAttachedAbsorbers q r (X.image ends) R' 𝒲' A Qon Qoff ∧
        (∀ W ∈ 𝒲', Disjoint (A W) F) ∧
        (∀ S : Finset (Fin n), S.card = r - 1 → deg (R' ∪ 𝒲'.sup A) S ≤ Cf * D) ∧
        ∀ W ∈ 𝒲', ∀ Q ∈ Qon W ∪ Qoff W, ∀ P ∈ Pk, (Q ∩ P).card ≤ r := by
  obtain ⟨C', hC', hred⟩ := placedMultiplicityReductionHost hr hrq C hC
  obtain ⟨Ca, hCa, habs⟩ := safePlacedAttachedAbsorbers (by omega : 1 ≤ r) hrq C'
  set Cf := C' + Ca * (1 + C') + 1 with hCf
  refine ⟨Cf, by omega, ?_⟩
  intro n E _ ends K X R 𝒲 D F Pk hS hD hFdeg hn hPk hPm hCq
  have hC'D : C' * D ≤ n := (Nat.mul_le_mul_right _ (by omega)).trans hD
  have hFC' : ∀ S : Finset (Fin n), S.card = r - 1 → C' * (D + deg F S) ≤ n := fun S hS' =>
    (Nat.mul_le_mul_right _ (by omega)).trans (hFdeg S hS')
  obtain ⟨R', 𝒲', hS', hR'F⟩ := hred n ends X R 𝒲 D F (IsStrongMultiRefiner.keepX hS) hC'D hFC' hn
  have hR := hS'.refiner
  have hdegG : ∀ S : Finset (Fin n), S.card = r - 1 →
      Ca * deg (X.image ends ∪ (R' ∪ F)) S ≤ n := by
    intro S hS''
    have h1 : deg (X.image ends ∪ (R' ∪ F)) S ≤
        deg (X.image ends) S + (deg R' S + deg F S) := by
      unfold deg; rw [filter_union, filter_union]
      exact (card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _)
    have h2 := hS'.degX S hS''
    have h3 := hS'.degR S hS''
    refine le_trans (Nat.mul_le_mul_left _ h1) (le_trans ?_ (hFdeg S hS''))
    have : Ca * (D + (C' * D + deg F S)) ≤ Cf * (D + deg F S) := by
      have e : Ca * (D + (C' * D + deg F S)) + ((C' + 1) * (D + deg F S) + Ca * C' * deg F S) =
          Cf * (D + deg F S) := by simp only [hCf]; ring
      omega
    calc Ca * (deg (X.image ends) S + (deg R' S + deg F S))
        ≤ Ca * (D + (C' * D + deg F S)) := by gcongr
      _ ≤ _ := this
  have hCaD : Ca * (C' * D) ≤ n := by
    refine le_trans ?_ hD
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by simp only [hCf]; nlinarith)
  have hCaq : Ca * q ≤ n := (Nat.mul_le_mul_right _ (by simp only [hCf]; nlinarith)).trans hCq
  obtain ⟨A, Qon, Qoff, hA, hdeg, hsafe⟩ := habs n (X.image ends) (R' ∪ F) 𝒲' (C' * D) Pk
    (fun W hW e he => hR.rgraph e (hR.subset W hW he)) hR.divisible hR.card_le
    hdegG hS'.pieceDeg hCaD hn hPk hPm hCaq
  refine ⟨R', 𝒲', A, Qon, Qoff, IsStrongRefiner.mono_C hS' (by omega), hR'F,
    ⟨hA.rgraph, ?_, hA.pairwise, hA.on, hA.off⟩, ?_, ?_, hsafe⟩
  · intro W hW
    exact disjoint_of_subset_right (union_subset_union subset_rfl subset_union_left)
      (hA.disjoint W hW)
  · intro W hW
    exact disjoint_of_subset_right (subset_union_right.trans subset_union_right)
      (hA.disjoint W hW)
  · intro S hS''
    have h1 : deg (R' ∪ 𝒲'.sup A) S ≤ deg R' S + deg (𝒲'.sup A) S := by
      unfold deg; rw [filter_union]; exact card_union_le _ _
    have h2 := hS'.degR S hS''
    have h3 := hdeg S hS''
    calc deg (R' ∪ 𝒲'.sup A) S ≤ C' * D + Ca * (C' * D) := h1.trans (Nat.add_le_add h2 h3)
      _ ≤ Cf * D := by simp only [hCf]; nlinarith

/-- **Safe core of Theorem 1.7, `r ≥ 2`.** -/
theorem safeHostCore {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (n : ℕ) (X F : Finset (Finset (Fin n))) (D : ℝ)
      (Pk : Finset (Finset (Fin n))),
      IsRGraph r X → MaxDegLE r X D → D ≤ n / C →
      (∀ S : Finset (Fin n), S.card + 1 = r → C * deg F S ≤ n) →
      (∀ P ∈ Pk, P.card = q) → (∀ f : Finset (Fin n), f.card = r → cliqueMult Pk f ≤ 1) →
      C * q ≤ n →
      ∃ (R : Finset (Finset (Fin n))) (𝒲 : Finset (Finset (Finset (Fin n))))
        (A Qon Qoff : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
        HostWitness q r C X F (max D (budget n r)) R 𝒲 A Qon Qoff ∧
        ∀ W ∈ 𝒲, ∀ Q ∈ Qon W ∪ Qoff W, ∀ P ∈ Pk, (Q ∩ P).card ≤ r := by
  obtain ⟨C₁, hC₁, n₀, hN⟩ := General.nativeStrongMultiRefiners_all hr hrq
  obtain ⟨Cf, hCf, hasm⟩ := safeHostRefinerAbsorbers hr hrq C₁ hC₁
  obtain ⟨n₁, hn₁⟩ := eventually_mul_rpow_log_le (by omega : 1 ≤ r) (2 * (Cf : ℝ) * C₁)
    (by positivity)
  set C₀ := 2 * Cf * C₁ + 2 * Cf + r * Cf + Cf * C₁ + C₁ + n₀ + n₁ + 1 with hC₀
  refine ⟨C₀, by omega, ?_⟩
  intro n X F D Pk hX hXD hDn hF hPk hPm hCq
  have hC₀pos : (0 : ℝ) < C₀ := by positivity
  have hn0R : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set L := budget n r with hL
  have hL0 : 0 ≤ L := budget_nonneg n r
  have hM0 : 0 ≤ max D L := le_max_of_le_right hL0
  by_cases hsmall : n₀ ≤ n ∧ n₁ ≤ n ∧ 1 ≤ n
  · obtain ⟨hn0, hn1, hnpos⟩ := hsmall
    have hCC : (C₁ : ℝ) ≤ C₀ := by exact_mod_cast (show C₁ ≤ C₀ by omega)
    have hC₁pos : (0 : ℝ) < C₁ := by exact_mod_cast hC₁
    have hDn' : D ≤ n / C₁ := hDn.trans (div_le_div_of_nonneg_left hn0R hC₁pos hCC)
    obtain ⟨E, _, ends, K, Xl, R, 𝒲, B, hXl, hB, hS⟩ := hN n hn0 X D hX hXD hDn'
    have hD1 : 2 * (Cf : ℝ) * C₁ * D ≤ n := by
      rcases le_or_gt D 0 with hD0 | hD0
      · have : 2 * (Cf : ℝ) * C₁ * D ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hD0
        linarith
      · have h2 : ((2 * Cf * C₁ : ℕ) : ℝ) ≤ C₀ := by exact_mod_cast (show 2 * Cf * C₁ ≤ C₀ by omega)
        calc 2 * (Cf : ℝ) * C₁ * D = ((2 * Cf * C₁ : ℕ) : ℝ) * D := by push_cast; ring
          _ ≤ C₀ * D := mul_le_mul_of_nonneg_right h2 hD0.le
          _ ≤ C₀ * (n / C₀) := mul_le_mul_of_nonneg_left hDn hC₀pos.le
          _ = n := by field_simp
    have hL1 : 2 * (Cf : ℝ) * C₁ * L ≤ n := hn₁ n hn1
    have h2B : ((2 * Cf * B : ℕ) : ℝ) ≤ n := by
      push_cast
      calc 2 * (Cf : ℝ) * B ≤ 2 * Cf * (C₁ * max D L) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
        _ = max (2 * (Cf : ℝ) * C₁ * D) (2 * (Cf : ℝ) * C₁ * L) := by
            rw [← mul_assoc, mul_max_of_nonneg _ _ (by positivity)]
        _ ≤ n := max_le hD1 hL1
    have h2B' : 2 * Cf * B ≤ n := by exact_mod_cast h2B
    have hCfB : Cf * B ≤ n := by nlinarith
    have hFdeg : ∀ S : Finset (Fin n), S.card = r - 1 → Cf * (B + deg F S) ≤ n := by
      intro S hS
      have h1 := hF S (by omega)
      have h2 : 2 * Cf * deg F S ≤ C₀ * deg F S := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    have hCfq : Cf * q ≤ n := (Nat.mul_le_mul_right _ (by omega)).trans hCq
    obtain ⟨R', 𝒲', A, Qon, Qoff, hS', hR'F, hA, hAF, hdeg, hsafe⟩ :=
      hasm n ends K Xl R 𝒲 B F Pk hS hCfB hFdeg hnpos hPk hPm hCfq
    rw [hXl] at hS' hA
    have hCfC : ((Cf * C₁ : ℕ) : ℝ) ≤ C₀ := by exact_mod_cast (show Cf * C₁ ≤ C₀ by omega)
    have hbound : ∀ x : ℕ, x ≤ Cf * B → (x : ℝ) ≤ C₀ * max D L := by
      intro x hx
      calc (x : ℝ) ≤ ((Cf * B : ℕ) : ℝ) := by exact_mod_cast hx
        _ = Cf * B := by push_cast; ring
        _ ≤ Cf * (C₁ * max D L) := mul_le_mul_of_nonneg_left hB (by positivity)
        _ = ((Cf * C₁ : ℕ) : ℝ) * max D L := by push_cast; ring
        _ ≤ C₀ * max D L := mul_le_mul_of_nonneg_right hCfC hM0
    have hR := hS'.refiner
    refine ⟨R', 𝒲', A, Qon, Qoff, ⟨hR.mono (by omega), hS'.oneX, fun W hW => ?_, hR'F, hA,
      hAF, fun S hS'' => hbound _ (hS'.degR S (by omega)),
      fun S hS'' => hbound _ (hdeg S (by omega)),
      fun S hS'' => hbound _ (hS'.pieceDeg S (by omega))⟩, hsafe⟩
    refine (card_vertexSet_le (fun e he => hR.rgraph e (hR.subset W hW he))
      (hR.card_le W hW)).trans ?_
    omega
  · have hlt : n < C₀ := by
      rcases not_and_or.1 hsmall with h | h
      · omega
      · rcases not_and_or.1 h with h | h <;> omega
    have hltR : (n : ℝ) < C₀ := by exact_mod_cast hlt
    have hD1 : D < 1 := hDn.trans_lt ((div_lt_one hC₀pos).2 hltR)
    have hX0 := eq_empty_of_maxDegLE_lt_one (by omega) hX hXD hD1
    subst hX0
    exact ⟨_, _, _, _, _, hostWitness_empty q r C₀ n F _ hM0, by simp⟩

/-- **Theorem 1.7, safe with respect to a given packing, `r ≥ 2`.** -/
theorem safeTheorem17 {q r : ℕ} (hr : 2 ≤ r) (hrq : r < q) :
    ∃ C : ℕ, 1 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (G X : Finset (Finset (Fin n))) (D : ℝ)
      (Pk : Finset (Finset (Fin n))),
      IsRGraph r G → MinDegGE r G ((1 - ε) * n) → X ⊆ G → MaxDegLE r X D → D ≤ n / C →
      (∀ P ∈ Pk, P.card = q) → (∀ f : Finset (Fin n), f.card = r → cliqueMult Pk f ≤ 1) →
      C * q ≤ n →
      ∃ (A F : Finset (Finset (Fin n))) (QA : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
        IsOmniAbsorberOn q r univ X A F QA ∧ A ⊆ G ∧
        MaxDegLE r A (C * max D (budget n r)) ∧ ∀ Q ∈ F, ∀ P ∈ Pk, (Q ∩ P).card ≤ r := by
  obtain ⟨C, hC, hcore⟩ := safeHostCore (q := q) hr hrq
  refine ⟨2 * C, by omega, 1 / C, by positivity, ?_⟩
  intro n G X D Pk hG hδ hXG hXD hDn hPk hPm hCq
  have hX : IsRGraph r X := fun e he => hG e (hXG he)
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hDn' : D ≤ n / C := hDn.trans (div_le_div_of_nonneg_left hn0 hCpos (by push_cast; linarith))
  have hCq' : C * q ≤ n := (Nat.mul_le_mul_right _ (by omega)).trans hCq
  obtain ⟨R, 𝒲, A, Qon, Qoff, hW, hsafe⟩ := hcore n X (completeRGraph (Fin n) r \ G) D Pk hX hXD
    hDn' (fun S hS => mul_deg_compl_le hC hG hδ S hS) hPk hPm hCq'
  have hR := hW.refiner
  have hA := hW.absorbers
  obtain ⟨QA, hQA, -⟩ := omniAbsorber_of_refiner_absorbers hrq.le hC hR hA
  have hRr : ∀ e ∈ R, e.card = r := fun e he => hR.rgraph e (mem_union_right _ he)
  have hAr : ∀ e ∈ R ∪ 𝒲.sup A, e.card = r := by
    intro e he
    rcases mem_union.1 he with h | h
    · exact hRr e h
    · obtain ⟨W, hW', heW⟩ := mem_sup.1 h
      exact hA.rgraph W hW' e heW
  have hAF : Disjoint (R ∪ 𝒲.sup A) (completeRGraph (Fin n) r \ G) := by
    rw [disjoint_union_left]
    exact ⟨hW.avoidR, Finset.disjoint_sup_left.2 hW.avoidA⟩
  have hfam : ∀ Q ∈ 𝒲.sup (fun W => Qon W ∪ Qoff W), ∃ W ∈ 𝒲,
      (Q ∈ Qon W ∧ cliqueEdges r Q ⊆ A W ∪ W) ∨ (Q ∈ Qoff W ∧ cliqueEdges r Q ⊆ A W) := by
    intro Q hQ
    obtain ⟨W, hW', hQW⟩ := mem_sup.1 hQ
    refine ⟨W, hW', ?_⟩
    rcases mem_union.1 hQW with h | h
    · exact Or.inl ⟨h, (hA.on W hW').cliqueEdges_subset h⟩
    · exact Or.inr ⟨h, (hA.off W hW').cliqueEdges_subset h⟩
  refine ⟨R ∪ 𝒲.sup A, 𝒲.sup (fun W => Qon W ∪ Qoff W), QA,
    ⟨fun e he => ⟨hX e he, subset_univ _⟩, fun e he => ⟨hAr e he, subset_univ _⟩,
      hQA.disjoint, fun Q hQ => ?_, hQA.subset_family, hQA.decomp⟩,
    subset_of_disjoint_compl hAr hAF, fun S hS => ?_, fun Q hQ P hP => ?_⟩
  · obtain ⟨W, hW', h | h⟩ := hfam Q hQ
    · refine ⟨(hA.on W hW').card_eq Q h.1, h.2.trans ?_⟩
      intro e he
      rcases mem_union.1 he with h' | h'
      · exact mem_union_right _ (mem_union_right _ (mem_sup.2 ⟨W, hW', h'⟩))
      · rcases mem_union.1 (hR.subset W hW' h') with h'' | h''
        · exact mem_union_left _ h''
        · exact mem_union_right _ (mem_union_left _ h'')
    · refine ⟨(hA.off W hW').card_eq Q h.1, h.2.trans ?_⟩
      intro e he
      exact mem_union_right _ (mem_union_right _ (mem_sup.2 ⟨W, hW', he⟩))
  · refine (hW.degRA S hS).trans ?_
    have hM : 0 ≤ max D (budget n r) := le_max_of_le_right (budget_nonneg n r)
    push_cast
    nlinarith
  · obtain ⟨W, hW', hQW⟩ := mem_sup.1 hQ
    exact hsafe W hW' Q hQW P hP

end RefinedAbsorption.Pending
