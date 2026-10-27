module
public import RequestProject.GeneralEmbedding.State

/-!
# One step of the greedy embedding

Given the embeddings of the supergraphs `W_H`, `H ∈ 𝒮`, with accidental degrees below the
thresholds `θ_j = K_j D n^{r-1-j}`, we embed one more supergraph `W_H`: among its at least
`γ n^{m_H}` embeddings, at most `γ n^{m_H} / 4` reuse an already used new edge
(`card_bad1_le`) and at most `γ n^{m_H} / 4` put a new edge through a nearly saturated set
(`card_bad2_le`), so a good embedding exists (`exists_good_embedding`).
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

variable {n r C : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {ends : ι → Finset (Fin n)} {ℋ : Finset (Finset ι)} {m : Finset ι → ℕ}
  {W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H)))}

/-- The thresholds `θ_j = K_j D n^{r-1-j}`. -/
noncomputable def thr (Q c D : ℝ) (n r j : ℕ) : ℝ := Kseq Q c j * D * (n : ℝ) ^ (r - 1 - j)

/-- Total degrees are bounded by structural plus accidental contributions. -/
theorem totDeg_bound {Q D : ℝ} (hD0 : 0 ≤ D)
    (hends : ∀ x, (ends x).card = r)
    (hdeg : ∀ S : Finset (Fin n), S.card + 1 = r →
      ((univ.filter (fun x => S ⊆ ends x)).card : ℝ) ≤ D)
    (href : IsCRefinedFamily C ℋ) (hint : IsEdgeIntersecting ends ℋ m W)
    (hbd : ∀ H ∈ ℋ, (W H).card ≤ C) {𝒮 : Finset (Finset ι)} (h𝒮 : 𝒮 ⊆ ℋ)
    {φ : (H : Finset ι) → Fin (m H) → Fin n}
    (hacc : ∀ A : Finset (Fin n), A.card + 1 ≤ r →
      (accDeg W 𝒮 φ A : ℝ) ≤ thr Q ((C : ℝ) ^ 2) D n r A.card)
    (A : Finset (Fin n)) (hA : A.card + 1 ≤ r) :
    (totDeg W 𝒮 φ A : ℝ) ≤ ((C : ℝ) ^ 2 + Kseq Q ((C : ℝ) ^ 2) A.card) * D *
      (n : ℝ) ^ (r - 1 - A.card) := by
  have h1 : (totDeg W 𝒮 φ A : ℝ) ≤ strDeg W 𝒮 A + accDeg W 𝒮 φ A := by
    exact_mod_cast totDeg_le W 𝒮 φ A
  have h2 : (strDeg W 𝒮 A : ℝ) ≤ C * C * (univ.filter (fun x => A ⊆ ends x)).card := by
    exact_mod_cast strDeg_le W h𝒮 href hint hbd A
  have h3 := mdeg_le ends hends hD0 hdeg A hA
  have h4 := hacc A hA
  unfold thr at h4
  have hC0 : (0 : ℝ) ≤ C * C := by positivity
  have h5 : (C : ℝ) * C * (univ.filter (fun x => A ⊆ ends x)).card ≤
      C * C * ((n : ℝ) ^ (r - 1 - A.card) * D) := mul_le_mul_of_nonneg_left h3 hC0
  nlinarith

/-- The `b`-sets `T` disjoint from `A'` such that `A' ∪ T` is nearly saturated. -/
noncomputable def satSets (W : (H : Finset ι) → Finset (Finset (Fin n ⊕ Fin (m H))))
    (𝒮 : Finset (Finset ι)) (φ : (H : Finset ι) → Fin (m H) → Fin n) (Q D : ℝ) (C r : ℕ)
    (A' : Finset (Fin n)) (b : ℕ) : Finset (Finset (Fin n)) :=
  ((univ : Finset (Fin n)).powersetCard b).filter (fun T => Disjoint T A' ∧
    A'.card + b + 1 ≤ r ∧
    thr Q ((C : ℝ) ^ 2) D n r (A'.card + b) < (accDeg W 𝒮 φ (A' ∪ T) : ℝ) + C)

omit [Fintype ι] [DecidableEq ι] in
theorem accDeg_le_totDeg (𝒮 : Finset (Finset ι)) (φ : (H : Finset ι) → Fin (m H) → Fin n)
    (A : Finset (Fin n)) : accDeg W 𝒮 φ A ≤ totDeg W 𝒮 φ A :=
  card_le_card (fun _ hp => mem_filter.2 ⟨(mem_filter.1 hp).1, (mem_filter.1 hp).2.1⟩)

/-- Few sets are nearly saturated. -/
theorem card_satSets_le {Q D : ℝ} (hQ : 2 ≤ Q) (hD1 : 1 ≤ D) (hn : 1 ≤ n) (hC1 : 1 ≤ C)
    (hends : ∀ x, (ends x).card = r)
    (hdeg : ∀ S : Finset (Fin n), S.card + 1 = r →
      ((univ.filter (fun x => S ⊆ ends x)).card : ℝ) ≤ D)
    (href : IsCRefinedFamily C ℋ) (hint : IsEdgeIntersecting ends ℋ m W)
    (hunif : ∀ H ∈ ℋ, ∀ e ∈ W H, e.card = r)
    (hbd : ∀ H ∈ ℋ, (W H).card ≤ C) {𝒮 : Finset (Finset ι)} (h𝒮 : 𝒮 ⊆ ℋ)
    {φ : (H : Finset ι) → Fin (m H) → Fin n}
    (hacc : ∀ A : Finset (Fin n), A.card + 1 ≤ r →
      (accDeg W 𝒮 φ A : ℝ) ≤ thr Q ((C : ℝ) ^ 2) D n r A.card)
    (A' : Finset (Fin n)) {b : ℕ} (hb : 1 ≤ b) :
    ((satSets W 𝒮 φ Q D C r A' b).card : ℝ) ≤ 2 ^ (r + 1) / Q * (n : ℝ) ^ b := by
  classical
  rcases (satSets W 𝒮 φ Q D C r A' b).eq_empty_or_nonempty with hS | ⟨T₀, hT₀⟩
  · rw [hS, card_empty, Nat.cast_zero]; positivity
  have hj : A'.card + b + 1 ≤ r := (mem_filter.1 hT₀).2.2.1
  set j := A'.card + b with hjdef
  set c2 : ℝ := (C : ℝ) ^ 2 with hc2
  set K := Kseq Q c2 with hK
  have hc20 : 0 ≤ c2 := by positivity
  have hQ1 : 1 ≤ Q := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD0 : 0 ≤ D := by linarith
  -- the threshold `θ_j` is at least `2C`
  have hKj : Q * c2 ≤ K j := by
    have : j = (j - 1) + 1 := by omega
    rw [this]; exact Kseq_succ_ge hQ1 hc20 _
  have hCc2 : (C : ℝ) ≤ c2 := by
    have : (1 : ℝ) ≤ C := by exact_mod_cast hC1
    rw [hc2]; nlinarith
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ (r - 1 - j) := one_le_pow₀ hn1
  have hθ : 2 * (C : ℝ) ≤ thr Q c2 D n r j := by
    unfold thr
    have h1 : 2 * (C : ℝ) ≤ K j := by nlinarith
    have h2 : K j ≤ K j * D * (n : ℝ) ^ (r - 1 - j) := by
      have hK0 : 0 ≤ K j := Kseq_nonneg (by linarith) hc20 j
      have : 1 ≤ D * (n : ℝ) ^ (r - 1 - j) := by nlinarith
      nlinarith
    linarith
  have hθpos : 0 < thr Q c2 D n r j := by
    have : (0 : ℝ) < C := by exact_mod_cast hC1
    linarith
  -- every saturated set carries half the threshold
  have hsum1 : ((satSets W 𝒮 φ Q D C r A' b).card : ℝ) * (thr Q c2 D n r j / 2) ≤
      ∑ T ∈ satSets W 𝒮 φ Q D C r A' b, (accDeg W 𝒮 φ (A' ∪ T) : ℝ) := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun T hT => ?_
    have := (mem_filter.1 hT).2.2.2
    linarith
  have hsum2 : ∑ T ∈ satSets W 𝒮 φ Q D C r A' b, (accDeg W 𝒮 φ (A' ∪ T) : ℝ) ≤
      ∑ T ∈ (univ : Finset (Fin n)).powersetCard b, (totDeg W 𝒮 φ (A' ∪ T) : ℝ) := by
    refine (sum_le_sum fun T _ => (by exact_mod_cast accDeg_le_totDeg 𝒮 φ (A' ∪ T) :
      (accDeg W 𝒮 φ (A' ∪ T) : ℝ) ≤ totDeg W 𝒮 φ (A' ∪ T))).trans ?_
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
  have hsum3 : ∑ T ∈ (univ : Finset (Fin n)).powersetCard b, (totDeg W 𝒮 φ (A' ∪ T) : ℝ) ≤
      2 ^ r * (totDeg W 𝒮 φ A' : ℝ) := by
    have h := sum_card_filter_union_le (newPairs W 𝒮) (pimg φ) r (fun p hp => by
      have hp' := mem_filter.1 hp
      obtain ⟨hH, he⟩ := mem_sigma.1 hp'.1
      exact (card_embedEdge_le _ _).trans (hunif p.1 (h𝒮 hH) p.2 he).le) A' b
    unfold totDeg
    exact_mod_cast h
  have hA' : A'.card + 1 ≤ r := by omega
  have htot := totDeg_bound hD0 hends hdeg href hint hbd h𝒮 hacc A' hA'
  -- comparison of thresholds
  have hKA' : Q * (c2 + K A'.card) ≤ K j := by
    have hj1 : j = (j - 1) + 1 := by omega
    have hmono : K A'.card ≤ K (j - 1) := Kseq_mono hQ1 hc20 (by omega)
    rw [hj1]
    show Q * (c2 + K A'.card) ≤ Q * (c2 + K (j - 1))
    nlinarith
  have hpow : (n : ℝ) ^ (r - 1 - A'.card) = (n : ℝ) ^ (r - 1 - j) * (n : ℝ) ^ b := by
    rw [← pow_add]; congr 1; omega
  have hmain : ((satSets W 𝒮 φ Q D C r A' b).card : ℝ) * thr Q c2 D n r j ≤
      2 ^ (r + 1) / Q * (n : ℝ) ^ b * thr Q c2 D n r j := by
    have e1 : ((satSets W 𝒮 φ Q D C r A' b).card : ℝ) * thr Q c2 D n r j ≤
        2 ^ (r + 1) * ((c2 + K A'.card) * D * (n : ℝ) ^ (r - 1 - A'.card)) := by
      have := hsum1.trans (hsum2.trans hsum3)
      have h2r : (0 : ℝ) ≤ 2 ^ r := by positivity
      have := mul_le_mul_of_nonneg_left htot h2r
      rw [pow_succ]
      nlinarith
    have e2 : 2 ^ (r + 1) * ((c2 + K A'.card) * D * (n : ℝ) ^ (r - 1 - A'.card)) ≤
        2 ^ (r + 1) / Q * (n : ℝ) ^ b * thr Q c2 D n r j := by
      unfold thr
      rw [hpow]
      have hQ0 : 0 < Q := by linarith
      have hX : 0 ≤ D * (n : ℝ) ^ (r - 1 - j) * (n : ℝ) ^ b := by positivity
      have : (c2 + K A'.card) ≤ K j / Q := by rw [le_div_iff₀ hQ0]; linarith
      calc 2 ^ (r + 1) * ((c2 + K A'.card) * D * ((n : ℝ) ^ (r - 1 - j) * (n : ℝ) ^ b))
          = 2 ^ (r + 1) * ((c2 + K A'.card) * (D * (n : ℝ) ^ (r - 1 - j) * (n : ℝ) ^ b)) := by
            ring
        _ ≤ 2 ^ (r + 1) * (K j / Q * (D * (n : ℝ) ^ (r - 1 - j) * (n : ℝ) ^ b)) := by gcongr
        _ = 2 ^ (r + 1) / Q * (n : ℝ) ^ b * (K j * D * (n : ℝ) ^ (r - 1 - j)) := by ring
    exact e1.trans e2
  exact le_of_mul_le_mul_right hmain hθpos

end RefinedAbsorption
