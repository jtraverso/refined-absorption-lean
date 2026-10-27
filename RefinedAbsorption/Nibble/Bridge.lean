module
public import RefinedAbsorption.WeightedNibbleBridge
public import RefinedAbsorption.Nibble.Main

/-!
# The nibble with leftover degree control, proved

We apply the nibble with test sets (`Nibble.nearRegularNibble`, proved from scratch in
`RequestProject/Nibble/`) to the auxiliary `binom(q,r)`-uniform hypergraph whose vertices are the
edges of `G` and whose edges are the edge sets of the cliques of `H`, with one test set
`{e ∈ G : S ⊆ e}` for every `(r-1)`-set `S`.  This proves `NibbleLeftoverDegree`
(`nibbleLeftoverDegree_proved`), hence Corollary 2.4 of the survey without any assumption
(`nibbleWithReserves_proved`), and reduces the Existence Conjecture to `RefinerWithAbsorbers`
alone (`steinerExistence_of_refinerWithAbsorbers`).
-/

@[expose] public section

namespace RefinedAbsorption

open Finset Filter Nibble

/-- In the auxiliary hypergraph the degree of an `r`-set `e` is its clique multiplicity. -/
theorem card_star_auxEdges {n q r : ℕ} {G H : Finset (Finset (Fin n))} (hr : 1 ≤ r) (hrq : r < q)
    (hH : H ⊆ cliquesOf q r G) {e : Finset (Fin n)} (he : e.card = r) :
    (Nibble.star (auxEdges r H) e).card = cliqueMult H e := by
  unfold Nibble.star auxEdges cliqueMult
  rw [filter_image, card_image_of_injOn
    (fun Q₁ h₁ Q₂ h₂ heq => auxEdges_injOn hr hrq hH (mem_filter.1 h₁).1 (mem_filter.1 h₂).1 heq)]
  congr 1
  ext Q
  simp only [mem_filter, cliqueEdges, mem_powersetCard, he, and_true]

/-- **Nibble with leftover degree control, packing inside `H`.**  The same statement as
`NibbleLeftoverDegree`, with the additional conclusion that the packing only uses cliques of the
given family `H`. -/
def NibbleLeftoverDegreeSub : Prop :=
  ∀ q r : ℕ, 1 ≤ r → r < q → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ β : ℝ, 0 < β → β < 1 →
    ∃ γ : ℝ, 0 < γ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G ⊆ completeRGraph (Fin n) r, ∀ H ⊆ cliquesOf q r G,
      (∀ e ∈ G, |(cliqueMult H e : ℝ) - ρ * (n.choose (q - r))|
          ≤ (n : ℝ) ^ (-β) * (n.choose (q - r))) →
      ∃ P ⊆ H, IsPacking q r G P ∧ MaxDegLE r (G \ coveredEdges r P) ((n : ℝ) ^ (1 - γ))

set_option maxHeartbeats 1000000 in
/-- **The nibble with leftover degree control, packing inside `H`** (proved). -/
theorem nibbleLeftoverDegreeSub_proved : NibbleLeftoverDegreeSub := by
  intro q r hr hrq ρ hρ hρ1 β hβ hβ1
  set s : ℕ := q - r with hs
  have hs1 : 1 ≤ s := by omega
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  set k : ℕ := q.choose r with hk
  have hk2 : 2 ≤ k := two_le_choose_of_lt hr hrq
  set δ : ℝ := min (1 / (4 * s)) (β / (2 * s)) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hsδ1 : (s : ℝ) * δ ≤ 1 / 4 := by
    have : δ ≤ 1 / (4 * s) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hsδβ : (s : ℝ) * δ ≤ β / 2 := by
    have : δ ≤ β / (2 * s) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hδ1 : δ ≤ 1 := by nlinarith
  obtain ⟨c, hc0, Δ₀, hΔ₀⟩ := nearRegularNibble k hk2 δ hδ0 hδ1 (r + 1)
  set γ : ℝ := min (c / 2) (1 / 2) with hγ
  have hγ0 : 0 < γ := lt_min (by positivity) (by norm_num)
  have hγc : γ < c := by have := min_le_left (c / 2) (1 / 2); linarith
  have hγ1 : γ ≤ 1 / 2 := min_le_right _ _
  set c₁ : ℝ := 1 / (2 ^ s * (s.factorial : ℝ)) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set A : ℝ := ρ * c₁ with hA
  have hA0 : 0 < A := mul_pos hρ hc₁0
  have ev : ∀ᶠ x : ℝ in atTop, (2 * s : ℝ) ≤ x ∧ x ^ (-β) ≤ ρ / 2 ∧ Δ₀ ≤ A * x ∧
      x ^ (-β) ≤ ρ / 4 * x ^ (-(β / 2)) ∧
      x ^ ((s : ℝ) - 1) ≤ A ^ (1 - δ) * x ^ ((s : ℝ) - 1 / 4) ∧
      1 ≤ A ^ (r + 1) * x ∧ x ^ (-c) ≤ A ^ c * x ^ (-γ) ∧
      x ^ (1 / 4 : ℝ) ≤ 1 / 2 * x ^ (1 / 2 : ℝ) ∧ 1 ≤ x := by
    have e2 : ∀ᶠ x : ℝ in atTop, x ^ (-β) ≤ ρ / 2 := by
      filter_upwards [eventually_rpow_le_mul_rpow (show -β < 0 by linarith)
        (show (0 : ℝ) < ρ / 2 by positivity), eventually_gt_atTop 0] with x hx hx0
      simpa using hx
    have e3 : ∀ᶠ x : ℝ in atTop, Δ₀ ≤ A * x :=
      (tendsto_id.const_mul_atTop hA0).eventually (eventually_ge_atTop _)
    have e6 : ∀ᶠ x : ℝ in atTop, 1 ≤ A ^ (r + 1) * x :=
      (tendsto_id.const_mul_atTop (pow_pos hA0 _)).eventually (eventually_ge_atTop _)
    filter_upwards [eventually_ge_atTop (2 * s : ℝ), e2, e3,
      eventually_rpow_le_mul_rpow (show -β < -(β / 2) by linarith) (show (0 : ℝ) < ρ / 4 by
        positivity),
      eventually_rpow_le_mul_rpow (show (s : ℝ) - 1 < s - 1 / 4 by linarith)
        (show 0 < A ^ (1 - δ) by positivity), e6,
      eventually_rpow_le_mul_rpow (show -c < -γ by linarith) (show 0 < A ^ c by positivity),
      eventually_rpow_le_mul_rpow (show (1 / 4 : ℝ) < 1 / 2 by norm_num)
        (show (0 : ℝ) < 1 / 2 by norm_num), eventually_ge_atTop 1]
      with x h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually ev)
  refine ⟨γ, hγ0, n₀, fun n hn G hG H hH hdegH => ?_⟩
  obtain ⟨Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9⟩ := hn₀ n hn
  have hn2s : 2 * s ≤ n := by exact_mod_cast Q1
  have hn1 : 1 ≤ n := by omega
  have hn1R : (1 : ℝ) ≤ n := Q9
  have hn0R : (0 : ℝ) < n := by linarith
  set C : ℝ := (n.choose s : ℝ) with hC
  have hClo : c₁ * (n : ℝ) ^ s ≤ C := by
    have := choose_lower_bound hn2s
    rw [hc₁]; rw [div_eq_mul_inv, mul_comm] at this; simpa [one_div] using this
  have hChi : C ≤ (n : ℝ) ^ s := by rw [hC]; exact_mod_cast Nat.choose_le_pow n s
  have hC0 : 0 ≤ C := Nat.cast_nonneg _
  set t : ℝ := (n : ℝ) ^ (-β) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hn0R.le _
  set Δ : ℝ := (ρ + t) * C with hΔ
  have hns : (n : ℝ) ≤ (n : ℝ) ^ s := le_self_pow₀ hn1R (by omega)
  have hΔlo : A * (n : ℝ) ^ s ≤ Δ := by
    have : A * (n : ℝ) ^ s = ρ * (c₁ * (n : ℝ) ^ s) := by rw [hA]; ring
    rw [this, hΔ]
    have : ρ * (c₁ * (n : ℝ) ^ s) ≤ ρ * C := mul_le_mul_of_nonneg_left hClo hρ.le
    nlinarith
  have hΔhi : Δ ≤ 2 * (n : ℝ) ^ s := by
    rw [hΔ]
    have : ρ + t ≤ 2 := by linarith
    calc (ρ + t) * C ≤ 2 * C := by gcongr
      _ ≤ 2 * (n : ℝ) ^ s := by gcongr
  have hAn : A * n ≤ Δ := le_trans (mul_le_mul_of_nonneg_left hns hA0.le) hΔlo
  have hΔ0 : 0 < Δ := lt_of_lt_of_le (mul_pos hA0 hn0R) hAn
  -- the tests
  set 𝒯 : Finset (Finset (Finset (Fin n))) :=
    (univ.powersetCard (r - 1)).image (fun S => G.filter (fun e => S ⊆ e)) with h𝒯
  have hnr : ((n : ℝ) ^ r) ≤ Δ ^ (r + 1) := by
    calc ((n : ℝ) ^ r) = (n : ℝ) ^ r * 1 := (mul_one _).symm
      _ ≤ (n : ℝ) ^ r * (A ^ (r + 1) * n) := by gcongr
      _ = (A * n) ^ (r + 1) := by ring
      _ ≤ Δ ^ (r + 1) := by gcongr
  have hGcard : (G.card : ℝ) ≤ Δ ^ (r + 1) := by
    refine le_trans ?_ hnr
    have h1 : G.card ≤ (completeRGraph (Fin n) r).card := card_le_card hG
    have h2 : (completeRGraph (Fin n) r).card ≤ n ^ r := by
      unfold completeRGraph; rw [card_powersetCard, card_univ, Fintype.card_fin]
      exact Nat.choose_le_pow n r
    exact_mod_cast h1.trans h2
  have h𝒯card : (𝒯.card : ℝ) ≤ Δ ^ (r + 1) := by
    refine le_trans ?_ hnr
    have h1 : 𝒯.card ≤ (univ.powersetCard (r - 1) : Finset (Finset (Fin n))).card :=
      card_image_le
    have h2 : (univ.powersetCard (r - 1) : Finset (Finset (Fin n))).card ≤ n ^ r := by
      rw [card_powersetCard, card_univ, Fintype.card_fin]
      exact (Nat.choose_le_pow n (r - 1)).trans (Nat.pow_le_pow_right hn1 (by omega))
    exact_mod_cast h1.trans h2
  -- degrees of the auxiliary hypergraph
  have hdeg : ∀ v ∈ G, Δ * (1 - Δ ^ (-δ)) ≤ (Nibble.star (auxEdges r H) v).card ∧
      ((Nibble.star (auxEdges r H) v).card : ℝ) ≤ Δ := by
    intro v hv
    have hvr : v.card = r := (mem_powersetCard.1 (hG hv)).2
    rw [card_star_auxEdges hr hrq hH hvr]
    have hb := abs_le.1 (hdegH v hv)
    refine ⟨?_, by rw [hΔ]; linarith⟩
    have hpow1 : (2 * (n : ℝ) ^ s) ^ (-δ) ≤ Δ ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos hΔ0 hΔhi (by linarith)
    have hpow2 : (2 * (n : ℝ) ^ s) ^ (-δ) = (2 : ℝ) ^ (-δ) * (n : ℝ) ^ ((s : ℝ) * (-δ)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_natCast_mul hn0R.le]
    have hpow3 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-δ) := by
      have : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (-δ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rwa [Real.rpow_neg_one, ← one_div] at this
    have hpow4 : (n : ℝ) ^ (-(β / 2)) ≤ (n : ℝ) ^ ((s : ℝ) * (-δ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
    have hlow : (1 / 2 : ℝ) * (n : ℝ) ^ (-(β / 2)) ≤ Δ ^ (-δ) := by
      rw [hpow2] at hpow1
      have h0 : 0 ≤ (n : ℝ) ^ (-(β / 2)) := Real.rpow_nonneg hn0R.le _
      calc (1 / 2 : ℝ) * (n : ℝ) ^ (-(β / 2)) ≤ (2 : ℝ) ^ (-δ) * (n : ℝ) ^ ((s : ℝ) * (-δ)) := by
            gcongr
        _ ≤ Δ ^ (-δ) := hpow1
    have hρC : ρ * C ≤ Δ := by rw [hΔ]; nlinarith
    have hkey : 2 * t * C ≤ Δ * Δ ^ (-δ) := by
      have h1 : 2 * t ≤ ρ / 2 * (n : ℝ) ^ (-(β / 2)) := by linarith
      have hD0 : 0 ≤ Δ ^ (-δ) := Real.rpow_nonneg hΔ0.le _
      calc 2 * t * C ≤ ρ / 2 * (n : ℝ) ^ (-(β / 2)) * C := by gcongr
        _ = ρ * C * ((1 / 2 : ℝ) * (n : ℝ) ^ (-(β / 2))) := by ring
        _ ≤ Δ * Δ ^ (-δ) := by
            gcongr
    have : Δ * (1 - Δ ^ (-δ)) = (ρ + t) * C - Δ * Δ ^ (-δ) := by rw [hΔ]; ring
    rw [this]
    linarith
  -- codegrees
  have hcod : ∀ u v : Finset (Fin n), u ≠ v →
      (codeg (auxEdges r H) u v : ℝ) ≤ Δ ^ (1 - δ) := by
    intro u v huv
    have h1 : codeg (auxEdges r H) u v ≤ n ^ (q - r - 1) := auxEdges_codeg_le hn1 hH huv
    have h2 : ((n ^ (q - r - 1) : ℕ) : ℝ) = (n : ℝ) ^ ((s : ℝ) - 1) := by
      push_cast
      rw [← Real.rpow_natCast]; congr 1
      rw [show q - r - 1 = s - 1 by omega]; push_cast [Nat.cast_sub hs1]; ring
    have h3 : (n : ℝ) ^ ((s : ℝ) - 1 / 4) ≤ (n : ℝ) ^ ((s : ℝ) * (1 - δ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1R (by
        have : (s : ℝ) * (1 - δ) = s - s * δ := by ring
        rw [this]; linarith)
    have h4 : A ^ (1 - δ) * (n : ℝ) ^ ((s : ℝ) * (1 - δ)) = (A * (n : ℝ) ^ s) ^ (1 - δ) := by
      rw [Real.mul_rpow hA0.le (by positivity), Real.rpow_natCast_mul hn0R.le]
    have h5 : (A * (n : ℝ) ^ s) ^ (1 - δ) ≤ Δ ^ (1 - δ) :=
      Real.rpow_le_rpow (by positivity) hΔlo (by linarith)
    calc (codeg (auxEdges r H) u v : ℝ) ≤ ((n ^ (q - r - 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (n : ℝ) ^ ((s : ℝ) - 1) := h2
      _ ≤ A ^ (1 - δ) * (n : ℝ) ^ ((s : ℝ) - 1 / 4) := Q5
      _ ≤ A ^ (1 - δ) * (n : ℝ) ^ ((s : ℝ) * (1 - δ)) := by gcongr
      _ = (A * (n : ℝ) ^ s) ^ (1 - δ) := h4
      _ ≤ Δ ^ (1 - δ) := h5
  have hEV : ∀ F ∈ auxEdges r H, F ⊆ G := by
    intro F hF
    obtain ⟨Q, hQ, rfl⟩ := mem_image.1 hF
    exact cliqueEdges_subset_of_mem_cliquesOf (hH hQ)
  obtain ⟨M, hMsub, hMdisj, hMT⟩ := hΔ₀ Δ (Q3.trans hAn) (Finset (Fin n)) (auxEdges r H) G 𝒯
    (auxEdges_card hH) hEV hdeg hcod (by exact_mod_cast hGcard) (by exact_mod_cast h𝒯card)
  obtain ⟨hP, hcovP⟩ := packing_of_auxMatching hr hrq hH hMsub hMdisj
  refine ⟨_, filter_subset _ _, hP, fun S hS => ?_⟩
  rw [hcovP]
  set TS := G.filter (fun e => S ⊆ e) with hTS
  have hTS𝒯 : TS ∈ 𝒯 := mem_image.2 ⟨S, mem_powersetCard.2 ⟨subset_univ _, by omega⟩, rfl⟩
  have hTSG : TS ∩ G = TS := inter_eq_left.2 (filter_subset _ _)
  have hdegeq : deg (G \ M.biUnion id) S = (TS \ cov M).card := by
    unfold deg cov
    congr 1
    ext e; simp only [TS, Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [hdegeq]
  have hTSn : (TS.card : ℝ) ≤ n := by exact_mod_cast deg_le_n hG hS
  have hn1γ : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ (1 - γ) :=
    Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
  by_cases hbig : Δ ^ δ ≤ (TS ∩ G).card
  · have h := hMT TS hTS𝒯 hbig
    rw [hTSG] at h
    have h1 : Δ ^ (-c) ≤ (A * n) ^ (-c) := Real.rpow_le_rpow_of_nonpos (by positivity) hAn
      (by linarith)
    have h2 : (A * n) ^ (-c) = A ^ (-c) * (n : ℝ) ^ (-c) := Real.mul_rpow hA0.le hn0R.le
    have h3 : A ^ (-c) * (n : ℝ) ^ (-c) ≤ (n : ℝ) ^ (-γ) := by
      have hAc : A ^ (-c) * A ^ c = 1 := by
        rw [← Real.rpow_add hA0]; simp
      calc A ^ (-c) * (n : ℝ) ^ (-c) ≤ A ^ (-c) * (A ^ c * (n : ℝ) ^ (-γ)) := by gcongr
        _ = (n : ℝ) ^ (-γ) := by rw [← mul_assoc, hAc, one_mul]
    have h4 : (n : ℝ) ^ (-γ) * n = (n : ℝ) ^ (1 - γ) := by
      rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add hn0R, Real.rpow_one]
    have hΔc0 : 0 ≤ Δ ^ (-c) := Real.rpow_nonneg hΔ0.le _
    calc ((TS \ cov M).card : ℝ) ≤ Δ ^ (-c) * TS.card := h
      _ ≤ Δ ^ (-c) * n := by gcongr
      _ ≤ (n : ℝ) ^ (-γ) * n := by
          gcongr
          rw [← h2] at h3
          exact h1.trans h3
      _ = (n : ℝ) ^ (1 - γ) := h4
  · push_neg at hbig
    rw [hTSG] at hbig
    have h1 : ((TS \ cov M).card : ℝ) ≤ TS.card := by exact_mod_cast card_le_card sdiff_subset
    have h2 : Δ ^ δ ≤ (2 * (n : ℝ) ^ s) ^ δ := Real.rpow_le_rpow hΔ0.le hΔhi hδ0.le
    have h3 : (2 * (n : ℝ) ^ s) ^ δ = (2 : ℝ) ^ δ * (n : ℝ) ^ ((s : ℝ) * δ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_natCast_mul hn0R.le]
    have h4 : (2 : ℝ) ^ δ ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hδ1
      rwa [Real.rpow_one] at this
    have h5 : (n : ℝ) ^ ((s : ℝ) * δ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1R hsδ1
    have h6 : (2 : ℝ) ^ δ * (n : ℝ) ^ ((s : ℝ) * δ) ≤ 2 * (n : ℝ) ^ (1 / 4 : ℝ) := by
      gcongr
    linarith

/-- **The nibble with leftover degree control** (proved). -/
theorem nibbleLeftoverDegree_proved : NibbleLeftoverDegree := by
  intro q r hr hrq ρ hρ hρ1 β hβ hβ1
  obtain ⟨γ, hγ, n₀, h⟩ := nibbleLeftoverDegreeSub_proved q r hr hrq ρ hρ hρ1 β hβ hβ1
  refine ⟨γ, hγ, n₀, fun n hn G hG H hH hdeg => ?_⟩
  obtain ⟨P, -, hP, hP'⟩ := h n hn G hG H hH hdeg
  exact ⟨P, hP, hP'⟩

/-- **Corollary 2.4, exactly as stated in the survey** (proved). -/
theorem nibbleWithReserves_proved : NibbleWithReserves :=
  nibbleWithReserves_of_nibbleLeftoverDegree nibbleLeftoverDegree_proved

/-- **Corollary 2.4 with general polynomial error** (proved). -/
theorem nibbleWithReservesGen_proved : NibbleWithReservesGen :=
  nibbleWithReservesGen_of_nibbleLeftoverDegree nibbleLeftoverDegree_proved

/-- **The Existence Conjecture for Steiner systems** from `RefinerWithAbsorbers` alone. -/
theorem steinerExistence_of_refinerWithAbsorbers (hRef : RefinerWithAbsorbers) :
    SteinerExistenceConjecture :=
  steinerExistence_of_refinerWithAbsorbers_nibbleLeftoverDegree hRef nibbleLeftoverDegree_proved

end RefinedAbsorption
