module
public import RequestProject.Multigraph.NibbleMulti
public import RequestProject.Pending.Danger

/-!
# The nibble with reserves avoiding a sparse forbidden family

`safeNibbleWithReserves`: Corollary 2.4 (nibble with reserves) with the additional property that
the packing avoids a prescribed family `Φ` of `q`-sets, provided every `r`-set lies in at most
`K n^(q-r-1)` members of `Φ`.  Both phases are modified as in Section 6.3 of arXiv:2402.17855v1:
the nibble runs on `H \ Φ` (whose degrees are still `(ρ ± n^(-β/2)) binom(n, q-r)`), and the
reserve covering only uses reserve cliques outside `Φ` (`reserve_cover_multi` with one layer).
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset Filter

/-- Removing `K n^(k-1)` cliques per edge costs less than the change of error from `n^(-β)` to
`n^(-β/2)`. -/
theorem ev_removal_poly {k : ℕ} (hk : 1 ≤ k) {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K * (n : ℝ) ^ (k - 1) + (n : ℝ) ^ (-β) * (n.choose k) ≤
      (n : ℝ) ^ (-(β / 2)) * (n.choose k) := by
  have hF : (0 : ℝ) < 2 ^ k * (k.factorial : ℝ) := by positivity
  have e1 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-β) ≤ (1 / 2) * (n : ℝ) ^ (-(β / 2)) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_rpow_le_mul_rpow (show -β < -(β / 2) by linarith) (by norm_num))
  have hβ' : 0 < 1 - β / 2 := by linarith
  filter_upwards [eventually_ge_atTop (2 * k), eventually_ge_atTop 1, e1,
    ev_le_rpow (2 * |K| * (2 ^ k * (k.factorial : ℝ))) hβ'] with n hn hn1 h1 h2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hB := choose_lower_bound hn
  have hB0 : (0 : ℝ) ≤ n.choose k := by positivity
  have hp : (0 : ℝ) ≤ (n : ℝ) ^ (-(β / 2)) := by positivity
  have hpk : (0 : ℝ) ≤ (n : ℝ) ^ (k - 1) := by positivity
  have e2 : (n : ℝ) ^ (-(β / 2)) * ((n : ℝ) ^ k / (2 ^ k * k.factorial)) =
      (n : ℝ) ^ (1 - β / 2) * (n : ℝ) ^ (k - 1) / (2 ^ k * k.factorial) := by
    have : (n : ℝ) ^ k = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (k - 1) := by
      rw [Real.rpow_one, ← pow_succ']
      congr 1; omega
    rw [this, mul_div_assoc', ← mul_assoc, ← Real.rpow_add hn0]
    ring_nf
  have h3 : K * (n : ℝ) ^ (k - 1) ≤ (1 / 2) * ((n : ℝ) ^ (-(β / 2)) * (n.choose k)) := by
    have h4 : (n : ℝ) ^ (-(β / 2)) * ((n : ℝ) ^ k / (2 ^ k * k.factorial)) ≤
        (n : ℝ) ^ (-(β / 2)) * (n.choose k) := mul_le_mul_of_nonneg_left hB hp
    rw [e2] at h4
    have h5 : 2 * |K| * (n : ℝ) ^ (k - 1) ≤
        (n : ℝ) ^ (1 - β / 2) * (n : ℝ) ^ (k - 1) / (2 ^ k * k.factorial) := by
      rw [le_div_iff₀ hF]
      nlinarith
    have h6 : K * (n : ℝ) ^ (k - 1) ≤ |K| * (n : ℝ) ^ (k - 1) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) hpk
    linarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hB0]

/-- `K n^(k-1) + n^(k-s) ≤ n^(k-s/2)` for large `n`, if `0 < s < 2`. -/
theorem ev_reserve_slack_poly {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K * (n : ℝ) ^ (k - 1) + (n : ℝ) ^ ((k : ℝ) - s) ≤
      (n : ℝ) ^ ((k : ℝ) - s / 2) := by
  have e1 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ((k : ℝ) - s) ≤ (1 / 2) * (n : ℝ) ^ ((k : ℝ) - s / 2) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_rpow_le_mul_rpow (show (k : ℝ) - s < k - s / 2 by linarith) (by norm_num))
  have hs' : 0 < 1 - s / 2 := by linarith
  filter_upwards [eventually_ge_atTop 1, e1, ev_le_rpow (2 * |K|) hs'] with n hn1 h1 h2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpk : (0 : ℝ) ≤ (n : ℝ) ^ (k - 1) := by positivity
  have e2 : (n : ℝ) ^ ((k : ℝ) - s / 2) = (n : ℝ) ^ (1 - s / 2) * (n : ℝ) ^ (k - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0, Nat.cast_sub hk]
    ring_nf
  have h6 : K * (n : ℝ) ^ (k - 1) ≤ |K| * (n : ℝ) ^ (k - 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) hpk
  have h7 : 2 * |K| * (n : ℝ) ^ (k - 1) ≤ (n : ℝ) ^ ((k : ℝ) - s / 2) := by
    rw [e2]; exact mul_le_mul_of_nonneg_right h2 hpk
  linarith

/-- With one layer, the layer count is the indicator of the layer. -/
theorem layerCount_one {V : Type*} [DecidableEq V] (R : ℕ → Finset (Finset V)) (T : Finset V) :
    layerCount 1 R T = if T ∈ R 0 then 1 else 0 := by
  rw [layerCount_succ, layerCount_zero, zero_add]

/-- **Nibble with reserves avoiding a sparse forbidden family.** -/
theorem safeNibbleWithReserves (q r : ℕ) (hr : 1 ≤ r) (hrq : r < q) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (K : ℝ) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G ⊆ completeRGraph (Fin n) r,
      ∀ H ⊆ cliquesOf q r G,
      (∀ e ∈ G, |(cliqueMult H e : ℝ) - ρ * (n.choose (q - r))|
          ≤ (n : ℝ) ^ (-β) * (n.choose (q - r))) →
      ∀ X ⊆ completeRGraph (Fin n) r \ G,
      (∀ e ∈ G, (n : ℝ) ^ ((q : ℝ) - r - α) ≤ (reserveCliques q r X e).card) →
      ∀ Φ : Finset (Finset (Fin n)),
      (∀ e : Finset (Fin n), e.card = r → (cliqueMult Φ e : ℝ) ≤ K * (n : ℝ) ^ (q - r - 1)) →
        ∃ P, IsPacking q r (G ∪ X) P ∧ G ⊆ coveredEdges r P ∧ Disjoint P Φ := by
  obtain ⟨γ, hγ, n₀, hn₀⟩ := nibbleLeftoverDegreeSub_proved q r hr hrq ρ hρ hρ1 (β / 2)
    (by positivity) (by linarith)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set α' : ℝ := min (γ / (4 * r)) (1 / 2) with hα'def
  have hα' : 0 < α' := lt_min (by positivity) (by norm_num)
  have hα'2 : α' ≤ 1 / 2 := min_le_right _ _
  have hα'γ : 4 * α' * r ≤ γ := by
    have : α' ≤ γ / (4 * r) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hk : 1 ≤ q - r := by omega
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (reserve_cover_multi q r hr hrq 1 hα' hα'2 hα'γ)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (ev_removal_poly hk hβ hβ1 K)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (ev_reserve_slack_poly hk hα' (by linarith) K)
  refine ⟨α' / 2, by positivity, by linarith, max (max n₀ N₁) (max N₂ N₃),
    fun n hn G hGK H hHG hH X hXK hres Φ hΦ => ?_⟩
  have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) (le_max_left _ _) |>.trans hn
  have hN₁' : N₁ ≤ n := le_trans (le_max_right _ _) (le_max_left _ _) |>.trans hn
  have hN₂' : N₂ ≤ n := le_trans (le_max_left _ _) (le_max_right _ _) |>.trans hn
  have hN₃' : N₃ ≤ n := le_trans (le_max_right _ _) (le_max_right _ _) |>.trans hn
  have hqr : ((q - r : ℕ) : ℝ) = (q : ℝ) - r := by rw [Nat.cast_sub hrq.le]
  have hGr : ∀ e ∈ G, e.card = r := fun e he => (mem_powersetCard.1 (hGK he)).2
  -- the main phase on `H \ Φ`
  have hH'G : H \ Φ ⊆ cliquesOf q r G := sdiff_subset.trans hHG
  have hreg : ∀ e ∈ G, |(cliqueMult (H \ Φ) e : ℝ) - ρ * (n.choose (q - r))|
      ≤ (n : ℝ) ^ (-(β / 2)) * (n.choose (q - r)) := by
    intro e he
    have h1 : (cliqueMult (H \ Φ) e : ℝ) ≤ cliqueMult H e := by
      exact_mod_cast cliqueMult_sdiff_le H Φ e
    have h2 : (cliqueMult H e : ℝ) ≤ cliqueMult (H \ Φ) e + cliqueMult Φ e := by
      exact_mod_cast cliqueMult_le_sdiff_add H Φ e
    have h3 := hΦ e (hGr e he)
    have h4 := hH e he
    have h5 := hN₂ n hN₂'
    have h0 : (0 : ℝ) ≤ cliqueMult Φ e := Nat.cast_nonneg _
    rw [abs_le] at h4 ⊢
    constructor <;> linarith [h4.1, h4.2]
  obtain ⟨P₁, hP₁H, hP₁, hdeg⟩ := hn₀ n hn₀' G hGK (H \ Φ) hH'G hreg
  have hGX : Disjoint G X := by
    rw [disjoint_right]; intro f hf hfG
    exact (mem_sdiff.1 (hXK hf)).2 hfG
  set L := G \ coveredEdges r P₁ with hLdef
  have hLK : L ⊆ completeRGraph (Fin n) r := sdiff_subset.trans hGK
  -- the reserve phase, avoiding `Φ`
  have hresL : ∀ j < 1, ∀ e ∈ (fun _ : ℕ => L) j,
      (n : ℝ) ^ ((q : ℝ) - r - α') ≤ (reserveCliques q r X e \ Φ).card := by
    intro j _ e he
    have heG : e ∈ G := (mem_sdiff.1 he).1
    have h1 : ((reserveCliques q r X e).card : ℝ) ≤
        (reserveCliques q r X e \ Φ).card + cliqueMult Φ e := by
      exact_mod_cast card_reserveCliques_sdiff X Φ e
    have h2 := hres e heG
    have h3 := hΦ e (hGr e heG)
    have h4 := hN₃ n hN₃'
    rw [hqr] at h4
    have e1 : (q : ℝ) - r - α' / 2 = (q : ℝ) - r - α' / 2 := rfl
    have e2 : (q : ℝ) - r - α' = ((q : ℝ) - r) - α' := rfl
    linarith
  obtain ⟨P₂, hP₂card, hP₂Φ, hP₂mult⟩ := hN₁ n hN₁' (fun _ => L) X Φ (fun _ _ => hLK)
    (fun _ _ => hdeg) hresL
  have hLX : Disjoint L X := disjoint_of_subset_left sdiff_subset hGX
  have hP₂ : IsPacking q r (L ∪ X) P₂ := by
    refine ⟨hP₂card, fun Q hQ f hf => ?_, fun f hf => ?_⟩
    · obtain ⟨hfQ, hfc⟩ := mem_powersetCard.1 hf
      have h1 : 1 ≤ cliqueMult P₂ f := card_pos.2 ⟨Q, mem_filter.2 ⟨hQ, hfQ⟩⟩
      have h2 := (hP₂mult f hfc).2
      rw [layerCount_one] at h2
      rw [mem_union]
      by_contra hno
      push_neg at hno
      simp only [hno.1, hno.2, if_false] at h2
      omega
    · have h2 := (hP₂mult f hf).2
      rw [layerCount_one] at h2
      by_cases hfL : f ∈ L
      · have hfX : f ∉ X := disjoint_left.1 hLX hfL
        simp only [hfL, hfX, if_true, if_false] at h2
        exact h2
      · simp only [hfL, if_false, zero_add] at h2
        split_ifs at h2 <;> omega
  have hcovL : L ⊆ coveredEdges r P₂ := by
    intro e he
    have h1 := (hP₂mult e (hGr e (mem_sdiff.1 he).1)).1
    rw [layerCount_one] at h1
    simp only [he, if_true] at h1
    obtain ⟨Q, hQ⟩ := card_pos.1 (show 0 < cliqueMult P₂ e by omega)
    obtain ⟨hQP, heQ⟩ := mem_filter.1 hQ
    exact mem_biUnion.2 ⟨Q, hQP, mem_powersetCard.2 ⟨heQ, hGr e (mem_sdiff.1 he).1⟩⟩
  refine ⟨P₁ ∪ P₂, hP₁.union_leftover hP₂ hGX Subset.rfl, fun e he => ?_, ?_⟩
  · by_cases hc : e ∈ coveredEdges r P₁
    · obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.1 hc
      exact mem_biUnion.2 ⟨Q, mem_union_left _ hQ, heQ⟩
    · obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.1 (hcovL (mem_sdiff.2 ⟨he, hc⟩))
      exact mem_biUnion.2 ⟨Q, mem_union_right _ hQ, heQ⟩
  · rw [disjoint_union_left]
    refine ⟨?_, hP₂Φ⟩
    rw [disjoint_left]
    intro Q hQ hQΦ
    exact (mem_sdiff.1 (hP₁H hQ)).2 hQΦ

end RefinedAbsorption.Pending
