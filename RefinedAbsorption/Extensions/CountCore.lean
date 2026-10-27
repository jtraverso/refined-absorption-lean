module
public import RefinedAbsorption.Designs
public import RefinedAbsorption.Extensions.Partial

/-!
# Counting Steiner systems through their restrictions to a small set

If every partial Steiner system with `k` blocks inside a set `U` of size `u` extends to a
Steiner system on `Fin n`, then the number of `(n, q, r)`-Steiner systems is at least
`|PS_k(U)| / 2^{binom(u, r)}`: every partial system lies in the restriction to `U` of some
Steiner system, and a restriction (a partial system inside `U`) has at most `binom(u, r)` blocks.
-/

@[expose] public section

namespace RefinedAbsorption.Extensions

open Finset

open Classical in
/-- The set of all `(n, q, r)`-Steiner systems on `Fin n`. -/
noncomputable def steinerSystems (q r n : ℕ) : Finset (Finset (Finset (Fin n))) :=
  univ.filter (fun 𝒮 => IsSteinerSystem q r 𝒮)

variable {V : Type*} [DecidableEq V]

/-- A partial Steiner system whose blocks lie in `U` has at most `binom(|U|, r)` blocks. -/
theorem IsPartialSteinerSystem.card_le {q r : ℕ} (hrq : r ≤ q) {U : Finset V}
    {R : Finset (Finset V)} (hR : IsPartialSteinerSystem q r R) (hRU : ∀ Q ∈ R, Q ⊆ U) :
    R.card ≤ U.card.choose r := by
  classical
  have h1 : R.card ≤ (R.sigma (fun Q => Q.powersetCard r)).card := by
    rw [card_sigma]
    calc R.card = ∑ _Q ∈ R, 1 := by simp
      _ ≤ _ := sum_le_sum fun Q hQ => by
        rw [card_powersetCard, hR.1 Q hQ]; exact Nat.one_le_iff_ne_zero.2
          (Nat.choose_pos hrq).ne'
  refine h1.trans ?_
  rw [← card_powersetCard]
  refine card_le_card_of_injOn (fun x => x.2) ?_ ?_
  · intro x hx
    rw [mem_coe, mem_sigma] at hx
    exact mem_powersetCard.2 ⟨(mem_powersetCard.1 hx.2).1.trans (hRU _ hx.1),
      (mem_powersetCard.1 hx.2).2⟩
  · intro x hx y hy hxy
    rw [mem_coe, mem_sigma] at hx hy
    simp only at hxy
    have hT := (mem_powersetCard.1 hx.2).2
    have hm := hR.2 x.2 hT
    have hxy1 : x.1 = y.1 := by
      by_contra hne
      have : ({x.1, y.1} : Finset (Finset V)) ⊆ R.filter (fun Q => x.2 ⊆ Q) := by
        intro Q hQ
        rcases mem_insert.1 hQ with rfl | hQ
        · exact mem_filter.2 ⟨hx.1, (mem_powersetCard.1 hx.2).1⟩
        · rw [mem_singleton.1 hQ]
          exact mem_filter.2 ⟨hy.1, hxy ▸ (mem_powersetCard.1 hy.2).1⟩
      have := card_le_card this
      rw [card_pair hne] at this
      unfold cliqueMult at hm
      omega
    exact Sigma.ext hxy1 (heq_of_eq hxy)

/-- A Steiner system is a partial Steiner system. -/
theorem IsSteinerSystem.isPartial {n q r : ℕ} {𝒮 : Finset (Finset (Fin n))}
    (h : IsSteinerSystem q r 𝒮) : IsPartialSteinerSystem q r 𝒮 :=
  ⟨h.card_eq, fun T hT => (h.mult_eq T hT).le⟩

/-- Subfamilies of partial Steiner systems are partial Steiner systems. -/
theorem IsPartialSteinerSystem.mono {q r : ℕ} {R R' : Finset (Finset V)}
    (h : IsPartialSteinerSystem q r R) (hR : R' ⊆ R) : IsPartialSteinerSystem q r R' :=
  ⟨fun Q hQ => h.1 Q (hR hQ), fun T hT =>
    (card_le_card (filter_subset_filter _ hR)).trans (h.2 T hT)⟩

/-- **Counting through restrictions.**  If every partial Steiner system with `k` blocks inside
`U` extends to an `(n, q, r)`-Steiner system, then
`|PS_k(U)| ≤ #(Steiner systems) · 2^{binom(|U|, r)}`. -/
theorem card_psFamily_le_steiner {n q r k : ℕ} (hrq : r ≤ q) (U : Finset (Fin n))
    (hext : ∀ P ∈ psFamily q r k U, ∃ 𝒮 : Finset (Finset (Fin n)),
      P ⊆ 𝒮 ∧ IsSteinerSystem q r 𝒮) :
    (psFamily q r k U).card ≤ (steinerSystems q r n).card * 2 ^ (U.card.choose r) := by
  classical
  have hsub : psFamily q r k U ⊆ (steinerSystems q r n).biUnion
      (fun 𝒮 => (𝒮.filter (fun Q => Q ⊆ U)).powersetCard k) := by
    intro P hP
    obtain ⟨𝒮, hP𝒮, h𝒮⟩ := hext P hP
    have hP' := hP
    simp only [psFamily, mem_filter, mem_powersetCard] at hP'
    refine mem_biUnion.2 ⟨𝒮, by simp [steinerSystems, h𝒮], mem_powersetCard.2 ⟨?_, hP'.1.2⟩⟩
    intro Q hQ
    exact mem_filter.2 ⟨hP𝒮 hQ, (mem_powersetCard.1 (hP'.1.1 hQ)).1⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun 𝒮 h𝒮 => ?_
  have h𝒮' : IsSteinerSystem q r 𝒮 := by simpa [steinerSystems] using h𝒮
  rw [card_powersetCard]
  refine (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) ?_)
  exact ((IsSteinerSystem.isPartial h𝒮').mono (filter_subset _ _)).card_le hrq (fun Q hQ => (mem_filter.1 hQ).2)

end RefinedAbsorption.Extensions
