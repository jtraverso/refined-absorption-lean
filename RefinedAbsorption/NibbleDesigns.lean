module
public import RefinedAbsorption.Nibble.LocalMain
public import RefinedAbsorption.Nibble.Bridge

/-!
# Theorem 1.3 (Nibble for designs), with no bound on the number of vertices

* `nibbleCover`: a `k`-uniform hypergraph with all degrees in `[Δ(1 - Δ^{-δ}), Δ]` and all
  codegrees at most `Δ^{1-δ}` has a matching covering all but at most `Δ^{-c} |V|` vertices, for
  some `c = c(k, δ) > 0` and all large `Δ`.  There is **no** assumption on `|V|`: the vertex
  set is cut into chunks of size between `Δ^{δ/2}` and `2Δ^{δ/2}`, which are used as test sets
  of the nibble with local test sets (`localNibble`, proved with the Lovász Local Lemma).
* `nibbleForDesigns`: Theorem 1.3 of the survey exactly as stated in `NibbleForDesigns`
  (`RequestProject/Statements.lean`), applied to the auxiliary hypergraph whose vertices are
  the edges of `G` and whose edges are the edge sets of the cliques of `H`.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset Filter Nibble

/-! ### Cutting a finite set into chunks -/

/-- A finite set with at least `m ≥ 1` elements can be cut into pairwise disjoint chunks whose
sizes lie in `[m, 2m)`. -/
theorem exists_chunks {α : Type*} [DecidableEq α] (m : ℕ) (hm : 1 ≤ m) :
    ∀ V : Finset α, m ≤ V.card → ∃ Ps : Finset (Finset α),
      (∀ P ∈ Ps, ∀ P' ∈ Ps, P ≠ P' → Disjoint P P') ∧ Ps.biUnion id = V ∧
      ∀ P ∈ Ps, m ≤ P.card ∧ P.card < 2 * m := by
  intro V
  induction h : V.card using Nat.strong_induction_on generalizing V with
  | _ N ih =>
  intro hmV
  rw [← h] at hmV
  by_cases hlt : V.card < 2 * m
  · refine ⟨{V}, ?_, by simp, ?_⟩
    · intro P hP P' hP' hne
      rw [mem_singleton] at hP hP'
      exact absurd (hP.trans hP'.symm) hne
    · intro P hP
      rw [mem_singleton] at hP
      subst hP; exact ⟨hmV, hlt⟩
  · obtain ⟨P, hPV, hPc⟩ := exists_subset_card_eq hmV
    have hc : (V \ P).card = V.card - m := by rw [card_sdiff_of_subset hPV, hPc]
    obtain ⟨Ps', h1, h2, h3⟩ := ih (V \ P).card (by omega) (V \ P) rfl (by omega)
    have hsub : ∀ P' ∈ Ps', P' ⊆ V \ P := fun P' hP' => by
      rw [← h2]; exact subset_biUnion_of_mem id hP'
    have hPne : P.Nonempty := card_pos.1 (by omega)
    have hPnot : P ∉ Ps' := by
      intro hP
      obtain ⟨x, hx⟩ := hPne
      exact (Finset.mem_sdiff.1 (hsub P hP hx)).2 hx
    refine ⟨insert P Ps', ?_, ?_, ?_⟩
    · intro A hA B hB hne
      rcases mem_insert.1 hA with hAP | hA' <;> rcases mem_insert.1 hB with hBP | hB'
      · exact absurd (hAP.trans hBP.symm) hne
      · rw [hAP, disjoint_left]; intro x hx hxB
        exact (Finset.mem_sdiff.1 (hsub B hB' hxB)).2 hx
      · rw [hBP, disjoint_left]; intro x hxA hx
        exact (Finset.mem_sdiff.1 (hsub A hA' hxA)).2 hx
      · exact h1 A hA' B hB' hne
    · rw [biUnion_insert, h2, id, union_sdiff_of_subset hPV]
    · intro A hA
      rcases mem_insert.1 hA with rfl | hA
      · exact ⟨hPc.ge, by omega⟩
      · exact h3 A hA

/-! ### The nibble covering all but a polynomially small fraction of the vertices -/

/-- In a hypergraph with degrees at least `Δ(1 - Δ^{-δ})` and codegrees at most `Δ^{1-δ}`, a
nonempty vertex set has at least `Δ^δ - 1` elements. -/
theorem card_ge_of_deg {α : Type*} [DecidableEq α] {k : ℕ} (hk2 : 2 ≤ k) {Δ δ : ℝ} (hΔ : 0 < Δ)
    {E : Finset (Finset α)} {V : Finset α} (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ v ∈ V, Δ * (1 - Δ ^ (-δ)) ≤ (star E v).card)
    (hcod : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ Δ ^ (1 - δ)) {v : α} (hv : v ∈ V) :
    Δ ^ δ - 1 ≤ V.card := by
  have h1 := sum_codeg_eq E (V.erase v) v
  have h2 : ∑ e ∈ star E v, (e ∩ V.erase v).card = ∑ e ∈ star E v, (k - 1) := by
    refine sum_congr rfl fun e he => ?_
    obtain ⟨heE, hve⟩ := mem_star.1 he
    have : e ∩ V.erase v = e.erase v := by
      ext x; simp only [mem_inter, mem_erase]
      constructor
      · rintro ⟨hx, hxv, _⟩; exact ⟨hxv, hx⟩
      · rintro ⟨hxv, hx⟩; exact ⟨hx, hxv, hEV e heE hx⟩
    rw [this, card_erase_of_mem hve, hk e heE]
  rw [h2, sum_const, smul_eq_mul] at h1
  have h3 : ((∑ u ∈ V.erase v, codeg E u v : ℕ) : ℝ) ≤ (V.erase v).card * Δ ^ (1 - δ) := by
    push_cast
    calc ∑ u ∈ V.erase v, (codeg E u v : ℝ) ≤ ∑ u ∈ V.erase v, Δ ^ (1 - δ) :=
          sum_le_sum fun u hu => hcod u v (ne_of_mem_erase hu)
      _ = (V.erase v).card * Δ ^ (1 - δ) := by rw [sum_const, nsmul_eq_mul]
  rw [h1] at h3
  push_cast at h3
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  have hkc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hkc] at h3
  have hdv := hdeg v hv
  have hst0 : (0 : ℝ) ≤ (star E v).card := Nat.cast_nonneg _
  have h4 : Δ * (1 - Δ ^ (-δ)) ≤ (V.erase v).card * Δ ^ (1 - δ) := by
    calc Δ * (1 - Δ ^ (-δ)) ≤ (star E v).card := hdv
      _ ≤ (star E v).card * ((k : ℝ) - 1) := le_mul_of_one_le_right hst0 hk1
      _ = ((k : ℝ) - 1) * (star E v).card := by ring
      _ ≤ _ := by linarith [h3]
  have hpos : 0 < Δ ^ (1 - δ) := Real.rpow_pos_of_pos hΔ _
  have h5 : Δ * (1 - Δ ^ (-δ)) = (Δ ^ δ - 1) * Δ ^ (1 - δ) := by
    have e1 : Δ = Δ ^ δ * Δ ^ (1 - δ) := by
      rw [← Real.rpow_add hΔ]; simp
    have e2 : Δ ^ (-δ) * Δ = Δ ^ (1 - δ) := by
      rw [← Real.rpow_add_one hΔ.ne']; congr 1; ring
    have : Δ * (1 - Δ ^ (-δ)) = Δ - Δ ^ (-δ) * Δ := by ring
    rw [this, e2]
    nth_rewrite 1 [e1]
    ring
  rw [h5] at h4
  have h6 : Δ ^ δ - 1 ≤ (V.erase v).card := le_of_mul_le_mul_right h4 hpos
  have h7 : ((V.erase v).card : ℝ) ≤ V.card := by exact_mod_cast card_erase_le
  linarith

/-- **The nibble without any bound on the number of vertices.**  For `k ≥ 2` and `δ ∈ (0,1]`
there are `c > 0` and `Δ₀` such that every `k`-uniform hypergraph with vertex degrees in
`[Δ(1 - Δ^{-δ}), Δ]` and codegrees at most `Δ^{1-δ}`, `Δ ≥ Δ₀`, has a matching covering all but
at most `Δ^{-c} |V|` vertices. -/
theorem nibbleCover (k : ℕ) (hk2 : 2 ≤ k) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ → ∀ (α : Type) [DecidableEq α]
      (E : Finset (Finset α)) (V : Finset α),
      (∀ F ∈ E, F.card = k) → (∀ F ∈ E, F ⊆ V) →
      (∀ v ∈ V, Δ * (1 - Δ ^ (-δ)) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ Δ) →
      (∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ Δ ^ (1 - δ)) →
      ∃ M ⊆ E, (∀ F₁ ∈ M, ∀ F₂ ∈ M, F₁ ≠ F₂ → Disjoint F₁ F₂) ∧
        ((V \ cov M).card : ℝ) ≤ Δ ^ (-c) * V.card := by
  obtain ⟨c, hc0, Δ₀, hΔ₀⟩ := localNibble k hk2 (δ / 2) (by positivity) (by linarith) 1
  refine ⟨c, hc0, ?_⟩
  have ev : ∀ᶠ Δ : ℝ in atTop, Δ₀ ≤ Δ ∧ 1 ≤ Δ ∧ 2 * (Δ ^ (δ / 2) + 1) ≤ Δ ∧
      Δ ^ (δ / 2) + 2 ≤ Δ ^ δ := by
    have e3 : ∀ᶠ Δ : ℝ in atTop, 2 * (Δ ^ (δ / 2) + 1) ≤ Δ := by
      have h1 := eventually_rpow_le_mul_rpow (show δ / 2 < 1 by linarith)
        (show (0 : ℝ) < 1 / 4 by norm_num)
      filter_upwards [h1, eventually_ge_atTop (4 : ℝ)] with Δ h hΔ
      rw [Real.rpow_one] at h
      linarith
    have e4 : ∀ᶠ Δ : ℝ in atTop, Δ ^ (δ / 2) + 2 ≤ Δ ^ δ := by
      have h1 := eventually_rpow_le_mul_rpow (show δ / 2 < δ by linarith)
        (show (0 : ℝ) < 1 / 2 by norm_num)
      have h2 : ∀ᶠ Δ : ℝ in atTop, 4 ≤ Δ ^ δ :=
        (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop 4)
      filter_upwards [h1, h2] with Δ h h'
      linarith
    filter_upwards [eventually_ge_atTop Δ₀, eventually_ge_atTop 1, e3, e4] with Δ h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨Δ₁, hΔ₁⟩ := eventually_atTop.1 ev
  refine ⟨Δ₁, fun Δ hΔ α _ E V hk hEV hdeg hcod => ?_⟩
  obtain ⟨hΔ0', hΔ1, hΔ2, hΔ3⟩ := hΔ₁ Δ hΔ
  have hΔpos : 0 < Δ := by linarith
  -- the degree and codegree hypotheses with `δ / 2`
  have hdeg' : ∀ v ∈ V, Δ * (1 - Δ ^ (-(δ / 2))) ≤ (star E v).card ∧
      ((star E v).card : ℝ) ≤ Δ := by
    intro v hv
    refine ⟨le_trans ?_ (hdeg v hv).1, (hdeg v hv).2⟩
    have : Δ ^ (-δ) ≤ Δ ^ (-(δ / 2)) := Real.rpow_le_rpow_of_exponent_le hΔ1 (by linarith)
    nlinarith
  have hcod' : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ Δ ^ (1 - δ / 2) := fun u v huv =>
    (hcod u v huv).trans (Real.rpow_le_rpow_of_exponent_le hΔ1 (by linarith))
  rcases V.eq_empty_or_nonempty with hV | ⟨v₀, hv₀⟩
  · exact ⟨∅, empty_subset _, by simp, by simp [hV]⟩
  set m : ℕ := ⌈Δ ^ (δ / 2)⌉₊ with hm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by
    rw [hm]; exact (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hΔpos _)).ne')
  have hmle : (m : ℝ) ≤ Δ ^ (δ / 2) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hmge : Δ ^ (δ / 2) ≤ m := Nat.le_ceil _
  have hVm : m ≤ V.card := by
    have h := card_ge_of_deg hk2 hΔpos hk hEV (fun v hv => (hdeg v hv).1) hcod hv₀
    have : (m : ℝ) ≤ V.card := by linarith
    exact_mod_cast this
  obtain ⟨Ps, hdisj, hcover, hsize⟩ := exists_chunks m hm1 V hVm
  have hPV : ∀ P ∈ Ps, P ⊆ V := fun P hP => by
    rw [← hcover]; exact subset_biUnion_of_mem id hP
  obtain ⟨M, hME, hMdisj, hMT⟩ := hΔ₀ Δ hΔ0' α E V Ps hk hEV hdeg' hcod'
    (fun T hT => by
      rw [pow_one]
      have h1 : (T.card : ℝ) < 2 * m := by exact_mod_cast (hsize T hT).2
      linarith)
    (fun w => by
      rw [pow_one]
      have : (Ps.filter (fun T => w ∈ T)).card ≤ 1 := by
        rw [card_le_one]
        intro A hA B hB
        by_contra hne
        exact disjoint_left.1 (hdisj A (mem_filter.1 hA).1 B (mem_filter.1 hB).1 hne)
          (mem_filter.1 hA).2 (mem_filter.1 hB).2
      have h : ((Ps.filter (fun T => w ∈ T)).card : ℝ) ≤ 1 := by exact_mod_cast this
      linarith)
  refine ⟨M, hME, hMdisj, ?_⟩
  have hsplit : V \ cov M = Ps.biUnion (fun P => P \ cov M) := by
    rw [← hcover]; ext x; simp only [Finset.mem_sdiff, mem_biUnion, id]
    constructor
    · rintro ⟨⟨P, hP, hx⟩, hxM⟩; exact ⟨P, hP, hx, hxM⟩
    · rintro ⟨P, hP, hx, hxM⟩; exact ⟨⟨P, hP, hx⟩, hxM⟩
  have hcardV : (V.card : ℝ) = ∑ P ∈ Ps, (P.card : ℝ) := by
    rw [← hcover, card_biUnion (t := id) (fun A hA B hB hne => hdisj A hA B hB hne)]
    push_cast; rfl
  rw [hsplit, card_biUnion (fun A hA B hB hne =>
    disjoint_of_subset_left sdiff_subset (disjoint_of_subset_right sdiff_subset
      (hdisj A hA B hB hne)))]
  push_cast
  rw [hcardV, mul_sum]
  refine sum_le_sum fun P hP => ?_
  have hPinter : P ∩ V = P := inter_eq_left.2 (hPV P hP)
  have h := hMT P hP (by rw [hPinter]; exact hmge.trans (by exact_mod_cast (hsize P hP).1))
  rwa [hPinter] at h

/-! ### Theorem 1.3 -/

theorem codeg_auxEdges_le {n q r : ℕ} {G H : Finset (Finset (Fin n))}
    (hH : H ⊆ cliquesOf q r G) (u v : Finset (Fin n)) :
    codeg (auxEdges r H) u v ≤ if u ∈ G ∧ v ∈ G then cliqueMult H (u ∪ v) else 0 := by
  unfold codeg auxEdges
  rw [filter_image]
  refine (card_image_le).trans ?_
  split_ifs with huv
  · unfold cliqueMult
    refine card_le_card fun Q hQ => ?_
    simp only [mem_filter, cliqueEdges, mem_powersetCard] at hQ ⊢
    exact ⟨hQ.1, union_subset hQ.2.1.1 hQ.2.2.1⟩
  · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
    intro Q hQ hcon
    refine huv ⟨cliqueEdges_subset_of_mem_cliquesOf (hH hQ) hcon.1,
      cliqueEdges_subset_of_mem_cliquesOf (hH hQ) hcon.2⟩

/-- **Theorem 1.3 (Nibble for designs)**, exactly as stated in `NibbleForDesigns`: no bound on
the number of vertices `n` in terms of `D` is assumed. -/
theorem nibbleForDesigns : NibbleForDesigns := by
  intro q r hr hrq β hβ hβ1
  set k : ℕ := q.choose r with hk
  have hk2 : 2 ≤ k := two_le_choose_of_lt hr hrq
  obtain ⟨c, hc0, Δ₀, hΔ₀⟩ := nibbleCover k hk2 (β / 2) (by positivity) (by linarith)
  refine ⟨min c (1 / 2), lt_min hc0 (by norm_num), (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  have ev : ∀ᶠ D : ℝ in atTop, max Δ₀ 1 ≤ D ∧ 2 ≤ D ^ (β / 2) := by
    filter_upwards [eventually_ge_atTop (max Δ₀ 1),
      (tendsto_rpow_atTop (show 0 < β / 2 by positivity)).eventually (eventually_ge_atTop 2)]
      with D h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.1 ev
  refine ⟨D₀, fun D hD n G H hG hH hdeg hcod => ?_⟩
  obtain ⟨hDmax, hD2⟩ := hD₀ D hD
  have hD1 : 1 ≤ D := (le_max_right _ _).trans hDmax
  have hDΔ₀ : Δ₀ ≤ D := (le_max_left _ _).trans hDmax
  have hD0 : 0 < D := by linarith
  set Δ := D + D ^ (1 - β) with hΔ
  have hDβ0 : 0 ≤ D ^ (1 - β) := Real.rpow_nonneg hD0.le _
  have hDΔ : D ≤ Δ := by linarith
  have hΔ1 : 1 ≤ Δ := by linarith
  have hΔ0 : 0 < Δ := by linarith
  -- comparison of the error terms
  have hcmp1 : D ^ (1 - β) ≤ D ^ (1 - β / 2) :=
    Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
  have hcmp2 : D ^ (1 - β / 2) ≤ Δ ^ (1 - β / 2) :=
    Real.rpow_le_rpow hD0.le hDΔ (by linarith)
  have hcmp3 : 2 * D ^ (1 - β) ≤ D ^ (1 - β / 2) := by
    have : D ^ (1 - β / 2) = D ^ (β / 2) * D ^ (1 - β) := by
      rw [← Real.rpow_add hD0]; congr 1; ring
    rw [this]; nlinarith
  have hΔexp : Δ * (1 - Δ ^ (-(β / 2))) = Δ - Δ ^ (1 - β / 2) := by
    have e2 : Δ ^ (-(β / 2)) * Δ = Δ ^ (1 - β / 2) := by
      rw [← Real.rpow_add_one hΔ0.ne']; congr 1; ring
    have : Δ * (1 - Δ ^ (-(β / 2))) = Δ - Δ ^ (-(β / 2)) * Δ := by ring
    rw [this, e2]
  -- the auxiliary hypergraph
  have hstar : ∀ e ∈ G, ((star (auxEdges r H) e).card : ℝ) = cliqueMult H e := fun e he => by
    rw [card_star_auxEdges hr hrq hH (hG e he)]
  obtain ⟨M, hME, hMdisj, hMcov⟩ := hΔ₀ Δ (hDΔ₀.trans hDΔ) (Finset (Fin n)) (auxEdges r H) G
    (auxEdges_card hH)
    (fun F hF => by
      obtain ⟨Q, hQ, rfl⟩ := mem_image.1 hF
      exact cliqueEdges_subset_of_mem_cliquesOf (hH hQ))
    (fun e he => by
      rw [hstar e he]
      have h := abs_le.1 (hdeg e he)
      constructor
      · rw [hΔexp]; linarith
      · linarith)
    (fun u v huv => by
      have h := codeg_auxEdges_le hH u v
      split_ifs at h with hG'
      · have h' : (codeg (auxEdges r H) u v : ℝ) ≤ cliqueMult H (u ∪ v) := by exact_mod_cast h
        exact h'.trans ((hcod u hG'.1 v hG'.2 huv).trans (hcmp1.trans hcmp2))
      · have : codeg (auxEdges r H) u v = 0 := Nat.le_zero.1 h
        rw [this, Nat.cast_zero]; positivity)
  obtain ⟨hpack, hcovEq⟩ := packing_of_auxMatching hr hrq hH hME hMdisj
  refine ⟨_, hpack, ?_⟩
  set P := H.filter (fun Q => cliqueEdges r Q ∈ M) with hP
  -- `|M| ≤ |P|`
  have hMP : M.card ≤ P.card := by
    have : M ⊆ P.image (cliqueEdges r) := by
      intro F hF
      obtain ⟨Q, hQ, rfl⟩ := mem_image.1 (hME hF)
      exact mem_image.2 ⟨Q, mem_filter.2 ⟨hQ, hF⟩, rfl⟩
    exact (card_le_card this).trans card_image_le
  -- `|cov M| ≤ k |M|`
  have hcovM : (cov M).card ≤ k * M.card := by
    unfold cov
    refine card_biUnion_le.trans (le_of_eq ?_)
    rw [sum_congr rfl fun F hF => by rw [id, auxEdges_card hH F (hME hF)], sum_const,
      smul_eq_mul, mul_comm]
  -- `|G| ≤ |G \ cov M| + |cov M|`
  have hGsplit : G.card ≤ (G \ cov M).card + (cov M).card := by
    have := card_sdiff_add_card_inter G (cov M)
    have h2 : (G ∩ cov M).card ≤ (cov M).card := card_le_card inter_subset_right
    omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hα : Δ ^ (-c) ≤ D ^ (-(min c (1 / 2))) := by
    calc Δ ^ (-c) ≤ D ^ (-c) := Real.rpow_le_rpow_of_nonpos hD0 hDΔ (by linarith)
      _ ≤ D ^ (-(min c (1 / 2))) :=
          Real.rpow_le_rpow_of_exponent_le hD1 (by have := min_le_left c (1 / 2); linarith)
  have hGc : (G.card : ℝ) ≤ ((G \ cov M).card : ℝ) + k * P.card := by
    have h1 : (G.card : ℝ) ≤ (G \ cov M).card + (cov M).card := by exact_mod_cast hGsplit
    have h2 : ((cov M).card : ℝ) ≤ k * M.card := by exact_mod_cast hcovM
    have h3 : (k : ℝ) * M.card ≤ k * P.card := by
      have : (M.card : ℝ) ≤ P.card := by exact_mod_cast hMP
      exact mul_le_mul_of_nonneg_left this hk0.le
    linarith
  have hG0 : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
  rw [div_mul_eq_mul_div, div_le_iff₀ hk0]
  have : (G.card : ℝ) * (1 - D ^ (-(min c (1 / 2)))) ≤ G.card - (G \ cov M).card := by
    have := mul_le_mul_of_nonneg_left hα hG0
    nlinarith [hMcov]
  linarith

end RefinedAbsorption
