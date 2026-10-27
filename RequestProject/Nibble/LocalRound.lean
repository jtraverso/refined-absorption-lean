module
public import RequestProject.Nibble.Round
public import RequestProject.Nibble.LLL

/-!
# One round of the nibble, via the Local Lemma

`nibble_round_lll` has the same conclusion as `nibble_round`, but the union bound over all
vertices and test sets is replaced by the Lovász Local Lemma (`lll_real`).  Hence there is no
bound on the number of vertices or of test sets: it suffices that every test set has at most
`M` elements and that every vertex lies in at most `M` test sets.

Every bad event is centred at a set `X` of vertices (`{v}` for a vertex, `T ∩ V` for a test
set) and only depends on the coins in `ballCoins E X`, the edges meeting an edge that meets
`X`.
-/

@[expose] public section

namespace RefinedAbsorption.Nibble

open Finset

variable {α : Type*} [DecidableEq α]

/-- The edges meeting an edge that meets `X`. -/
def ballCoins (E : Finset (Finset α)) (X : Finset α) : Finset (Finset α) :=
  nbhd E (cov (nbhd E X))

theorem mem_nbhd' {E : Finset (Finset α)} {X : Finset α} {g : Finset α} :
    g ∈ nbhd E X ↔ g ∈ E ∧ ¬ Disjoint g X := by
  unfold nbhd
  simp only [mem_biUnion, mem_star, not_disjoint_iff]
  constructor
  · rintro ⟨u, hu, hg, hug⟩; exact ⟨hg, u, hug, hu⟩
  · rintro ⟨hg, u, hug, hu⟩; exact ⟨u, hu, hg, hug⟩

theorem nbhd_singleton (E : Finset (Finset α)) (v : α) : nbhd E {v} = star E v := by
  unfold nbhd; rw [singleton_biUnion]

theorem nbhd_subset_ballCoins (E : Finset (Finset α)) (X : Finset α) :
    nbhd E X ⊆ ballCoins E X := by
  intro g hg
  obtain ⟨hgE, hgX⟩ := mem_nbhd'.1 hg
  obtain ⟨u, hug, _⟩ := not_disjoint_iff.1 hgX
  exact mem_nbhd'.2 ⟨hgE, not_disjoint_iff.2 ⟨u, hug, mem_cov.2 ⟨g, hg, hug⟩⟩⟩

/-- Coverage of `Y` only depends on the edges meeting `Y`. -/
theorem inter_cov_inter {E S C : Finset (Finset α)} {Y : Finset α} (hS : S ⊆ E)
    (hC : nbhd E Y ⊆ C) : Y ∩ cov (S ∩ C) = Y ∩ cov S := by
  ext u
  simp only [mem_inter, mem_cov]
  constructor
  · rintro ⟨hu, g, hg, hug⟩; exact ⟨hu, g, hg.1, hug⟩
  · rintro ⟨hu, g, hg, hug⟩
    exact ⟨hu, g, ⟨hg, hC (mem_nbhd'.2 ⟨hS hg, not_disjoint_iff.2 ⟨u, hug, hu⟩⟩)⟩,
      hug⟩

/-! ### The bad events -/

/-- Some vertex `w` lies in at least `L` chosen edges. -/
def badVertexEv (E : Finset (Finset α)) (L : ℕ) (w : α) (S : Finset (Finset α)) : Prop :=
  ∃ F ∈ (star E w).powersetCard L, F ⊆ S

/-- The degree of `v` deviates from its expectation. -/
def degDevEv (E : Finset (Finset α)) (p t : ℝ) (v : α) (S : Finset (Finset α)) : Prop :=
  fdeg E v S ≤ Ex p E (fdeg E v) - t ∨ Ex p E (fdeg E v) + t ≤ fdeg E v S

/-- Too many vertices of `X` stay uncovered. -/
def covDevEv (E : Finset (Finset α)) (p θ : ℝ) (X : Finset α) (S : Finset (Finset α)) : Prop :=
  Ex p E (fcov X) + θ * X.card / 8 ≤ fcov X S

/-- There are `s` disjoint witness pairs at `X`. -/
def witEv (E : Finset (Finset α)) (X : Finset α) (s : ℕ) (S : Finset (Finset α)) : Prop :=
  ∃ P ∈ witFam E X s, P.biUnion pairSet ⊆ S

theorem badVertexEv_local {E S : Finset (Finset α)} (L : ℕ) (w : α) :
    badVertexEv E L w S ↔ badVertexEv E L w (S ∩ ballCoins E {w}) := by
  unfold badVertexEv
  have hsub : star E w ⊆ ballCoins E {w} := by
    rw [← nbhd_singleton]; exact nbhd_subset_ballCoins E {w}
  constructor
  · rintro ⟨F, hF, hFS⟩
    exact ⟨F, hF, subset_inter hFS ((mem_powersetCard.1 hF).1.trans hsub)⟩
  · rintro ⟨F, hF, hFS⟩
    exact ⟨F, hF, hFS.trans inter_subset_left⟩

theorem fdeg_local {E S : Finset (Finset α)} (hS : S ⊆ E) (v : α) :
    fdeg E v (S ∩ ballCoins E {v}) = fdeg E v S := by
  unfold fdeg
  congr 2
  refine filter_congr fun e he => ?_
  set Y := cov (nbhd E {v}) with hY
  have heY : e.erase v ⊆ Y := by
    intro u hu
    refine mem_cov.2 ⟨e, ?_, mem_of_mem_erase hu⟩
    rw [nbhd_singleton]; exact he
  have key := inter_cov_inter (C := ballCoins E {v}) hS (Subset.refl _)
  rw [← hY] at key
  rw [disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty]
  have h1 : e.erase v ∩ cov (S ∩ ballCoins E {v}) = e.erase v ∩ (Y ∩ cov (S ∩ ballCoins E {v})) := by
    rw [← inter_assoc, inter_eq_left.2 heY]
  have h2 : e.erase v ∩ cov S = e.erase v ∩ (Y ∩ cov S) := by
    rw [← inter_assoc, inter_eq_left.2 heY]
  rw [h1, h2, key]

theorem degDevEv_local {E S : Finset (Finset α)} (hS : S ⊆ E) (p t : ℝ) (v : α) :
    degDevEv E p t v S ↔ degDevEv E p t v (S ∩ ballCoins E {v}) := by
  unfold degDevEv; rw [fdeg_local hS]

theorem fcov_local {E S : Finset (Finset α)} (hS : S ⊆ E) (X : Finset α) :
    fcov X (S ∩ ballCoins E X) = fcov X S := by
  unfold fcov
  congr 2
  refine filter_congr fun u hu => ?_
  have key := inter_cov_inter (Y := X) (C := ballCoins E X) hS (nbhd_subset_ballCoins E X)
  constructor
  · intro h h'
    exact h (mem_inter.1 (key ▸ mem_inter.2 ⟨hu, h'⟩ : u ∈ X ∩ cov (S ∩ ballCoins E X))).2
  · intro h h'
    exact h (mem_inter.1 (key.symm ▸ mem_inter.2 ⟨hu, h'⟩ : u ∈ X ∩ cov S)).2

theorem covDevEv_local {E S : Finset (Finset α)} (hS : S ⊆ E) (p θ : ℝ) (X : Finset α) :
    covDevEv E p θ X S ↔ covDevEv E p θ X (S ∩ ballCoins E X) := by
  unfold covDevEv; rw [fcov_local hS]

theorem pairSet_subset_ballCoins {E : Finset (Finset α)} {X : Finset α}
    {gh : Finset α × Finset α} (h : gh ∈ witPairs E X) : pairSet gh ⊆ ballCoins E X := by
  unfold witPairs at h
  obtain ⟨hmem, -, h1X, h12⟩ := mem_filter.1 h
  obtain ⟨hg, hh⟩ := mem_product.1 hmem
  have hg' : gh.1 ∈ nbhd E X := mem_nbhd'.2 ⟨hg, h1X⟩
  intro f hf
  unfold pairSet at hf
  rcases mem_insert.1 hf with rfl | hf
  · exact nbhd_subset_ballCoins E X hg'
  · rw [mem_singleton] at hf
    subst hf
    obtain ⟨u, hu1, hu2⟩ := not_disjoint_iff.1 h12
    exact mem_nbhd'.2 ⟨hh, not_disjoint_iff.2 ⟨u, hu2, mem_cov.2 ⟨gh.1, hg', hu1⟩⟩⟩

theorem witEv_local {E S : Finset (Finset α)} (X : Finset α) (s : ℕ) :
    witEv E X s S ↔ witEv E X s (S ∩ ballCoins E X) := by
  classical
  unfold witEv
  constructor
  · rintro ⟨P, hP, hPS⟩
    refine ⟨P, hP, subset_inter hPS ?_⟩
    intro f hf
    obtain ⟨gh, hgh, hf⟩ := mem_biUnion.1 hf
    have hP' := (mem_powersetCard.1 (mem_filter.1 hP).1).1
    exact pairSet_subset_ballCoins (hP' hgh) hf
  · rintro ⟨P, hP, hPS⟩
    exact ⟨P, hP, hPS.trans inter_subset_left⟩

/-! ### Counting dependencies -/

theorem card_cov_le {E F : Finset (Finset α)} {k : ℕ} (hk : ∀ g ∈ E, g.card = k) (hF : F ⊆ E) :
    ((cov F).card : ℝ) ≤ k * F.card := by
  unfold cov
  refine (Nat.cast_le.2 card_biUnion_le).trans ?_
  push_cast
  rw [sum_congr rfl fun g hg => by rw [id, hk g (hF hg)], sum_const, nsmul_eq_mul, mul_comm]

theorem nbhd_subset' (E : Finset (Finset α)) (X : Finset α) : nbhd E X ⊆ E := fun _ hg =>
  (mem_nbhd'.1 hg).1

theorem card_ballCoins_le {E : Finset (Finset α)} {V X : Finset α} {k : ℕ} {Dmax : ℝ}
    (hD : 0 ≤ Dmax) (hk : ∀ g ∈ E, g.card = k) (hEV : ∀ F ∈ E, F ⊆ V) (hXV : X ⊆ V)
    (hdeg : ∀ u ∈ V, ((star E u).card : ℝ) ≤ Dmax) :
    ((ballCoins E X).card : ℝ) ≤ k * X.card * Dmax ^ 2 := by
  have h1 := card_nbhd_le (E := E) hXV hdeg
  have h2 := card_cov_le hk (nbhd_subset' E X)
  have h3 := card_nbhd_le (E := E) (X := cov (nbhd E X))
    (cov_subset_of_subset (nbhd_subset' E X) hEV) hdeg
  unfold ballCoins
  calc ((nbhd E (cov (nbhd E X))).card : ℝ) ≤ (cov (nbhd E X)).card * Dmax := h3
    _ ≤ (k * (nbhd E X).card) * Dmax := by gcongr
    _ ≤ (k * (X.card * Dmax)) * Dmax := by gcongr
    _ = k * X.card * Dmax ^ 2 := by ring

theorem mem_ballCoins_imp {E : Finset (Finset α)} {X g : Finset α} (h : g ∈ ballCoins E X) :
    ¬ Disjoint X (cov (nbhd E g)) := by
  obtain ⟨_, hgY⟩ := mem_nbhd'.1 h
  obtain ⟨u, hug, huY⟩ := not_disjoint_iff.1 hgY
  obtain ⟨f, hf, huf⟩ := mem_cov.1 huY
  obtain ⟨hfE, hfX⟩ := mem_nbhd'.1 hf
  obtain ⟨w, hwf, hwX⟩ := not_disjoint_iff.1 hfX
  refine not_disjoint_iff.2 ⟨w, hwX, mem_cov.2 ⟨f, ?_, hwf⟩⟩
  exact mem_nbhd'.2 ⟨hfE, not_disjoint_iff.2 ⟨u, huf, hug⟩⟩

/-- Bounding the dependency degree of events with local coin sets. -/
theorem card_dep_le {ι : Type*} [DecidableEq ι] {E : Finset (Finset α)} {V : Finset α} {k : ℕ}
    {Dmax M : ℝ} (hD : 0 ≤ Dmax) (hk : ∀ g ∈ E, g.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ u ∈ V, ((star E u).card : ℝ) ≤ Dmax)
    (I : Finset ι) (X : ι → Finset α) (hXV : ∀ i ∈ I, X i ⊆ V) (hXM : ∀ i ∈ I, ((X i).card : ℝ) ≤ M)
    (hmult : ∀ w : α, ((I.filter (fun j => w ∈ X j)).card : ℝ) ≤ M)
    (i : ι) (hi : i ∈ I) :
    ((I.filter (fun j => ¬ Disjoint (ballCoins E (X i)) (ballCoins E (X j)))).card : ℝ) ≤
      (k * M * Dmax ^ 2) * ((k * k * Dmax) * M) := by
  have hsub1 : I.filter (fun j => ¬ Disjoint (ballCoins E (X i)) (ballCoins E (X j))) ⊆
      (ballCoins E (X i)).biUnion (fun g => I.filter (fun j => g ∈ ballCoins E (X j))) := by
    intro j hj
    obtain ⟨hjI, hdis⟩ := mem_filter.1 hj
    obtain ⟨g, hg1, hg2⟩ := not_disjoint_iff.1 hdis
    exact mem_biUnion.2 ⟨g, hg1, mem_filter.2 ⟨hjI, hg2⟩⟩
  have hM0 : 0 ≤ M := le_trans (Nat.cast_nonneg _) (hXM i hi)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hg : ∀ g ∈ ballCoins E (X i),
      ((I.filter (fun j => g ∈ ballCoins E (X j))).card : ℝ) ≤ (k * k * Dmax) * M := by
    intro g hgC
    have hgE : g ∈ E := (mem_nbhd'.1 hgC).1
    have hsub2 : I.filter (fun j => g ∈ ballCoins E (X j)) ⊆
        (cov (nbhd E g)).biUnion (fun w => I.filter (fun j => w ∈ X j)) := by
      intro j hj
      obtain ⟨hjI, hgj⟩ := mem_filter.1 hj
      obtain ⟨w, hw1, hw2⟩ := not_disjoint_iff.1 (mem_ballCoins_imp hgj)
      exact mem_biUnion.2 ⟨w, hw2, mem_filter.2 ⟨hjI, hw1⟩⟩
    have hc1 := card_cov_le hk (nbhd_subset' E g)
    have hc2 := card_nbhd_le (E := E) (hEV g hgE) hdeg
    rw [hk g hgE] at hc2
    calc ((I.filter (fun j => g ∈ ballCoins E (X j))).card : ℝ)
        ≤ (((cov (nbhd E g)).biUnion (fun w => I.filter (fun j => w ∈ X j))).card : ℝ) := by
          exact_mod_cast card_le_card hsub2
      _ ≤ ∑ w ∈ cov (nbhd E g), ((I.filter (fun j => w ∈ X j)).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ w ∈ cov (nbhd E g), M := sum_le_sum fun w _ => hmult w
      _ = (cov (nbhd E g)).card * M := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (k * (nbhd E g).card) * M := by gcongr
      _ ≤ (k * (k * Dmax)) * M := by gcongr
      _ = (k * k * Dmax) * M := by ring
  have hC := card_ballCoins_le hD hk hEV (hXV i hi) hdeg
  calc ((I.filter (fun j => ¬ Disjoint (ballCoins E (X i)) (ballCoins E (X j)))).card : ℝ)
      ≤ (((ballCoins E (X i)).biUnion
          (fun g => I.filter (fun j => g ∈ ballCoins E (X j)))).card : ℝ) := by
        exact_mod_cast card_le_card hsub1
    _ ≤ ∑ g ∈ ballCoins E (X i), ((I.filter (fun j => g ∈ ballCoins E (X j))).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ g ∈ ballCoins E (X i), (k * k * Dmax) * M := sum_le_sum hg
    _ = (ballCoins E (X i)).card * ((k * k * Dmax) * M) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (k * (X i).card * Dmax ^ 2) * ((k * k * Dmax) * M) := by gcongr
    _ ≤ (k * M * Dmax ^ 2) * ((k * k * Dmax) * M) := by
        gcongr
        exact hXM i hi

/-! ### The round -/

/-- **One round of the nibble, via the Local Lemma.**  The same conclusion as `nibble_round`,
without any bound on `|V|` or `|𝒯|`. -/
theorem nibble_round_lll {E : Finset (Finset α)} {V : Finset α} {k L : ℕ}
    {D e C θ η τ ζ M : ℝ} (𝒯 : Finset (Finset α))
    (hk2 : 2 ≤ k) (hk : ∀ F ∈ E, F.card = k) (hEV : ∀ F ∈ E, F ⊆ V)
    (hdeg : ∀ v ∈ V, D * (1 - e) ≤ (star E v).card ∧ ((star E v).card : ℝ) ≤ D * (1 + e))
    (hcod : ∀ u v : α, u ≠ v → (codeg E u v : ℝ) ≤ C)
    (hD1 : 1 ≤ D) (hC : 0 < C) (hCD : k * C ≤ D / 2) (he0 : 0 ≤ e) (he : e ≤ 1 / 4)
    (hθ0 : 0 < θ) (hθ : k * θ ≤ 1 / 4) (hη0 : 0 < η) (hη : η ≤ 1)
    (hζ : 160 * k * θ ^ 2 ≤ ζ)
    (hM : 1 ≤ M) (h𝒯size : ∀ T ∈ 𝒯, (T.card : ℝ) ≤ M)
    (h𝒯mult : ∀ w : α, ((𝒯.filter (fun T => w ∈ T)).card : ℝ) ≤ M)
    (hprob : 4 * ((2 * θ) ^ L + 2 * Real.exp (-(θ * η ^ 2 * D / (16 * k ^ 2 * C)))
      + (Real.exp (-(θ * τ / (512 * k))) + Real.exp (-(ζ * τ)))) *
      ((k * (M + 1) * (2 * D) ^ 2) * ((k * k * (2 * D)) * (M + 1)) + 1) ≤ 1) :
    ∃ S ⊆ E,
      (∀ v ∈ V \ cov S,
        D * (1 - (k - 1) * θ) *
            (1 - (e + 4 * k * θ * e + 4 * k ^ 2 * θ * (C / D + θ) + 2 * θ * η))
          ≤ (star (nextE E S) v).card ∧
        ((star (nextE E S) v).card : ℝ) ≤
          D * (1 - (k - 1) * θ) *
            (1 + (e + 4 * k * θ * e + 4 * k ^ 2 * θ * (C / D + θ) + 2 * θ * η))) ∧
      (∀ T ∈ 𝒯, τ ≤ (T ∩ V).card →
        (((T ∩ V) \ cov S).card : ℝ) ≤ (1 - θ / 2) * (T ∩ V).card) ∧
      (∀ T ∈ 𝒯, τ ≤ (T ∩ V).card →
        ((waste S ∩ (T ∩ V)).card : ℝ) ≤ 2 * k * (1 + k * L) * ζ * (T ∩ V).card) := by
  classical
  have hD : 0 < D := by linarith
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hθ8 : θ ≤ 1 / 8 := by nlinarith
  have hθD : θ ≤ D := by linarith
  have hp0 : 0 ≤ θ / D := div_nonneg hθ0.le hD.le
  have hp1 : θ / D ≤ 1 := (div_le_one hD).2 hθD
  have he1 : e ≤ 1 := by linarith
  set p := θ / D with hp
  set 𝒯L := 𝒯.filter (fun T => τ ≤ ((T ∩ V).card : ℝ)) with h𝒯L
  set I : Finset (α ⊕ Finset α) := V.disjSum 𝒯L with hI
  set X : α ⊕ Finset α → Finset α := Sum.elim (fun v => {v}) (fun T => T ∩ V) with hX
  set A : α ⊕ Finset α → Finset (Finset α) → Prop := Sum.elim
    (fun v S => badVertexEv E L v S ∨ degDevEv E p (θ * η * D) v S)
    (fun T S => covDevEv E p θ (T ∩ V) S ∨ witEv E (T ∩ V) ⌈ζ * (T ∩ V).card⌉₊ S) with hA
  set q := (2 * θ) ^ L + 2 * Real.exp (-(θ * η ^ 2 * D / (16 * k ^ 2 * C)))
      + (Real.exp (-(θ * τ / (512 * k))) + Real.exp (-(ζ * τ))) with hq
  have hdegmax : ∀ u ∈ V, ((star E u).card : ℝ) ≤ 2 * D := fun u hu =>
    (hdeg u hu).2.trans (by nlinarith)
  have hloc : ∀ i ∈ I, ∀ S ⊆ E, A i S ↔ A i (S ∩ ballCoins E (X i)) := by
    intro i _ S hS
    rcases i with v | T
    · simp only [hA, hX, Sum.elim_inl]
      rw [← badVertexEv_local, ← degDevEv_local hS]
    · simp only [hA, hX, Sum.elim_inr]
      rw [← covDevEv_local hS, ← witEv_local]
  have hpr : ∀ i ∈ I, Pr p E (A i) ≤ q := by
    intro i hi
    have h1 := Real.exp_pos (-(θ * τ / (512 * k)))
    have h2 := Real.exp_pos (-(ζ * τ))
    have h3 := Real.exp_pos (-(θ * η ^ 2 * D / (16 * k ^ 2 * C)))
    have h4 : 0 ≤ (2 * θ) ^ L := by positivity
    rcases i with v | T
    · have hv : v ∈ V := by simpa [hI] using hi
      simp only [hA, Sum.elim_inl]
      refine (Pr_or_le hp0 hp1 E _ _).trans ?_
      have hb1 : Pr p E (badVertexEv E L v) ≤ (2 * θ) ^ L := by
        have := Pr_bad_vertex_le' (E := E) (V := {v}) (L := L)
          (fun w hw => by rw [mem_singleton] at hw; subst hw; exact hdeg w hv) hD hθ0.le hθD he1
        rw [card_singleton, Nat.cast_one, one_mul] at this
        refine le_trans (le_of_eq (Pr_congr p E fun S _ => ?_)) this
        unfold badVertexEv; simp
      have hb2 : Pr p E (degDevEv E p (θ * η * D) v) ≤
          2 * Real.exp (-(θ * η ^ 2 * D / (16 * k ^ 2 * C))) :=
        Pr_fdeg_dev_le hk hEV hdeg hcod hk2 hD hC hθ0.le hθD he1 hη0.le hη hv
      linarith
    · have hT : T ∈ 𝒯L := by simpa [hI] using hi
      have hτT := (mem_filter.1 hT).2
      simp only [hA, Sum.elim_inr]
      refine (Pr_or_le hp0 hp1 E _ _).trans ?_
      have hb3 : Pr p E (covDevEv E p θ (T ∩ V)) ≤ Real.exp (-(θ * τ / (512 * k))) := by
        refine (Pr_fcov_dev_le hk inter_subset_right hdeg hk2 hD hθ0.le hθD he1).trans ?_
        refine Real.exp_le_exp.2 (neg_le_neg ?_)
        gcongr
      have hb4 : Pr p E (witEv E (T ∩ V) ⌈ζ * (T ∩ V).card⌉₊) ≤ Real.exp (-(ζ * τ)) := by
        have hζ0 : 0 ≤ ζ := le_trans (by positivity) hζ
        refine (Pr_wit_T_le hk hEV inter_subset_right hdeg hD hθ0.le hθD he1 hζ).trans ?_
        refine Real.exp_le_exp.2 (neg_le_neg ?_)
        gcongr
      linarith
  have hXV : ∀ i ∈ I, X i ⊆ V := by
    intro i hi
    rcases i with v | T
    · have hv : v ∈ V := by simpa [hI] using hi
      simpa [hX] using hv
    · simp [hX]
  have hXM : ∀ i ∈ I, ((X i).card : ℝ) ≤ M + 1 := by
    intro i hi
    rcases i with v | T
    · simp [hX]; linarith
    · have hT : T ∈ 𝒯L := by simpa [hI] using hi
      simp only [hX, Sum.elim_inr]
      have := h𝒯size T (mem_filter.1 hT).1
      have h' : ((T ∩ V).card : ℝ) ≤ T.card := by exact_mod_cast card_le_card inter_subset_left
      linarith
  have hmult : ∀ w : α, ((I.filter (fun j => w ∈ X j)).card : ℝ) ≤ M + 1 := by
    intro w
    have hsub : I.filter (fun j => w ∈ X j) ⊆
        ({Sum.inl w} : Finset (α ⊕ Finset α)) ∪ (𝒯.filter (fun T => w ∈ T)).map Function.Embedding.inr := by
      intro j hj
      obtain ⟨_, hwj⟩ := mem_filter.1 hj
      rcases j with v | T
      · simp only [hX, Sum.elim_inl, mem_singleton] at hwj
        subst hwj; simp
      · have hT : T ∈ 𝒯L := by simpa [hI] using (mem_filter.1 hj).1
        simp only [hX, Sum.elim_inr, mem_inter] at hwj
        simp only [mem_union, mem_singleton, mem_map, mem_filter, Function.Embedding.inr_apply]
        right
        exact ⟨T, ⟨(mem_filter.1 hT).1, hwj.1⟩, rfl⟩
    have := card_le_card hsub
    have h2 := card_union_le ({Sum.inl w} : Finset (α ⊕ Finset α))
      ((𝒯.filter (fun T => w ∈ T)).map Function.Embedding.inr)
    rw [card_singleton, card_map] at h2
    have h3 : ((I.filter (fun j => w ∈ X j)).card : ℝ) ≤ 1 + (𝒯.filter (fun T => w ∈ T)).card := by
      exact_mod_cast this.trans h2
    linarith [h𝒯mult w]
  have hdep := card_dep_le (by linarith : (0 : ℝ) ≤ 2 * D) hk hEV hdegmax I X hXV hXM hmult
  have hq0 : 0 ≤ q := by
    have := Real.exp_pos (-(θ * τ / (512 * k)))
    have := Real.exp_pos (-(ζ * τ))
    have := Real.exp_pos (-(θ * η ^ 2 * D / (16 * k ^ 2 * C)))
    have : 0 ≤ (2 * θ) ^ L := by positivity
    positivity
  obtain ⟨S, hSE, hS⟩ := lll_real hp0 hp1 E I A (fun i => ballCoins E (X i)) _ hloc hpr hdep hq0
    (by positivity) (by rw [hq]; linarith)
  have hn1 : ∀ w ∈ V, ¬ badVertexEv E L w S := fun w hw h =>
    hS (Sum.inl w) (by simp [hI, hw]) (Or.inl h)
  have hn2 : ∀ v ∈ V, ¬ degDevEv E p (θ * η * D) v S := fun v hv h =>
    hS (Sum.inl v) (by simp [hI, hv]) (Or.inr h)
  have hn3 : ∀ T ∈ 𝒯L, ¬ covDevEv E p θ (T ∩ V) S := fun T hT h =>
    hS (Sum.inr T) (by simp [hI, hT]) (Or.inl h)
  have hn4 : ∀ T ∈ 𝒯L, ¬ witEv E (T ∩ V) ⌈ζ * (T ∩ V).card⌉₊ S := fun T hT h =>
    hS (Sum.inr T) (by simp [hI, hT]) (Or.inr h)
  refine ⟨S, hSE, fun v hv => ?_, fun T hT hτT => ?_, fun T hT hτT => ?_⟩
  · rw [mem_sdiff] at hv
    rw [card_star_nextE hv.2]
    have hdev : Ex (θ / D) E (fdeg E v) - θ * η * D < fdeg E v S ∧
        fdeg E v S < Ex (θ / D) E (fdeg E v) + θ * η * D := by
      by_contra h
      rw [not_and_or, not_lt, not_lt] at h
      exact hn2 v hv.1 h
    exact round_deg_of_dev hk2 hk hEV hdeg hcod hD1 hC hCD he0 he hθ0 hθ hη0 hv.1 hdev
  · have hTL : T ∈ 𝒯L := mem_filter.2 ⟨hT, hτT⟩
    have hlt : fcov (T ∩ V) S < Ex (θ / D) E (fcov (T ∩ V)) + θ * (T ∩ V).card / 8 := by
      by_contra h
      exact hn3 T hTL (not_lt.1 h)
    exact round_cov_of_dev hdeg hD1 he0 he hθ0 hθ8 hlt
  · have hTL : T ∈ 𝒯L := mem_filter.2 ⟨hT, hτT⟩
    have hgood : ∀ w ∈ V, (S.filter (fun g => w ∈ g)).card ≤ L := by
      intro w hw
      by_contra hcon
      push_neg at hcon
      obtain ⟨F, hF, hFc⟩ := exists_subset_card_eq hcon.le
      refine hn1 w hw ⟨F, mem_powersetCard.2 ⟨?_, hFc⟩, hF.trans (filter_subset _ _)⟩
      intro g hg
      have := mem_filter.1 (hF hg)
      exact mem_star.2 ⟨hSE this.1, this.2⟩
    have hno : ¬ ∃ P ∈ witFam E (T ∩ V) ⌈ζ * (T ∩ V).card⌉₊, P.biUnion pairSet ⊆ S :=
      fun h => hn4 T hTL h
    exact round_waste_of_good hSE hk hEV hgood hno (le_trans (by positivity) hζ)

end RefinedAbsorption.Nibble
