module
public import RequestProject.Pending.Danger
public import RequestProject.Statements

/-!
# Theorem 6.3 of arXiv:2402.17855v1, uniformity `r = 1`

For `r = 1` an `r`-graph is a set of singletons, a `K_q^1`-decomposition is a partition of its
vertex set into `q`-sets, and a packing is a family of disjoint `q`-subsets.  The machinery for
`r ≥ 2` is not needed: arrange the vertices in `k ≥ q` rows of length `q` such that every block of
the given packing is a row (`exists_partition_card`), index them by `Fin k × Fin q`, and take the
groups `{(j, t) : j + t ≡ c (mod k)}` (`latin_groups`).  Every group has `q` elements and meets
every row, hence every block, in at most one vertex.
-/

@[expose] public section

namespace RefinedAbsorption.Pending

open Finset

/-- A set whose size is a multiple of `q ≥ 1` is partitioned by `q`-subsets. -/
theorem exists_partition_card {α : Type*} [DecidableEq α] {q : ℕ} (hq : 1 ≤ q) :
    ∀ R : Finset α, q ∣ R.card → ∃ Pt : Finset (Finset α), (∀ B ∈ Pt, B.card = q) ∧
      (∀ B ∈ Pt, ∀ B' ∈ Pt, B ≠ B' → Disjoint B B') ∧ Pt.biUnion id = R := by
  intro R
  induction R using Finset.strongInduction with
  | H R ih =>
    intro hdvd
    rcases Nat.eq_zero_or_pos R.card with h0 | hpos
    · exact ⟨∅, by simp, by simp, by simp [card_eq_zero.1 h0]⟩
    · have hqR : q ≤ R.card := Nat.le_of_dvd hpos hdvd
      obtain ⟨T, hTR, hTc⟩ := exists_subset_card_eq hqR
      have hlt : R \ T ⊂ R := by
        refine sdiff_ssubset hTR ?_
        rw [← card_pos, hTc]; omega
      have hdvd' : q ∣ (R \ T).card := by
        rw [card_sdiff_of_subset hTR, hTc]
        exact Nat.dvd_sub hdvd (dvd_refl q)
      obtain ⟨Pt, hP1, hP2, hP3⟩ := ih _ hlt hdvd'
      have hsub : ∀ B ∈ Pt, B ⊆ R \ T := fun B hB => by
        rw [← hP3]; exact subset_biUnion_of_mem id hB
      have hTne : T.Nonempty := by rw [← card_pos, hTc]; omega
      have hTdisj : ∀ B ∈ Pt, Disjoint T B := fun B hB => by
        rw [disjoint_left]
        intro x hxT hxB
        exact (mem_sdiff.1 (hsub B hB hxB)).2 hxT
      refine ⟨insert T Pt, ?_, ?_, ?_⟩
      · intro B hB
        rcases mem_insert.1 hB with h1 | h1
        · rw [h1]; exact hTc
        · exact hP1 B h1
      · intro B hB B' hB' hne
        rcases mem_insert.1 hB with h1 | h1 <;> rcases mem_insert.1 hB' with h2 | h2
        · exact absurd (h1.trans h2.symm) hne
        · rw [h1]; exact hTdisj B' h2
        · rw [h2]; exact (hTdisj B h1).symm
        · exact hP2 B h1 B' h2 hne
      · rw [biUnion_insert, hP3, id, union_sdiff_of_subset hTR]

/-- **Latin groups.**  Given `k ≥ q ≥ 1` pairwise disjoint rows of size `q`, their union is
partitioned into `q`-sets each meeting every row in at most one element. -/
theorem latin_groups {α : Type*} [DecidableEq α] {q : ℕ} (hq : 1 ≤ q) (Rw : Finset (Finset α))
    (hqk : q ≤ Rw.card) (hrow : ∀ R ∈ Rw, R.card = q)
    (hdisj : ∀ R ∈ Rw, ∀ R' ∈ Rw, R ≠ R' → Disjoint R R') :
    ∃ Gs : Finset (Finset α), (∀ B ∈ Gs, B.card = q) ∧ (∀ B ∈ Gs, B ⊆ Rw.biUnion id) ∧
      (∀ v ∈ Rw.biUnion id, (Gs.filter fun B => v ∈ B).card = 1) ∧
      ∀ B ∈ Gs, ∀ R ∈ Rw, (B ∩ R).card ≤ 1 := by
  set k := Rw.card with hk
  have hk0 : 0 < k := by omega
  let row : Fin k → Finset α := fun j => (Rw.equivFin.symm j).1
  have hrowmem : ∀ j, row j ∈ Rw := fun j => (Rw.equivFin.symm j).2
  have hrowinj : Function.Injective row := fun a b h =>
    Rw.equivFin.symm.injective (Subtype.ext h)
  have hrowsurj : ∀ R ∈ Rw, ∃ j, row j = R := fun R hR =>
    ⟨Rw.equivFin ⟨R, hR⟩, by simp [row]⟩
  have hrowc : ∀ j, (row j).card = q := fun j => hrow _ (hrowmem j)
  let f : Fin k × Fin q → α := fun p =>
    ((row p.1).equivFin.symm (Fin.cast (hrowc p.1).symm p.2)).1
  have hfrow : ∀ p, f p ∈ row p.1 := fun p => ((row p.1).equivFin.symm _).2
  have hfinj : Function.Injective f := by
    rintro ⟨j, t⟩ ⟨j', t'⟩ h
    have hj : j = j' := by
      by_contra hne
      have h1 := hfrow (j, t)
      have h2 := hfrow (j', t')
      have hd := hdisj _ (hrowmem j) _ (hrowmem j') (fun h => hne (hrowinj h))
      exact disjoint_left.1 hd h1 (by rw [show f (j, t) = f (j', t') from h]; exact h2)
    subst hj
    have h0 := (row j).equivFin.symm.injective (Subtype.ext h :
      (row j).equivFin.symm (Fin.cast (hrowc j).symm t) =
        (row j).equivFin.symm (Fin.cast (hrowc j).symm t'))
    have htt : t = t' := by simpa using h0
    rw [htt]
  have hfsurj : ∀ v ∈ Rw.biUnion id, ∃ p, f p = v := by
    intro v hv
    obtain ⟨R, hR, hvR⟩ := mem_biUnion.1 hv
    obtain ⟨j, rfl⟩ := hrowsurj R hR
    refine ⟨(j, Fin.cast (hrowc j) ((row j).equivFin ⟨v, hvR⟩)), ?_⟩
    simp [f]
  -- modular arithmetic
  have M1 : ∀ (j j' : Fin k) (t : ℕ), (j.val + t) % k = (j'.val + t) % k → j = j' := by
    intro j j' t h
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' t h) j.2 j'.2)
  have M2 : ∀ (j : ℕ) (t t' : Fin q), (j + t.val) % k = (j + t'.val) % k → t = t' := by
    intro j t t' h
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' j h) (by omega)
      (by omega))
  have M3 : ∀ (c : Fin k) (t : Fin q), ∃ j : Fin k, (j.val + t.val) % k = c.val := by
    intro c t
    refine ⟨⟨(c.val + k - t.val) % k, Nat.mod_lt _ hk0⟩, ?_⟩
    simp only
    rw [Nat.mod_add_mod, show c.val + k - t.val + t.val = c.val + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt c.2]
  let grp : Fin k → Finset α := fun c =>
    (univ.filter fun p : Fin k × Fin q => (p.1.val + p.2.val) % k = c.val).image f
  have hgrpc : ∀ c, (grp c).card = q := by
    intro c
    rw [card_image_of_injective _ hfinj]
    apply le_antisymm
    · have hinj : Set.InjOn (fun p : Fin k × Fin q => p.2)
          ↑(univ.filter fun p : Fin k × Fin q => (p.1.val + p.2.val) % k = c.val) := by
        rintro ⟨j, t⟩ hp ⟨j', t'⟩ hp' h
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp hp'
        simp only at h
        subst h
        rw [M1 j j' t.val (hp.trans hp'.symm)]
      have := card_le_card_of_injOn (t := (univ : Finset (Fin q))) _
        (fun p _ => mem_coe.2 (mem_univ _)) hinj
      simpa using this
    · choose g hg using M3 c
      have hinj : Set.InjOn (fun t : Fin q => (g t, t)) ↑(univ : Finset (Fin q)) := by
        intro t _ t' _ h
        simp only [Prod.mk.injEq] at h
        exact h.2
      have := card_le_card_of_injOn
        (t := univ.filter fun p : Fin k × Fin q => (p.1.val + p.2.val) % k = c.val) _
        (fun t _ => by simp [hg t]) hinj
      simpa using this
  refine ⟨univ.image grp, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨c, -, rfl⟩ := mem_image.1 hB
    exact hgrpc c
  · intro B hB
    obtain ⟨c, -, rfl⟩ := mem_image.1 hB
    intro x hx
    obtain ⟨p, -, rfl⟩ := mem_image.1 hx
    exact mem_biUnion.2 ⟨row p.1, hrowmem p.1, hfrow p⟩
  · intro v hv
    obtain ⟨p, rfl⟩ := hfsurj v hv
    set c₀ : Fin k := ⟨(p.1.val + p.2.val) % k, Nat.mod_lt _ hk0⟩
    rw [card_eq_one]
    refine ⟨grp c₀, ?_⟩
    ext B
    simp only [mem_filter, mem_image, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨⟨c, rfl⟩, hpB⟩
      obtain ⟨p', hp', hpp'⟩ := mem_image.1 hpB
      rw [hfinj hpp'] at hp'
      simp only [mem_filter, mem_univ, true_and] at hp'
      have : c = c₀ := Fin.ext (by simp [c₀, hp'])
      rw [this]
    · rintro rfl
      exact ⟨⟨c₀, rfl⟩, mem_image.2 ⟨p, by simp [c₀], rfl⟩⟩
  · intro B hB R hR
    obtain ⟨c, -, rfl⟩ := mem_image.1 hB
    rw [card_le_one]
    intro x hx y hy
    obtain ⟨hxg, hxR⟩ := mem_inter.1 hx
    obtain ⟨hyg, hyR⟩ := mem_inter.1 hy
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hxg
    obtain ⟨p', hp', rfl⟩ := mem_image.1 hyg
    simp only [mem_filter, mem_univ, true_and] at hp hp'
    have hrowR : ∀ p, f p ∈ R → row p.1 = R := by
      intro p hpR
      by_contra hne
      exact disjoint_left.1 (hdisj _ (hrowmem p.1) _ hR hne) (hfrow p) hpR
    have hj : p.1 = p'.1 := hrowinj ((hrowR p hxR).trans (hrowR p' hyR).symm)
    have ht : p.2 = p'.2 := by
      apply M2 p.1.val
      rw [hp]
      conv_rhs => rw [hj]
      exact hp'.symm
    rw [Prod.ext hj ht]

/-- **Theorem 6.3, `r = 1`.** -/
theorem theorem_6_3_one {q : ℕ} (hq : 2 ≤ q) :
    ∃ (n₀ : ℕ) (ε : ℝ), 0 < ε ∧ ∀ n ≥ n₀,
      ∀ G : Finset (Finset (Fin n)), IsRGraph 1 G → IsDivisible q 1 G →
        MinDegGE 1 G ((1 - ε) * n) → ∀ Q₁ : Finset (Finset (Fin n)), IsPacking q 1 G Q₁ →
          ∃ Q₂ : Finset (Finset (Fin n)), IsDecomposition q 1 G Q₂ ∧
            ∀ P₁ ∈ Q₁, ∀ P₂ ∈ Q₂, (P₁ ∩ P₂).card ≤ 1 := by
  refine ⟨2 * q * q, 1 / 2, by norm_num, fun n hn G hG hdiv hδ Q₁ hQ₁ => ?_⟩
  have hq1 : 1 ≤ q := by omega
  set U := G.biUnion id with hU
  have hsing : ∀ e ∈ G, ∃ v, e = {v} := fun e he => card_eq_one.1 (hG e he)
  have hmemU : ∀ v, v ∈ U ↔ {v} ∈ G := by
    intro v
    constructor
    · intro hv
      obtain ⟨e, he, hve⟩ := mem_biUnion.1 hv
      obtain ⟨w, rfl⟩ := hsing e he
      rw [mem_singleton.1 hve]; exact he
    · intro hv
      exact mem_biUnion.2 ⟨{v}, hv, mem_singleton_self v⟩
  have hGU : G = U.image fun v => {v} := by
    ext e
    simp only [mem_image]
    constructor
    · intro he
      obtain ⟨v, rfl⟩ := hsing e he
      exact ⟨v, (hmemU v).2 he, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hmemU v).1 hv
  have hcardU : G.card = U.card := by
    rw [hGU, card_image_of_injective _ singleton_injective]
  have hdeg0 : deg G ∅ = G.card := by
    unfold deg; rw [filter_true_of_mem (fun e _ => empty_subset e)]
  have hdvdU : q ∣ U.card := by
    have := hdiv ∅ (by simp)
    simp only [card_empty, Nat.sub_zero, Nat.choose_one_right] at this
    rwa [hdeg0, hcardU] at this
  have hbigU : q * q ≤ U.card := by
    have h1 := hδ ∅ (by simp)
    rw [hdeg0, hcardU] at h1
    have h2 : ((2 * q * q : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : ((q * q : ℕ) : ℝ) ≤ U.card := by push_cast at h2 ⊢; nlinarith
    exact_mod_cast h3
  -- the blocks of the packing
  have hQsub : ∀ P ∈ Q₁, P ⊆ U := by
    intro P hP v hv
    rw [hmemU]
    exact hQ₁.sub P hP (mem_powersetCard.2 ⟨singleton_subset_iff.2 hv, card_singleton v⟩)
  have hQdisj : ∀ P ∈ Q₁, ∀ P' ∈ Q₁, P ≠ P' → Disjoint P P' := by
    intro P hP P' hP' hne
    rw [disjoint_left]
    intro v hv hv'
    have h1 := hQ₁.mult_le {v} (card_singleton v)
    unfold cliqueMult at h1
    have := card_le_one.1 h1 P (mem_filter.2 ⟨hP, singleton_subset_iff.2 hv⟩) P'
      (mem_filter.2 ⟨hP', singleton_subset_iff.2 hv'⟩)
    exact hne this
  set Wq := Q₁.biUnion id with hWq
  have hWU : Wq ⊆ U := biUnion_subset.2 fun P hP => hQsub P hP
  have hWcard : Wq.card = Q₁.card * q := by
    rw [hWq, card_biUnion (t := id) (fun P hP P' hP' hne => hQdisj P hP P' hP' hne)]
    rw [sum_congr rfl (fun P hP => show (id P).card = q from hQ₁.card_eq P hP), sum_const,
      smul_eq_mul]
  set R := U \ Wq with hR
  have hRdvd : q ∣ R.card := by
    rw [hR, card_sdiff_of_subset hWU, hWcard]
    exact Nat.dvd_sub hdvdU (dvd_mul_left q _)
  obtain ⟨Pt, hPc, hPd, hPU⟩ := exists_partition_card hq1 R hRdvd
  have hPsub : ∀ B ∈ Pt, B ⊆ R := fun B hB => by
    rw [← hPU]; exact subset_biUnion_of_mem id hB
  have hne : ∀ B : Finset (Fin n), B.card = q → B.Nonempty := fun B hB => by
    rw [← card_pos, hB]; omega
  have hcross : ∀ P ∈ Q₁, ∀ B ∈ Pt, Disjoint P B := by
    intro P hP B hB
    rw [disjoint_left]
    intro v hvP hvB
    exact (mem_sdiff.1 (hPsub B hB hvB)).2 (mem_biUnion.2 ⟨P, hP, hvP⟩)
  set Rw := Q₁ ∪ Pt with hRw
  have hRwc : ∀ B ∈ Rw, B.card = q := by
    intro B hB
    rcases mem_union.1 hB with h | h
    · exact hQ₁.card_eq B h
    · exact hPc B h
  have hRwd : ∀ B ∈ Rw, ∀ B' ∈ Rw, B ≠ B' → Disjoint B B' := by
    intro B hB B' hB' hne'
    rcases mem_union.1 hB with h | h <;> rcases mem_union.1 hB' with h' | h'
    · exact hQdisj B h B' h' hne'
    · exact hcross B h B' h'
    · exact (hcross B' h' B h).symm
    · exact hPd B h B' h' hne'
  have hRwU : Rw.biUnion id = U := by
    rw [hRw, union_biUnion, ← hWq, hPU, hR, union_sdiff_of_subset hWU]
  have hRwcard : q ≤ Rw.card := by
    have h1 : U.card = Rw.card * q := by
      rw [← hRwU, card_biUnion (t := id) (fun B hB B' hB' hne' => hRwd B hB B' hB' hne'),
        sum_congr rfl (fun B hB => show (id B).card = q from hRwc B hB), sum_const, smul_eq_mul]
    rw [h1] at hbigU
    exact Nat.le_of_mul_le_mul_right hbigU (by omega)
  obtain ⟨Gs, hGc, hGsub, hGone, hGinter⟩ := latin_groups hq1 Rw hRwcard hRwc hRwd
  rw [hRwU] at hGsub hGone
  refine ⟨Gs, ⟨hG, hGc, fun e he => ?_⟩, fun P₁ hP₁ P₂ hP₂ => ?_⟩
  · obtain ⟨v, rfl⟩ := card_eq_one.1 he
    unfold cliqueMult
    simp only [singleton_subset_iff]
    split_ifs with hvG
    · exact hGone v ((hmemU v).2 hvG)
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro B hB hvB
      exact hvG ((hmemU v).1 (hGsub B hB hvB))
  · rw [inter_comm]
    exact hGinter P₂ hP₂ P₁ (mem_union_left _ hP₁)

end RefinedAbsorption.Pending
