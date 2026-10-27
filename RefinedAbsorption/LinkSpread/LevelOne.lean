module
public import RefinedAbsorption.LinkSpread.TRefOut

/-!
# Tagged link refiners at level `1`

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down).  Lean formalization:
Juan Pablo Traverso Gianini, Apache-2.0.

At level `i = 1` the tags are single vertices outside the reserve.  The obstruction to iterating
stages for all fibres in one common chain of reserves is the codegree across tags: an
`(r-1)`-set inside the reserve can be a body of many fibres.  It is removed by splitting the tags
into four classes of (almost) equal size and giving every class its own quarter of the current
reserve (`classStep`).  The number of tags of a class shrinks at the same rate as its reserve, so
after multiplicity reduction the residue of a class has lifted degree `≤ M (|Z₁| + #tags)`
(`residue_deg_one`), which is linear in the size `|Z₁|` of its reserve, and the budgets form a
geometric series.  Different classes load disjoint reserves, so at every `(r-1)`-set only one
class pays for its deeper stages.

* `taggedBase`: small reserves (multiplicity reduction and the finite step in every fibre).
* `taggedDense`: complete tagged refiners with budget `A · D + A' · |Z|`.
* `taggedStaged`: budget `2^t · Bd ≤ 2^t · C_t · D + B' · |Z|`, refinedness uniform in `t`.
* **`taggedLinkRefinersE_one`**: `TaggedLinkRefinersE q r 1` from the link levels `2, …, r-1`.
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown

/-- **Lifted degrees of a residue with bounded multiplicity, tags of size one.** -/
theorem residue_deg_one {r M : ℕ} {n : ℕ} {E : Type} [DecidableEq E] {tg bd : E → Finset (Fin n)}
    {Z : Finset (Fin n)} {X : Finset E} (htg : ∀ x, Disjoint (tg x) Z)
    (hbd : ∀ x, bd x ⊆ Z) (htgc : ∀ x ∈ X, (tg x).card = 1)
    (hbdc : ∀ x ∈ X, (bd x).card = r - 1) (hmult : ∀ T e, mult bd (fibre tg X T) e ≤ M)
    (S : Finset (Fin n)) (hS : S.card = r - 1) (hr : 2 < r) :
    mdeg (liftEnds tg bd) X S ≤ M * (Z.card + (X.image tg).card) := by
  rw [mdeg_liftEnds_eq_sum]
  simp_rw [mdeg_lift]
  have hfr : ∀ T, MIsRGraph (r - 1) bd (fibre tg X T) :=
    fun T x hx => hbdc x (fibre_subset _ _ _ hx)
  have hTs1 : ∀ T ∈ X.image tg, T.card = 1 := by
    intro T hT; obtain ⟨x, hx, rfl⟩ := mem_image.1 hT; exact htgc x hx
  have hTsZ : ∀ T ∈ X.image tg, Disjoint T Z := by
    intro T hT; obtain ⟨x, -, rfl⟩ := mem_image.1 hT; exact htg x
  by_cases hSZ : S ⊆ Z
  · have hle : ∀ T ∈ X.image tg, mdeg bd (fibre tg X T) (S \ T) ≤ M := by
      intro T hT
      rw [sdiff_eq_self_of_disjoint (disjoint_of_subset_left hSZ (hTsZ T hT).symm)]
      refine le_trans (card_le_card fun x hx => ?_) (hmult T S)
      obtain ⟨hx, hSx⟩ := mem_filter.1 hx
      refine mem_filter.2 ⟨hx, (eq_of_subset_of_card_le hSx ?_).symm⟩
      rw [hfr T x hx, hS]
    calc ∑ T ∈ X.image tg, mdeg bd (fibre tg X T) (S \ T) ≤ ∑ _T ∈ X.image tg, M :=
          sum_le_sum hle
      _ = M * (X.image tg).card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ M * (Z.card + (X.image tg).card) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  · obtain ⟨v, hvS, hvZ⟩ := not_subset.1 hSZ
    have hzero : ∀ T ∈ X.image tg, mdeg bd (fibre tg X T) (S \ T) ≠ 0 → T ∈ ({{v}} : Finset _) := by
      intro T hT hne
      obtain ⟨x, hx⟩ := card_pos.1 (Nat.pos_of_ne_zero hne)
      obtain ⟨-, hSx⟩ := mem_filter.1 hx
      have hvT : v ∈ T := by
        by_contra hvT
        exact hvZ (hbd x (hSx (mem_sdiff.2 ⟨hvS, hvT⟩)))
      obtain ⟨w, hw⟩ := card_eq_one.1 (hTs1 T hT)
      rw [hw] at hvT ⊢
      rw [mem_singleton.1 hvT]
      exact mem_singleton_self _
    refine (sum_le_sum_of_ne_zero hzero).trans ?_
    rw [sum_singleton]
    have hcard : (S \ {v}).card + 1 = r - 1 := by
      rw [card_sdiff, singleton_inter_of_mem hvS, card_singleton, hS]; omega
    refine (RefinedAbsorption.Dense.mdeg_le_of_mult (hfr {v}) (fun x _ => hbd x) (hmult {v}) _ hcard).trans ?_
    exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

set_option maxHeartbeats 2000000 in
open Classical in
/-- **Small reserves**: multiplicity reduction followed by the finite step, in every fibre. -/
theorem taggedBase (q r i : ℕ) (hir : i + 1 < r) (hrq : r < q) (m₀ : ℕ) :
    ∃ Cb Ab : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (tg bd : E → Finset (Fin n))
      (Zc : Finset (Fin n)) (X : Finset E) (D : ℕ),
      (∀ x, bd x ⊆ Zc) → (∀ x ∈ X, (tg x).card = i) → (∀ x ∈ X, (bd x).card = r - i) →
      Zc.card ≤ m₀ →
      (∀ S : Finset (Fin n), S.card = r - 1 → mdeg (liftEnds tg bd) X S ≤ D) →
      TRefOut q r i Cb tg bd Zc X (fun _ => Ab * D + Ab * (X.image tg).card) := by
  obtain ⟨M, Cm, hM, hmr⟩ := multRed_explicit (q - i) (r - i) (by omega)
  set Kf := M * 2 ^ m₀ with hKf
  set Ab := (M + 2) ^ 2 + Cm * (1 + (M + 2) ^ 2) + 2 ^ Kf with hAb
  refine ⟨Cm + (Kf + 2 ^ Kf), Ab, ?_⟩
  intro n E _ tg bd Zc X D hbd htgc hbdc hZm hdeg
  set Ts := X.image tg with hTs
  have hfr : ∀ T, MIsRGraph (r - i) bd (fibre tg X T) :=
    fun T x hx => hbdc x (fibre_subset _ _ _ hx)
  have hTsc : ∀ T ∈ Ts, T.card = i := by
    intro T hT; obtain ⟨x, hx, rfl⟩ := mem_image.1 hT; exact htgc x hx
  set ends' : Finset (Fin n) → E ⊕ MLab (Fin n) → Finset (Fin n) :=
    fun _ => Sum.elim bd Prod.fst with hends'
  refine ⟨E ⊕ MLab (Fin n), inferInstance, Sum.inl, ends',
    fun T => (mR bd (fibre tg X T) M).image Sum.inr,
    fun T => mW bd (fibre tg X T) M ∪ ((mY bd (fibre tg X T) M).powerset.filter
      (MIsDivisible (q - i) (r - i) (Sum.elim bd Prod.fst))),
    Sum.inl_injective, fun T c => rfl, fun T hT => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · obtain ⟨hmends, hmYR, hm, hmult, -, -⟩ := hmr bd (fibre tg X T) (hfr T)
    have hRmZ : ∀ c ∈ (mR bd (fibre tg X T) M).image Sum.inr, ends' T c ⊆ Zc := by
      intro c hc
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
      obtain ⟨x, -, he⟩ := mem_image.1 (hmends y hy)
      show y.1 ⊆ Zc
      rw [← he]; exact hbd x
    have hYmr : MIsRGraph (r - i) (Sum.elim bd Prod.fst) (mY bd (fibre tg X T) M) :=
      fun c hc => hm.rgraph c (mem_union_right _ (hmYR hc))
    have hYmcard : (mY bd (fibre tg X T) M).card ≤ Kf :=
      (RefinedAbsorption.Dense.card_le_of_mult (fun c hc => hRmZ c (hmYR hc)) hmult).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hZm))
    have hf := finiteStep (q := q - i) hYmr hYmcard
    have hle : Kf + 2 ^ Kf ≤ Cm + (Kf + 2 ^ Kf) := Nat.le_add_left _ _
    have hch := (IsChainRefiner.ofResidual hf (empty_subset _)).mono' hle hle hle
    have hpre := IsChainRefiner.prepend hm hmYR (Nat.le_add_right _ _) hch
      (disjoint_empty_left _)
    rw [union_empty] at hpre
    refine ⟨fun c hc x hx => ?_, hpre, hRmZ⟩
    obtain ⟨y, -, rfl⟩ := mem_image.1 hc
    exact Sum.inl_ne_inr hx
  · calc ∑ T ∈ Ts, mdeg (fun c => T ∪ ends' T c) ((mR bd (fibre tg X T) M).image Sum.inr) S
        ≤ ∑ T ∈ Ts, (M + 2) ^ 2 * mdeg (fun c => T ∪ bd c) (fibre tg X T) S := by
          refine sum_le_sum fun T _ => ?_
          rw [mdeg_lift, mdeg_lift]
          exact (hmr bd (fibre tg X T) (hfr T)).2.2.2.2.1 _
      _ = (M + 2) ^ 2 * mdeg (liftEnds tg bd) X S := by rw [← mul_sum, mdeg_liftEnds_eq_sum]
      _ ≤ (M + 2) ^ 2 * D := Nat.mul_le_mul_left _ (hdeg S hS)
      _ ≤ Ab * D + Ab * Ts.card :=
          le_add_right (Nat.mul_le_mul_right _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
  · have hle : ∀ T ∈ Ts, pdeg (fun c => T ∪ ends' T c) (mW bd (fibre tg X T) M ∪
        ((mY bd (fibre tg X T) M).powerset.filter
          (MIsDivisible (q - i) (r - i) (Sum.elim bd Prod.fst)))) S ≤
        Cm * (1 + (M + 2) ^ 2) * mdeg (fun c => T ∪ bd c) (fibre tg X T) S + 2 ^ Kf := by
      intro T hT
      obtain ⟨hmends, hmYR, hm, hmult, hdegm, hparm⟩ := hmr bd (fibre tg X T) (hfr T)
      refine (pdeg_union_le _ _ _ S).trans (Nat.add_le_add ?_ ?_)
      · have hne : (S \ T).Nonempty := by
          rw [← card_pos]
          have := card_le_card_sdiff_add_card (s := S) (t := T)
          rw [hTsc T hT] at this
          omega
        refine (pdeg_lift_le _ _ _ S).trans ((pdeg_le_of_parallel hm hparm hne).trans ?_)
        rw [mdeg_lift]
        have hu := RefinedAbsorption.Dense.mdeg_union_le (Sum.elim bd Prod.fst)
          ((fibre tg X T).image Sum.inl) ((mR bd (fibre tg X T) M).image Sum.inr) (S \ T)
        rw [mdeg_image_eq (A := fibre tg X T) (ends := bd) (ends' := Sum.elim bd Prod.fst)
          (g := Sum.inl) (fun c _ => rfl) Sum.inl_injective.injOn subset_rfl] at hu
        have := hdegm (S \ T)
        calc Cm * mdeg (Sum.elim bd Prod.fst)
              ((fibre tg X T).image Sum.inl ∪ (mR bd (fibre tg X T) M).image Sum.inr) (S \ T)
            ≤ Cm * ((1 + (M + 2) ^ 2) * mdeg bd (fibre tg X T) (S \ T)) :=
              Nat.mul_le_mul_left _ (by nlinarith)
          _ = _ := by ring
      · have hYmcard : (mY bd (fibre tg X T) M).card ≤ Kf := by
          refine (RefinedAbsorption.Dense.card_le_of_mult (Z := Zc) (fun c hc => ?_) hmult).trans
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hZm))
          obtain ⟨y, hy, rfl⟩ := mem_image.1 (hmYR hc)
          obtain ⟨x, -, he⟩ := mem_image.1 (hmends y hy)
          show y.1 ⊆ Zc
          rw [← he]; exact hbd x
        refine (pdeg_le_card _ _ _).trans ((card_filter_le _ _).trans ?_)
        rw [card_powerset]
        exact Nat.pow_le_pow_right (by norm_num) hYmcard
    refine (sum_le_sum hle).trans ?_
    rw [sum_add_distrib, ← mul_sum, ← mdeg_liftEnds_eq_sum, sum_const, smul_eq_mul]
    have h1 := Nat.mul_le_mul_left (Cm * (1 + (M + 2) ^ 2)) (hdeg S hS)
    have h2 : Cm * (1 + (M + 2) ^ 2) * D ≤ Ab * D :=
      Nat.mul_le_mul_right _ ((Nat.le_add_left _ _).trans (Nat.le_add_right _ _))
    have h3 : Ts.card * 2 ^ Kf ≤ Ab * Ts.card := by
      rw [mul_comm]; exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
    show _ ≤ Ab * D + Ab * Ts.card
    omega

section Classes

variable {q r i C : ℕ} {n : ℕ} {E : Type} [DecidableEq E] {tg bd : E → Finset (Fin n)}
  {Z : Finset (Fin n)} {X : Finset E}

/-- **Union over finitely many classes of tags.** -/
theorem TRefOut.unionFin {k : ℕ} (cls : Finset (Fin n) → Fin k) (J : Finset (Fin k))
    (β : Fin k → Finset (Fin n) → ℕ)
    (h : ∀ j ∈ J, TRefOut q r i C tg bd Z (X.filter fun x => cls (tg x) = j) (β j)) :
    TRefOut q r i C tg bd Z (X.filter fun x => cls (tg x) ∈ J) (fun S => ∑ j ∈ J, β j S) := by
  induction J using Finset.induction_on with
  | empty =>
    have : (X.filter fun x => cls (tg x) ∈ (∅ : Finset (Fin k))) = ∅ := by simp
    rw [this]; exact TRefOut.empty _
  | insert a J ha ih =>
    have h1 : ((X.filter fun x => cls (tg x) ∈ insert a J).filter fun x => cls (tg x) = a) =
        X.filter fun x => cls (tg x) = a := by
      ext x; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨⟨hx, -⟩, h⟩; exact ⟨hx, h⟩
      · rintro ⟨hx, h⟩; exact ⟨⟨hx, Or.inl h⟩, h⟩
    have h2 : ((X.filter fun x => cls (tg x) ∈ insert a J).filter fun x => ¬ cls (tg x) = a) =
        X.filter fun x => cls (tg x) ∈ J := by
      ext x; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨⟨hx, h | h⟩, h'⟩
        · exact absurd h h'
        · exact ⟨hx, h⟩
      · rintro ⟨hx, h⟩; exact ⟨⟨hx, Or.inr h⟩, fun h' => ha (h' ▸ h)⟩
    have hu := TRefOut.union (X := X.filter fun x => cls (tg x) ∈ insert a J)
      (fun T => cls T = a) (β₁ := β a) (β₂ := fun S => ∑ j ∈ J, β j S)
      (by rw [h1]; exact h a (mem_insert_self _ _))
      (by rw [h2]; exact ih fun j hj => h j (mem_insert_of_mem hj))
    refine hu.mono le_rfl fun S _ => le_of_eq ?_
    rw [sum_insert ha]; rfl

/-- At most one of pairwise exclusive conditions holds. -/
theorem sum_ite_le_sup {k : ℕ} (c : Fin k → Prop) [DecidablePred c] (b : Fin k → ℕ)
    (hex : ∀ j l, c j → c l → j = l) :
    ∑ j, (if c j then b j else 0) ≤ univ.sup b := by
  by_cases h : ∃ j, c j
  · obtain ⟨j, hj⟩ := h
    rw [sum_eq_single j (fun l _ hl => if_neg fun hl' => hl (hex l j hl' hj))
      (fun hj' => absurd (mem_univ j) hj'), if_pos hj]
    exact le_sup (mem_univ j)
  · push_neg at h
    rw [sum_eq_zero fun j _ => if_neg (h j)]
    exact Nat.zero_le _

set_option maxHeartbeats 2000000 in
/-- **One level of the class splitting.**  The tags are split into four classes of at most a
quarter of the tags each, and the reserve `Z` contains four disjoint quarters; if every class can
be handled with its own quarter (`hcls`), then all the tags can, and the second budgets of the
classes are not added up. -/
theorem classStep {K : ℕ} (hTs : (X.image tg).card ≤ K * Z.card + K + 1)
    (P : ℕ → ℕ → Prop)
    (hcls : ∀ (p : Finset (Fin n) → Prop) [DecidablePred p] (Q : Finset (Fin n)), Q ⊆ Z →
      Q.card = Z.card / 4 →
      ((X.filter fun x => p (tg x)).image tg).card ≤ K * Q.card + K + 1 →
      ∃ b₁ b₂, P b₁ b₂ ∧ TRefOut q r i C tg bd Z (X.filter fun x => p (tg x))
        (fun S => b₁ + if (S ∩ Z).Nonempty ∧ S ∩ Z ⊆ Q then b₂ else 0)) :
    ∃ b₁ b₂ : Fin 4 → ℕ, (∀ j, P (b₁ j) (b₂ j)) ∧
      TRefOut q r i C tg bd Z X (fun _ => ∑ j, b₁ j + univ.sup b₂) := by
  set m := Z.card / 4 with hm
  -- four disjoint quarters
  obtain ⟨Q₀, hQ₀, hc₀⟩ := exists_subset_card_eq (s := Z) (n := m) (by omega)
  obtain ⟨Q₁, hQ₁, hc₁⟩ := exists_subset_card_eq (s := Z \ Q₀) (n := m)
    (by rw [card_sdiff_of_subset hQ₀]; omega)
  obtain ⟨Q₂, hQ₂, hc₂⟩ := exists_subset_card_eq (s := Z \ (Q₀ ∪ Q₁)) (n := m) (by
    have h01 : Q₀ ∪ Q₁ ⊆ Z := union_subset hQ₀ (hQ₁.trans sdiff_subset)
    rw [card_sdiff_of_subset h01, card_union_of_disjoint (disjoint_of_subset_right hQ₁
      disjoint_sdiff)]; omega)
  obtain ⟨Q₃, hQ₃, hc₃⟩ := exists_subset_card_eq (s := Z \ (Q₀ ∪ Q₁ ∪ Q₂)) (n := m) (by
    have h01 : Q₀ ∪ Q₁ ∪ Q₂ ⊆ Z :=
      union_subset (union_subset hQ₀ (hQ₁.trans sdiff_subset)) (hQ₂.trans sdiff_subset)
    rw [card_sdiff_of_subset h01, card_union_of_disjoint (disjoint_of_subset_right hQ₂
      disjoint_sdiff), card_union_of_disjoint (disjoint_of_subset_right hQ₁ disjoint_sdiff)]
    omega)
  set Q : Fin 4 → Finset (Fin n) := ![Q₀, Q₁, Q₂, Q₃] with hQdef
  have hQZ : ∀ j, Q j ⊆ Z := by
    intro j; fin_cases j
    · exact hQ₀
    · exact hQ₁.trans sdiff_subset
    · exact hQ₂.trans sdiff_subset
    · exact hQ₃.trans sdiff_subset
  have hQc : ∀ j, (Q j).card = m := by
    intro j; fin_cases j <;> assumption
  have hQdisj : ∀ j l, j ≠ l → Disjoint (Q j) (Q l) := by
    have d01 : Disjoint Q₀ Q₁ := disjoint_of_subset_right hQ₁ disjoint_sdiff
    have d02 : Disjoint Q₀ Q₂ := disjoint_of_subset_right hQ₂
      (disjoint_of_subset_left subset_union_left disjoint_sdiff)
    have d12 : Disjoint Q₁ Q₂ := disjoint_of_subset_right hQ₂
      (disjoint_of_subset_left subset_union_right disjoint_sdiff)
    have d03 : Disjoint Q₀ Q₃ := disjoint_of_subset_right hQ₃
      (disjoint_of_subset_left (subset_union_left.trans subset_union_left) disjoint_sdiff)
    have d13 : Disjoint Q₁ Q₃ := disjoint_of_subset_right hQ₃
      (disjoint_of_subset_left (subset_union_right.trans subset_union_left) disjoint_sdiff)
    have d23 : Disjoint Q₂ Q₃ := disjoint_of_subset_right hQ₃
      (disjoint_of_subset_left subset_union_right disjoint_sdiff)
    intro j l hjl
    fin_cases j <;> fin_cases l <;> simp_all [hQdef, disjoint_comm]
  -- four classes of tags
  set Ts := X.image tg with hTsdef
  obtain ⟨B, hB, hBc⟩ := exists_subset_card_eq (s := Ts) (n := Ts.card / 2) (by omega)
  obtain ⟨B₁, hB₁, hB₁c⟩ := exists_subset_card_eq (s := B) (n := B.card / 2) (by omega)
  obtain ⟨B₃, hB₃, hB₃c⟩ := exists_subset_card_eq (s := Ts \ B) (n := (Ts \ B).card / 2)
    (by omega)
  set cls : Finset (Fin n) → Fin 4 := fun T =>
    if T ∈ B then (if T ∈ B₁ then 0 else 1) else (if T ∈ B₃ then 2 else 3) with hcls'
  have hTB : (Ts \ B).card = Ts.card - Ts.card / 2 := by rw [card_sdiff_of_subset hB, hBc]
  have hclsc : ∀ j, (Ts.filter fun T => cls T = j).card ≤ (Ts.card + 3) / 4 := by
    intro j
    fin_cases j
    · refine (card_le_card fun T hT => ?_).trans (show B₁.card ≤ _ by omega)
      obtain ⟨-, hT⟩ := mem_filter.1 hT
      simp only [hcls'] at hT
      split_ifs at hT with h1 h2 <;> first | exact h2 | simp at hT
    · refine (card_le_card fun T hT => ?_).trans
        (show (B \ B₁).card ≤ _ by rw [card_sdiff_of_subset hB₁]; omega)
      obtain ⟨-, hT⟩ := mem_filter.1 hT
      simp only [hcls'] at hT
      split_ifs at hT with h1 h2 <;> first | exact mem_sdiff.2 ⟨h1, h2⟩ | simp at hT
    · refine (card_le_card fun T hT => ?_).trans (show B₃.card ≤ _ by omega)
      obtain ⟨-, hT⟩ := mem_filter.1 hT
      simp only [hcls'] at hT
      split_ifs at hT with h1 h2 h3 <;> first | exact h3 | simp at hT
    · refine (card_le_card fun T hT => ?_).trans
        (show ((Ts \ B) \ B₃).card ≤ _ by rw [card_sdiff_of_subset hB₃]; omega)
      obtain ⟨hTs', hT⟩ := mem_filter.1 hT
      simp only [hcls'] at hT
      split_ifs at hT with h1 h2 h3 <;> first
        | exact mem_sdiff.2 ⟨mem_sdiff.2 ⟨hTs', h1⟩, h3⟩ | simp at hT
  have hKm : ∀ j, ((X.filter fun x => cls (tg x) = j).image tg).card ≤ K * (Q j).card + K + 1 := by
    intro j
    rw [image_filter_tg (p := fun T => cls T = j), hQc j]
    have h2 : K * Z.card ≤ 4 * (K * m) + 3 * K := by
      have : Z.card ≤ 4 * m + 3 := by omega
      nlinarith
    refine (hclsc j).trans ?_
    omega
  -- each class
  have hc := fun j => hcls (fun T => cls T = j) (Q j) (hQZ j) (hQc j) (hKm j)
  choose b₁ b₂ hP hout using hc
  refine ⟨b₁, b₂, hP, ?_⟩
  have hall := TRefOut.unionFin cls univ
    (fun j S => b₁ j + if (S ∩ Z).Nonempty ∧ S ∩ Z ⊆ Q j then b₂ j else 0)
    (fun j _ => hout j)
  have hX : (X.filter fun x => cls (tg x) ∈ (univ : Finset (Fin 4))) = X := by
    ext x; simp
  rw [hX] at hall
  refine hall.mono le_rfl fun S _ => ?_
  rw [sum_add_distrib]
  refine Nat.add_le_add_left (sum_ite_le_sup _ b₂ fun j l hj hl => ?_) _
  by_contra hjl
  obtain ⟨v, hv⟩ := hj.1
  exact disjoint_left.1 (hQdisj j l hjl) (hj.2 hv) (hl.2 hv)

end Classes

end RefinedAbsorption.LinkSpread
