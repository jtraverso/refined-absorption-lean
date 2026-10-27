module
public import RequestProject.HyperPlan.Native
public import RequestProject.HyperPlan.Moves

/-!
# The grid plans of `r = 2` are `r`-uniform plans

The plans of `RequestProject/OddGrid` (signed walks and moves of pairs) are translated into the
general format of `HyperPlan` (signed lists of `r`-sets): a walk becomes its signed list of pairs and
a move becomes the one-element list `[(f, 1)]`.

* `planOKR_toR`: a valid grid plan is a valid `2`-uniform plan (`PlanOKR q 2 3`), with the same
  families of current pairs and smaller route loads.
* `rPlans_two`: hence `RPlans q 2` for every `q ≥ 3`; this checks that the combinatorial statement
  `RPlans` is satisfiable, and recovers `NativeStrongMultiRefiners q 2` through the general reduction
  `nativeStrongMultiRefiners_of_rPlans` (`nativeStrongMultiRefiners_two_viaR`).
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid RefinedAbsorption.Placement

variable {n K : ℕ} [NeZero K]

/-- A grid stage, as a stage of signed lists. -/
def toSpecR (s : Spec n) : SpecR n K := fun P e => (s P e).rest 1

variable (sp : List (Spec n)) (X : Finset (Finset (Fin n)))

omit [NeZero K] in
lemma getD_map_toSpecR {t : ℕ} (ht : t < sp.length) :
    (sp.map (toSpecR (K := K))).getD t idSpecR = toSpecR (sp.getD t idSpec) := by
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getD_eq_getElem _ _ ht,
    List.getElem_map]

lemma prunR_toR {t : ℕ} (ht : t ≤ sp.length) :
    prunR (sp.map (toSpecR (K := K))) X t = prun sp X t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [prunR_succ, prun_succ, ih (by omega)]
    apply biUnion_congr rfl
    intro e _
    unfold rtR
    rw [getD_map_toSpecR sp (by omega), ih (by omega), toSpecR, Route.rest_pairs]
    rfl

lemma rtR_toR {t : ℕ} (ht : t < sp.length) (e : Finset (Fin n)) :
    rtR (sp.map (toSpecR (K := K))) X t e = (rt sp X t e).rest 1 := by
  unfold rtR
  rw [getD_map_toSpecR sp ht, prunR_toR sp X ht.le]
  rfl

omit [NeZero K] in
lemma lfcl_singleton (l : List (Finset (Fin n) × ZMod K)) (v : Fin n) :
    lfcl l {v} = lcls l v := by
  unfold lfcl lcls
  congr 1
  apply List.map_congr_left
  intro p _
  simp [singleton_subset_iff]

omit [NeZero K] in
lemma lfcl_empty (l : List (Finset (Fin n) × ZMod K)) : lfcl l ∅ = ltot l := by
  unfold lfcl ltot
  simp

omit [NeZero K] in
lemma card_lt_two {S : Finset (Fin n)} (hS : S.card < 2) : S = ∅ ∨ ∃ v, S = {v} := by
  rcases Nat.lt_or_ge S.card 1 with h | h
  · left; exact card_eq_zero.1 (by omega)
  · right; exact card_eq_one.1 (by omega)

omit [NeZero K] in
lemma pair_mem_wpairs {l : List (Fin n)} (h : l.IsChain (· ≠ ·)) {f : Finset (Fin n)}
    (hf : f ∈ wpairs l) : f.card = 2 := by
  induction l with
  | nil => simp [wpairs] at hf
  | cons p tl ih =>
    cases tl with
    | nil => simp [wpairs] at hf
    | cons q rest =>
      simp only [wpairs, List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact card_pair (List.isChain_cons_cons.1 h).1
      · exact ih (List.isChain_cons_cons.1 h).2 hf

variable {sp X} {q : ℕ}

/-- **A valid grid plan is a valid `2`-uniform plan.** -/
theorem planOKR_toR (hK : ModsOK q 2 K) (hok : PlanOK sp X) :
    PlanOKR q 2 3 (sp.map (toSpecR (K := K))) X where
  rg := hok.rg
  route t ht e he := by
    rw [List.length_map] at ht
    rw [prunR_toR sp X ht.le] at he
    have hro := hok.route t ht e he
    have hmv := hok.move t ht e he
    rw [rtR_toR sp X ht]
    cases hr : rt sp X t e with
    | walk l =>
      rw [hr] at hro
      obtain ⟨p, tl, rfl, hch, hodd, -, rfl, hne⟩ := hro
      refine ⟨?_, ?_⟩
      · intro x hx
        have : x.1 ∈ (walkL (p :: tl) (1 : ZMod K)).map Prod.fst := List.mem_map_of_mem hx
        rw [map_fst_walkL] at this
        exact pair_mem_wpairs hch this
      · intro s _ S hS
        have h0 : defect (Route.rest (.walk (p :: tl)) (1 : ZMod K))
            {p, (p :: tl).getLast (List.cons_ne_nil _ _)} S = 0 := by
          unfold defect
          rcases card_lt_two hS with rfl | ⟨v, rfl⟩
          · rw [lfcl_empty]
            simp only [Route.rest, ltot_walkL, hodd, if_false, empty_subset, if_true, sub_self]
          · rw [lfcl_singleton]
            simp only [Route.rest, lcls_walkL_odd p tl hch hodd, singleton_subset_iff,
              mem_insert, mem_singleton]
            by_cases h1 : v = p
            · subst h1
              simp [hne]
            · by_cases h2 : v = (p :: tl).getLast (List.cons_ne_nil _ _)
              · simp [h2, Ne.symm hne]
              · simp [h1, h2]
        rw [h0, zero_mul, ZMod.val_zero]
        exact dvd_zero _
    | move f =>
      rw [hr] at hro hmv
      obtain ⟨ht1, u, hu, hlone⟩ := hmv rfl
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Route.rest, List.mem_singleton] at hx
        subst hx; exact hro
      · intro s hs S hS
        have hs' : (q - 1) ∣ s.val := by
          unfold wts at hs
          rw [if_neg (by omega), prunR_toR sp X ht.le] at hs
          simp only [allowedR, mem_filter, mem_univ, true_and] at hs
          have := hs {u} (by simpa using hu) (by simp) (by
            intro f hf hsub
            exact hlone f hf (singleton_subset_iff.1 hsub))
          simpa using this
        rcases card_lt_two hS with rfl | ⟨v, rfl⟩
        · have : defect (Route.rest (.move f) (1 : ZMod K)) e ∅ = 0 := by
            simp [defect, lfcl, Route.rest]
          rw [this, zero_mul, ZMod.val_zero]
          exact dvd_zero _
        · have hK1 : (q - 1) ∣ K := by simpa using hK 1 (by norm_num)
          simpa using dvd_val_mul hK1 (a := defect (Route.rest (.move f) (1 : ZMod K)) e {v}) hs'
  len t ht e he := by
    rw [List.length_map] at ht
    rw [prunR_toR sp X ht.le] at he
    have hro := hok.route t ht e he
    rw [rtR_toR sp X ht]
    cases hr : rt sp X t e with
    | walk l =>
      rw [hr] at hro
      obtain ⟨p, tl, rfl, -, -, hl, -, -⟩ := hro
      simp only [Route.rest, length_walkL, List.length_cons]
      omega
    | move f => simp [Route.rest]

/-- The route loads of the translated plan are at most those of the grid plan. -/
lemma passR_toR_le (hok : PlanOK sp X) {t : ℕ} (ht : t < sp.length) (v : Fin n) :
    passR (sp.map (toSpecR (K := K))) X t {v} ≤ OddGrid.pass sp X t v := by
  unfold passR OddGrid.pass
  rw [prunR_toR sp X ht.le]
  apply card_le_card
  intro e he
  simp only [mem_filter] at he ⊢
  refine ⟨he.1, ?_⟩
  have hv := singleton_subset_iff.1 he.2
  rw [rtR_toR sp X ht] at hv
  unfold visitR at hv
  rcases mem_union.1 hv with hv | hv
  · exact pair_subset_visit (hok.route t ht e he.1) hv
  · obtain ⟨f, hf, hvf⟩ := mem_sup.1 hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hf)
    exact rest_subset_visit _ _ e hx hvf

/-- **`RPlans q 2` for every `q ≥ 3`**, from the grid plans of `OddGrid`. -/
theorem rPlans_two {q : ℕ} (hq : 3 ≤ q) : RPlans q 2 := by
  refine ⟨1205, 3, 256, by norm_num, 25, ?_⟩
  intro n hn X D hX hXD _
  have hK1 : 1 < Kmod q 2 := one_lt_Kmod (by norm_num) (by omega)
  haveI : NeZero (Kmod q 2) := ⟨by omega⟩
  set Dn := ⌊D⌋₊
  have hD : ∀ y : Fin n, (X.filter (y ∈ ·)).card ≤ Dn := by
    intro y
    have h := hXD {y} (by simp)
    have heq : deg X {y} = (X.filter (y ∈ ·)).card := by
      unfold deg; congr 1; apply filter_congr; intro e _; exact singleton_subset_iff
    rw [heq] at h
    exact Nat.le_floor h
  obtain ⟨sp, hok, hT, hM, hP⟩ := base_plan hn hX hD
  refine ⟨inferInstance, sp.map toSpecR, planOKR_toR (modsOK_Kmod q 2) hok,
    by simpa using hT, ?_, ?_⟩
  · rw [List.length_map, prunR_toR sp X le_rfl]; exact hM
  · intro S hS
    obtain ⟨v, rfl⟩ := card_eq_one.1 (by simpa using hS)
    rw [List.length_map]
    have hsum : ∑ t ∈ range sp.length, passR (sp.map (toSpecR (K := Kmod q 2))) X t {v} ≤
        5 * Dn + 400 * Nat.sqrt n * Nat.clog 2 n :=
      (sum_le_sum fun t ht => passR_toR_le hok (mem_range.1 ht) v).trans (hP v)
    have hsum' : ((∑ t ∈ range sp.length, passR (sp.map (toSpecR (K := Kmod q 2))) X t {v} : ℕ)
        : ℝ) ≤ 5 * (Dn : ℝ) + 400 * (Nat.sqrt n : ℝ) * (Nat.clog 2 n : ℝ) := by
      exact_mod_cast hsum
    refine hsum'.trans ?_
    set L := (n : ℝ) ^ (1 - 1 / ((2 : ℕ) : ℝ)) * Real.log n
    have hL : 1 ≤ L := one_le_sqrt_log (by omega)
    have hfl : (Dn : ℝ) ≤ max D 0 := by
      rcases le_or_gt 0 D with h0 | h0
      · exact (Nat.floor_le h0).trans (le_max_left _ _)
      · have : Dn = 0 := Nat.floor_eq_zero.2 (by linarith)
        rw [this]; simp
    have hmax : max D 0 ≤ max D L := max_le_max le_rfl (by linarith)
    have hLm : L ≤ max D L := le_max_right _ _
    have hs := sqrt_le_rpow n
    have hc := clog_le_log (n := n) (by omega)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hc0 : (0 : ℝ) ≤ Nat.clog 2 n := Nat.cast_nonneg _
    have hsc : (Nat.sqrt n : ℝ) * Nat.clog 2 n ≤ 3 * L := by
      calc (Nat.sqrt n : ℝ) * Nat.clog 2 n
          ≤ (n : ℝ) ^ (1 - 1 / ((2 : ℕ) : ℝ)) * (3 * Real.log n) :=
            mul_le_mul hs hc hc0 (by positivity)
        _ = 3 * L := by ring
    have h1 : (Dn : ℝ) ≤ max D L := hfl.trans hmax
    have h2 : (400 : ℝ) * (Nat.sqrt n : ℝ) * (Nat.clog 2 n : ℝ) =
        400 * ((Nat.sqrt n : ℝ) * Nat.clog 2 n) := by ring
    rw [h2]
    push_cast
    linarith

/-- `NativeStrongMultiRefiners q 2` once more, now through the general reduction from plans. -/
theorem nativeStrongMultiRefiners_two_viaR {q : ℕ} (hq : 3 ≤ q) : NativeStrongMultiRefiners q 2 :=
  nativeStrongMultiRefiners_of_rPlans (by norm_num) (by omega) (rPlans_two hq)

end RefinedAbsorption.HyperPlan
