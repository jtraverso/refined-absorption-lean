module
public import RequestProject.HyperPlan.Class
public import RequestProject.OddGrid.Compose

/-!
# Divisibility in a stage, uniformity `r`

The stages of `RequestProject/OddGrid/Stage.lean` (switches `P1`, `P0` and accumulator chains) do
not depend on the uniformity.  Here their divisibility is proved for every `r`:

* `ldivR_P1`, `ldivR_chW`: switch pieces `P1` and chain pieces are divisible;
* `ldivR_P0`: the piece `P0 ℓ` is divisible as soon as the rerouting of `ℓ` has, at every face
  `S`, a *defect* (`defect`) whose product with the weight of `ℓ` is divisible by
  `binom(q - |S|, r - |S|)`;
* `stage_ldecompR`: a stage is a label-level decomposition for `r`-divisibility.
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner
  RefinedAbsorption.GridRefiner RefinedAbsorption.OddGrid

variable {n K : ℕ}

/-- The face class of a list of weighted sets. -/
def lfcl (l : List (Finset (Fin n) × ZMod K)) (S : Finset (Fin n)) : ZMod K :=
  (l.map fun p => if S ⊆ p.1 then p.2 else 0).sum

/-- The defect at `S` of rerouting one copy of `e` into the signed sets `ro`. -/
def defect (ro : List (Finset (Fin n) × ZMod K)) (e S : Finset (Fin n)) : ZMod K :=
  lfcl ro S - if S ⊆ e then 1 else 0

/-- Weighting a signed route by `w`. -/
def wroute (ro : List (Finset (Fin n) × ZMod K)) (w : ZMod K) :
    List (Finset (Fin n) × ZMod K) :=
  ro.map fun p => (p.1, p.2 * w)

lemma lfcl_wroute (ro : List (Finset (Fin n) × ZMod K)) (w : ZMod K) (S : Finset (Fin n)) :
    lfcl (wroute ro w) S = lfcl ro S * w := by
  unfold lfcl wroute
  rw [List.map_map, ← List.sum_map_mul_right]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  split_ifs <;> simp

variable [NeZero K] {q r : ℕ} (hK : ModsOK q r K)
  {t : ℕ} {I : Finset (Lab n K)} {restF : RestF n K} {pw : Lab n K → Finset (Fin n) × ZMod K}

include hK in
lemma ldivR_P1 (hpw : StagePW t restF pw) (ℓ : Lab n K) : LDivR q r pw (P1 t ℓ) := by
  apply ldivR_of_one_set hK (e := (pw ℓ).1)
  · intro x hx
    simp only [P1, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · rfl
    · rw [hpw.anti]
  · have hne : ℓ ≠ Lab.anti t ℓ := by
      intro h
      have := congrArg sizeOf h
      simp at this
    simp [P1, sum_pair hne, hpw.anti]

include hK in
lemma ldivR_chW (hpw : StagePW t restF pw) {e : Finset (Fin n)} {P : Finset (Lab n K)}
    (hP : P ∈ chW (Lab.cp t e) (Lab.cn t e) (item t I restF e) (iw t I restF e)
      (slen t I restF e)) : LDivR q r pw P := by
  simp only [chW, mem_union, mem_biUnion, mem_filter, mem_product, mem_univ, and_true,
    mem_insert, mem_singleton, mem_image] at hP
  rcases hP with ⟨⟨k, s⟩, ⟨hk, -⟩, rfl | rfl⟩ | ⟨⟨k, s⟩, hk, rfl⟩
  · obtain ⟨ℓ, -, j, -, hj⟩ := item_isRest hk
    have hpi := pw_item (I := I) hpw hk
    apply ldivR_of_one_set hK (e := e)
    · intro x hx
      simp only [chT, if_true, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · rw [hpw.cp]
      · rw [hpi]
      · rw [hpw.cn]
    · simp only [chT, if_true]
      rw [hj] at hpi ⊢
      rw [sum_insert (by simp), sum_insert (by simp), sum_singleton, hpw.cp, hpw.cn, hpi]
      ring
  · apply ldivR_of_one_set hK (e := e)
    · intro x hx
      simp only [chT, Bool.false_eq_true, if_false, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [hpw.cp]
      · rw [hpw.cn]
    · simp only [chT, Bool.false_eq_true, if_false]
      rw [sum_pair (by simp), hpw.cp, hpw.cn]
      ring
  · apply ldivR_of_one_set hK (e := e)
    · intro x hx
      simp only [chQ, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [hpw.cn]
      · rw [hpw.cp]
    · rw [chQ, sum_pair (by simp), hpw.cp, hpw.cn]
      ring

omit [NeZero K] in
/-- The face class of the rests of `ℓ`. -/
lemma fcl_rests (hpw : StagePW t restF pw) (ℓ : Lab n K) (S : Finset (Fin n)) :
    fcl pw (rests t restF ℓ) S = lfcl (restF ℓ) S := by
  rw [fcl, rests, sum_image (fun a _ b _ h => by simpa using h)]
  simp only [hpw.rest]
  rw [lfcl, ← sum_range_getD (restF ℓ) (∅, 0) (fun s => if S ⊆ s.1 then s.2 else 0)]

include hK in
/-- **The switch piece `P0`** is divisible when the defects of the rerouting, multiplied by the
weight, are divisible. -/
lemma ldivR_P0 (hpw : StagePW t restF pw) {ℓ : Lab n K} {ro : List (Finset (Fin n) × ZMod K)}
    (hw : restF ℓ = wroute ro (pw ℓ).2)
    (hdef : ∀ S : Finset (Fin n), S.card < r →
      (q - S.card).choose (r - S.card) ∣ (defect ro (pw ℓ).1 S * (pw ℓ).2).val) :
    LDivR q r pw (P0 t restF ℓ) := by
  rw [ldivR_iff hK]
  intro S hS
  have h : fcl pw (P0 t restF ℓ) S = defect ro (pw ℓ).1 S * (pw ℓ).2 := by
    rw [P0, ← Finset.singleton_union, fcl_union pw (disjoint_singleton_left.2
      (anti_notMem_rests ℓ)), fcl_rests hpw, hw, lfcl_wroute, fcl_singleton, hpw.anti, defect]
    split_ifs <;> ring
  rw [h]; exact hdef S hS

include hK in
lemma ldivR_stW (hpw : StagePW t restF pw) (hP0 : ∀ ℓ ∈ I, LDivR q r pw (P0 t restF ℓ))
    {P : Finset (Lab n K)} (hP : P ∈ stW t I restF) : LDivR q r pw P := by
  simp only [stW, mem_union, mem_image, mem_biUnion] at hP
  rcases hP with (⟨ℓ, -, rfl⟩ | ⟨ℓ, hℓ, rfl⟩) | ⟨e, -, hP⟩
  · exact ldivR_P1 hK hpw ℓ
  · exact hP0 ℓ hℓ
  · exact ldivR_chW hK hpw hP

include hK in
/-- The labels of a stage form a divisible multigraph. -/
lemma ldivR_stR (hpw : StagePW t restF pw) (hI : ∀ ℓ ∈ I, NotStage t ℓ)
    (hP0 : ∀ ℓ ∈ I, LDivR q r pw (P0 t restF ℓ)) : LDivR q r pw (stR t I restF) := by
  obtain ⟨hsub, hpd, hdj, heq⟩ := stage_decomp (restF := restF) hI ∅ (empty_subset _)
  rw [union_empty] at heq
  rw [← heq]
  refine ldivR_union hdj (ldivR_sup hpd fun P hP => ldivR_stW hK hpw hP0 (hsub hP))
    (ldivR_of_wt_zero ?_)
  intro x hx
  simp only [stRes, mem_image] at hx
  obtain ⟨e, -, rfl⟩ := hx
  rw [hpw.cp, sig_eq_sum e ∅ (empty_subset _), sum_empty]

include hK in
/-- The residue of a stage is divisible when the present inputs are. -/
lemma ldivR_stRes (hpw : StagePW t restF pw) (hI : ∀ ℓ ∈ I, NotStage t ℓ)
    (hP0 : ∀ ℓ ∈ I, LDivR q r pw (P0 t restF ℓ)) {Ls : Finset (Lab n K)} (hLs : Ls ⊆ I)
    (hdiv : LDivR q r pw Ls) : LDivR q r pw (stRes t I restF Ls) := by
  obtain ⟨hsub, hpd, hdj, heq⟩ := stage_decomp (restF := restF) hI Ls hLs
  exact ldivR_of_partition (ldivR_union (disjoint_stR hI hLs) (ldivR_stR hK hpw hI hP0) hdiv)
    hpd (fun P hP => ldivR_stW hK hpw hP0 (hsub hP)) hdj heq

include hK in
/-- **A stage is a label-level decomposition** (uniformity `r`). -/
theorem stage_ldecompR (hpw : StagePW t restF pw) (hI : ∀ ℓ ∈ I, NotStage t ℓ)
    (hP0 : ∀ ℓ ∈ I, LDivR q r pw (P0 t restF ℓ)) (Y : Finset (Lab n K))
    (hY : ∀ Ls ⊆ I, LDivR q r pw Ls → stRes t I restF Ls ⊆ Y) :
    LDecomp (LDivR q r pw) I (stR t I restF) Y (stW t I restF) := by
  intro Ls hLs hdiv
  obtain ⟨hsub, hpd, hdj, heq⟩ := stage_decomp (restF := restF) hI Ls hLs
  exact ⟨_, hsub, _, hY Ls hLs hdiv, ldivR_stRes hK hpw hI hP0 hLs hdiv, hpd, hdj, heq⟩

end RefinedAbsorption.HyperPlan
