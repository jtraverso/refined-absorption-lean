module
public import RefinedAbsorption.OddGrid.Chain

/-!
# One stage of the grid refiner

A stage `t` takes a set `I` of input labels and a *rerouting* `restF`: every input `ℓ` is
replaced by the weighted pairs `restF ℓ`.  The stage consists of

* a *switch* for every input `ℓ`: the pieces `P1 ℓ = {ℓ, anti ℓ}` (used when `ℓ` is present) and
  `P0 ℓ = {anti ℓ} ∪ rests ℓ` (used when `ℓ` is absent);
* an accumulator chain (`OddGrid.Chain`) on every output pair `e`, whose items are the rests lying
  on `e`.

For every set `Ls ⊆ I` of present inputs, the pieces `P1 ℓ` (`ℓ ∈ Ls`), `P0 ℓ` (`ℓ ∉ Ls`) and the
used chain pieces partition `R ∪ Ls` except for the residue: one carry `cp t e (len e) σ_e` per
output pair, where `σ_e` is the total weight of the rests on `e` of the present inputs
(`stage_decomp`).  This statement does not involve divisibility.
-/

@[expose] public section

namespace RefinedAbsorption.OddGrid

open Finset

section ToList

variable {α : Type} [DecidableEq α]

lemma toList_getD_mem (s : Finset α) (d : α) {k : ℕ} (hk : k ∈ Icc 1 s.card) :
    s.toList.getD (k - 1) d ∈ s := by
  have hk' := mem_Icc.1 hk
  have hl : k - 1 < s.toList.length := by rw [length_toList]; omega
  rw [List.getD_eq_getElem _ _ hl, ← mem_toList]
  exact List.getElem_mem _

lemma toList_getD_inj (s : Finset α) (d : α) {k k' : ℕ} (hk : k ∈ Icc 1 s.card)
    (hk' : k' ∈ Icc 1 s.card) (h : s.toList.getD (k - 1) d = s.toList.getD (k' - 1) d) :
    k = k' := by
  have h1 := mem_Icc.1 hk
  have h2 := mem_Icc.1 hk'
  have hl : k - 1 < s.toList.length := by rw [length_toList]; omega
  have hl' : k' - 1 < s.toList.length := by rw [length_toList]; omega
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hl'] at h
  have := (List.Nodup.getElem_inj_iff (nodup_toList s)).1 h
  omega

lemma toList_getD_surj (s : Finset α) (d : α) {x : α} (hx : x ∈ s) :
    ∃ k ∈ Icc 1 s.card, s.toList.getD (k - 1) d = x := by
  rw [← mem_toList, List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  refine ⟨i + 1, mem_Icc.2 ⟨by omega, ?_⟩, ?_⟩
  · rw [length_toList] at hi; omega
  · rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ hi]

end ToList

variable {n K : ℕ}

/-- Labels that do not belong to stage `t`. -/
def NotStage (t : ℕ) : Lab n K → Prop
  | .x _ => True
  | .anti t' _ => t' ≠ t
  | .rest t' _ _ => t' ≠ t
  | .cp t' _ _ _ => t' ≠ t
  | .cn t' _ _ _ => t' ≠ t

/-- The input a rest comes from. -/
def src : Lab n K → Lab n K
  | .rest _ ℓ _ => ℓ
  | ℓ => ℓ

/-- A rerouting rule. -/
abbrev RestF (n K : ℕ) := Lab n K → List (Finset (Fin n) × ZMod K)

/-- The pair of a rest label. -/
def restPair (restF : RestF n K) : Lab n K → Finset (Fin n)
  | .rest _ ℓ k => ((restF ℓ).getD k (∅, 0)).1
  | _ => ∅

/-- The weight of a rest label. -/
def restWt (restF : RestF n K) : Lab n K → ZMod K
  | .rest _ ℓ k => ((restF ℓ).getD k (∅, 0)).2
  | _ => 0

variable (t : ℕ) (I : Finset (Lab n K)) (restF : RestF n K)

/-- The rests of an input. -/
def rests (ℓ : Lab n K) : Finset (Lab n K) := (range (restF ℓ).length).image (Lab.rest t ℓ)

/-- All rests of the stage. -/
def restSet : Finset (Lab n K) := I.biUnion (rests t restF)

/-- The output pairs. -/
def outs : Finset (Finset (Fin n)) := (restSet t I restF).image (restPair restF)

/-- The rests lying on the pair `e`. -/
def onPair (e : Finset (Fin n)) : Finset (Lab n K) :=
  (restSet t I restF).filter (fun i => restPair restF i = e)

/-- The length of the chain on `e`. -/
def slen (e : Finset (Fin n)) : ℕ := (onPair t I restF e).card

/-- The `k`-th item (`1 ≤ k ≤ slen e`) of the chain on `e`. -/
noncomputable def item (e : Finset (Fin n)) (k : ℕ) : Lab n K :=
  (onPair t I restF e).toList.getD (k - 1) (.x ∅)

/-- The weight of the `k`-th item of the chain on `e`. -/
noncomputable def iw (e : Finset (Fin n)) (k : ℕ) : ZMod K := restWt restF (item t I restF e k)

/-- Switch piece used when the input is present. -/
def P1 (ℓ : Lab n K) : Finset (Lab n K) := {ℓ, .anti t ℓ}

/-- Switch piece used when the input is absent. -/
def P0 (ℓ : Lab n K) : Finset (Lab n K) := insert (.anti t ℓ) (rests t restF ℓ)

variable [NeZero K]

/-- The labels of the stage. -/
def stR : Finset (Lab n K) :=
  I.image (.anti t) ∪ restSet t I restF ∪
    (outs t I restF).biUnion (fun e => chR (Lab.cp t e) (Lab.cn t e) (slen t I restF e))

/-- The pieces of the stage. -/
noncomputable def stW : Finset (Finset (Lab n K)) :=
  I.image (P1 t) ∪ I.image (P0 t restF) ∪
    (outs t I restF).biUnion (fun e =>
      chW (Lab.cp t e) (Lab.cn t e) (item t I restF e) (iw t I restF e) (slen t I restF e))

/-- Presence of the `k`-th item of the chain on `e`. -/
def spres (e : Finset (Fin n)) (Ls : Finset (Lab n K)) (k : ℕ) : Prop :=
  src (item t I restF e k) ∈ Ls

noncomputable instance (e : Finset (Fin n)) (Ls : Finset (Lab n K)) :
    DecidablePred (spres t I restF e Ls) := fun k => by unfold spres; infer_instance

/-- The residual value of the chain on `e`. -/
noncomputable def sig (e : Finset (Fin n)) (Ls : Finset (Lab n K)) : ZMod K :=
  psum (iw t I restF e) (spres t I restF e Ls) (slen t I restF e)

/-- The residue of the stage. -/
noncomputable def stRes (Ls : Finset (Lab n K)) : Finset (Lab n K) :=
  (outs t I restF).image (fun e => Lab.cp t e (slen t I restF e) (sig t I restF e Ls))

/-- The used pieces. -/
noncomputable def stU (Ls : Finset (Lab n K)) : Finset (Finset (Lab n K)) :=
  Ls.image (P1 t) ∪ (I \ Ls).image (P0 t restF) ∪
    (outs t I restF).biUnion (fun e =>
      chU (Lab.cp t e) (Lab.cn t e) (item t I restF e) (iw t I restF e) (slen t I restF e)
        (spres t I restF e Ls))

/-! ### Basic facts -/

variable {t I restF}

lemma mem_rests {ℓ x : Lab n K} :
    x ∈ rests t restF ℓ ↔ ∃ k < (restF ℓ).length, x = .rest t ℓ k := by
  simp [rests, eq_comm]

lemma mem_restSet {x : Lab n K} :
    x ∈ restSet t I restF ↔ ∃ ℓ ∈ I, ∃ k < (restF ℓ).length, x = .rest t ℓ k := by
  simp only [restSet, mem_biUnion, mem_rests]

lemma mem_onPair {e : Finset (Fin n)} {x : Lab n K} :
    x ∈ onPair t I restF e ↔ x ∈ restSet t I restF ∧ restPair restF x = e := mem_filter

lemma item_mem {e : Finset (Fin n)} {k : ℕ} (hk : k ∈ Icc 1 (slen t I restF e)) :
    item t I restF e k ∈ onPair t I restF e := toList_getD_mem _ _ hk

lemma item_inj {e : Finset (Fin n)} {k k' : ℕ} (hk : k ∈ Icc 1 (slen t I restF e))
    (hk' : k' ∈ Icc 1 (slen t I restF e)) (h : item t I restF e k = item t I restF e k') :
    k = k' := toList_getD_inj _ _ hk hk' h

lemma item_surj {e : Finset (Fin n)} {x : Lab n K} (hx : x ∈ onPair t I restF e) :
    ∃ k ∈ Icc 1 (slen t I restF e), item t I restF e k = x := toList_getD_surj _ _ hx

/-- The present items of the chain on `e` are the rests on `e` of present inputs. -/
lemma present_items (e : Finset (Fin n)) (Ls : Finset (Lab n K)) :
    ((Icc 1 (slen t I restF e)).filter (spres t I restF e Ls)).image (item t I restF e) =
      (onPair t I restF e).filter (fun i => src i ∈ Ls) := by
  ext x
  simp only [mem_image, mem_filter, spres]
  constructor
  · rintro ⟨k, ⟨hk, hp⟩, rfl⟩
    exact ⟨item_mem hk, hp⟩
  · rintro ⟨hx, hp⟩
    obtain ⟨k, hk, rfl⟩ := item_surj hx
    exact ⟨k, ⟨hk, hp⟩, rfl⟩

lemma item_isRest {e : Finset (Fin n)} {k : ℕ} (hk : k ∈ Icc 1 (slen t I restF e)) :
    ∃ ℓ ∈ I, ∃ j < (restF ℓ).length, item t I restF e k = .rest t ℓ j :=
  mem_restSet.1 (mem_onPair.1 (item_mem hk)).1

/-- The chain decomposition on the pair `e`. -/
lemma stage_chain (e : Finset (Fin n)) (Ls : Finset (Lab n K)) :
    let U := chU (Lab.cp t e) (Lab.cn t e) (item t I restF e) (iw t I restF e)
      (slen t I restF e) (spres t I restF e Ls)
    U ⊆ chW (Lab.cp t e) (Lab.cn t e) (item t I restF e) (iw t I restF e) (slen t I restF e) ∧
      (U : Set (Finset (Lab n K))).PairwiseDisjoint id ∧
      Disjoint (U.sup id) {Lab.cp t e (slen t I restF e) (sig t I restF e Ls)} ∧
      U.sup id ∪ {Lab.cp t e (slen t I restF e) (sig t I restF e Ls)} =
        chR (Lab.cp t e) (Lab.cn t e) (slen t I restF e) ∪
          (onPair t I restF e).filter (fun i => src i ∈ Ls) := by
  intro U
  rw [← present_items]
  apply chain_decomp
  · intro k s k' s'; simp
  · intro k s k' s'; simp
  · intro k s k' s'; simp
  · intro k hk k' hk' h; exact item_inj hk hk' h
  · intro k hk k' s h
    obtain ⟨ℓ, -, j, -, hj⟩ := item_isRest hk
    rw [hj] at h; exact absurd h (by simp)
  · intro k hk k' s h
    obtain ⟨ℓ, -, j, -, hj⟩ := item_isRest hk
    rw [hj] at h; exact absurd h (by simp)

/-- Elements of used chain pieces. -/
lemma mem_of_chU {e : Finset (Fin n)} {Ls : Finset (Lab n K)} {P : Finset (Lab n K)}
    (hP : P ∈ chU (Lab.cp t e) (Lab.cn t e) (item t I restF e) (iw t I restF e)
      (slen t I restF e) (spres t I restF e Ls)) {x : Lab n K} (hx : x ∈ P) :
    x ∈ chR (Lab.cp t e) (Lab.cn t e) (slen t I restF e) ∨
      (x ∈ onPair t I restF e ∧ src x ∈ Ls) := by
  have h := (stage_chain (t := t) (I := I) (restF := restF) e Ls).2.2.2
  have hx' : x ∈ chR (Lab.cp t e) (Lab.cn t e) (slen t I restF e) ∪
      (onPair t I restF e).filter (fun i => src i ∈ Ls) := by
    rw [← h]
    exact mem_union_left _ (mem_sup.2 ⟨P, hP, hx⟩)
  rcases mem_union.1 hx' with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (mem_filter.1 h1)

lemma mem_chR {e : Finset (Fin n)} {m : ℕ} {x : Lab n K}
    (hx : x ∈ chR (Lab.cp t e) (Lab.cn t e) m) :
    (∃ k s, x = Lab.cp t e k s) ∨ (∃ k s, x = Lab.cn t e k s) := by
  simp only [chR, mem_union, mem_singleton, mem_image] at hx
  rcases hx with (rfl | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩
  · exact Or.inl ⟨0, 0, rfl⟩
  · exact Or.inl ⟨p.1, p.2, rfl⟩
  · exact Or.inr ⟨p.1, p.2, rfl⟩

lemma src_rest (t' : ℕ) (ℓ : Lab n K) (k : ℕ) : src (Lab.rest t' ℓ k) = ℓ := rfl

/-- **Stage decomposition.** -/
theorem stage_decomp (hI : ∀ ℓ ∈ I, NotStage t ℓ) (Ls : Finset (Lab n K)) (hLs : Ls ⊆ I) :
    stU t I restF Ls ⊆ stW t I restF ∧
      ((stU t I restF Ls : Set (Finset (Lab n K)))).PairwiseDisjoint id ∧
      Disjoint ((stU t I restF Ls).sup id) (stRes t I restF Ls) ∧
      (stU t I restF Ls).sup id ∪ stRes t I restF Ls = stR t I restF ∪ Ls := by
  -- labels of the input are not stage labels
  have hIa : ∀ ℓ ∈ I, ∀ ℓ', ℓ ≠ Lab.anti t ℓ' := by
    intro ℓ hℓ ℓ' h; have := hI ℓ hℓ; rw [h] at this; exact this rfl
  have hIr : ∀ ℓ ∈ I, ∀ ℓ' k, ℓ ≠ Lab.rest t ℓ' k := by
    intro ℓ hℓ ℓ' k h; have := hI ℓ hℓ; rw [h] at this; exact this rfl
  have hIp : ∀ ℓ ∈ I, ∀ e k s, ℓ ≠ Lab.cp t e k s := by
    intro ℓ hℓ e k s h; have := hI ℓ hℓ; rw [h] at this; exact this rfl
  have hIn : ∀ ℓ ∈ I, ∀ e k s, ℓ ≠ Lab.cn t e k s := by
    intro ℓ hℓ e k s h; have := hI ℓ hℓ; rw [h] at this; exact this rfl
  -- elements of the used pieces, by kind
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP
    simp only [stU, stW, mem_union, mem_image, mem_biUnion, mem_sdiff] at hP ⊢
    rcases hP with (⟨ℓ, hℓ, rfl⟩ | ⟨ℓ, hℓ, rfl⟩) | ⟨e, he, hP⟩
    · exact Or.inl (Or.inl ⟨ℓ, hLs hℓ, rfl⟩)
    · exact Or.inl (Or.inr ⟨ℓ, hℓ.1, rfl⟩)
    · exact Or.inr ⟨e, he, (stage_chain e Ls).1 hP⟩
  · intro P hP P' hP' hne
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro x hx hx'
    simp only [stU, coe_union, coe_image, coe_biUnion, Set.mem_union, Set.mem_image, mem_coe,
      Set.mem_iUnion, mem_sdiff, exists_prop] at hP hP'
    rcases hP with (⟨ℓ, hℓ, rfl⟩ | ⟨ℓ, hℓ, rfl⟩) | ⟨e, he, hP⟩ <;>
      rcases hP' with (⟨ℓ', hℓ', rfl⟩ | ⟨ℓ', hℓ', rfl⟩) | ⟨e', he', hP'⟩
    · -- P1 / P1
      apply hne
      simp only [P1, mem_insert, mem_singleton] at hx hx'
      rcases hx with rfl | rfl <;> rcases hx' with h | h
      · rw [h]
      · exact absurd h (hIa _ (hLs hℓ) _)
      · exact absurd h.symm (hIa _ (hLs hℓ') _)
      · simp only [Lab.anti.injEq, true_and] at h; rw [h]
    · -- P1 / P0
      simp only [P1, P0, mem_insert, mem_singleton, mem_rests] at hx hx'
      rcases hx with rfl | rfl <;> rcases hx' with h | ⟨k, -, h⟩
      · exact hIa _ (hLs hℓ) _ h
      · exact hIr _ (hLs hℓ) _ _ h
      · simp only [Lab.anti.injEq, true_and] at h; subst h; exact hℓ'.2 hℓ
      · exact absurd h (by simp)
    · -- P1 / chain
      simp only [P1, mem_insert, mem_singleton] at hx
      rcases mem_of_chU hP' hx' with h | ⟨h, -⟩
      · rcases mem_chR h with ⟨k, s, h'⟩ | ⟨k, s, h'⟩ <;> rcases hx with rfl | rfl
        · exact hIp _ (hLs hℓ) _ _ _ h'
        · exact absurd h' (by simp)
        · exact hIn _ (hLs hℓ) _ _ _ h'
        · exact absurd h' (by simp)
      · obtain ⟨ℓ₁, -, k, -, h'⟩ := mem_restSet.1 (mem_onPair.1 h).1
        rcases hx with rfl | rfl
        · exact hIr _ (hLs hℓ) _ _ h'
        · exact absurd h' (by simp)
    · -- P0 / P1
      simp only [P1, P0, mem_insert, mem_singleton, mem_rests] at hx' hx
      rcases hx' with rfl | rfl <;> rcases hx with h | ⟨k, -, h⟩
      · exact hIa _ (hLs hℓ') _ h
      · exact hIr _ (hLs hℓ') _ _ h
      · simp only [Lab.anti.injEq, true_and] at h; subst h; exact hℓ.2 hℓ'
      · exact absurd h (by simp)
    · -- P0 / P0
      apply hne
      simp only [P0, mem_insert, mem_rests] at hx hx'
      rcases hx with rfl | ⟨k, -, rfl⟩ <;> rcases hx' with h | ⟨k', -, h⟩
      · simp only [Lab.anti.injEq, true_and] at h; rw [h]
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · simp only [Lab.rest.injEq, true_and] at h; rw [h.1]
    · -- P0 / chain
      simp only [P0, mem_insert, mem_rests] at hx
      rcases mem_of_chU hP' hx' with h | ⟨h1, h⟩
      · rcases mem_chR h with ⟨k, s, h'⟩ | ⟨k, s, h'⟩ <;>
          rcases hx with rfl | ⟨j, -, rfl⟩ <;> exact absurd h' (by simp)
      · rcases hx with rfl | ⟨j, -, rfl⟩
        · obtain ⟨ℓ₁, -, k, -, h'⟩ := mem_restSet.1 (mem_onPair.1 h1).1
          exact absurd h' (by simp)
        · rw [src_rest] at h; exact hℓ.2 h
    · -- chain / P1
      simp only [P1, mem_insert, mem_singleton] at hx'
      rcases mem_of_chU hP hx with h | ⟨h, -⟩
      · rcases mem_chR h with ⟨k, s, h'⟩ | ⟨k, s, h'⟩ <;> rcases hx' with h'' | h'' <;>
          rw [h''] at h'
        · exact hIp _ (hLs hℓ') _ _ _ h'
        · exact absurd h' (by simp)
        · exact hIn _ (hLs hℓ') _ _ _ h'
        · exact absurd h' (by simp)
      · obtain ⟨ℓ₁, -, k, -, h'⟩ := mem_restSet.1 (mem_onPair.1 h).1
        rcases hx' with h'' | h'' <;> rw [h''] at h'
        · exact hIr _ (hLs hℓ') _ _ h'
        · exact absurd h' (by simp)
    · -- chain / P0
      simp only [P0, mem_insert, mem_rests] at hx'
      rcases mem_of_chU hP hx with h | ⟨h1, h⟩
      · rcases mem_chR h with ⟨k, s, h'⟩ | ⟨k, s, h'⟩ <;>
          rcases hx' with h'' | ⟨j, -, h''⟩ <;> rw [h''] at h' <;> exact absurd h' (by simp)
      · rcases hx' with h'' | ⟨j, -, h''⟩ <;> rw [h''] at h h1
        · obtain ⟨ℓ₁, -, k, -, h'⟩ := mem_restSet.1 (mem_onPair.1 h1).1
          exact absurd h' (by simp)
        · rw [src_rest] at h; exact hℓ'.2 h
    · -- chain / chain
      by_cases hee : e = e'
      · subst hee
        exact Finset.disjoint_left.1 ((stage_chain e Ls).2.1 hP hP' hne) hx hx'
      · rcases mem_of_chU hP hx with h | ⟨h, -⟩ <;> rcases mem_of_chU hP' hx' with h' | ⟨h', -⟩
        · rcases mem_chR h with ⟨k, s, rfl⟩ | ⟨k, s, rfl⟩ <;>
            rcases mem_chR h' with ⟨k', s', h''⟩ | ⟨k', s', h''⟩ <;>
            simp only [Lab.cp.injEq, Lab.cn.injEq, reduceCtorEq] at h'' <;> exact hee h''.2.1
        · obtain ⟨ℓ₁, -, k, -, h''⟩ := mem_restSet.1 (mem_onPair.1 h').1
          rcases mem_chR h with ⟨k', s', rfl⟩ | ⟨k', s', rfl⟩ <;> exact absurd h'' (by simp)
        · obtain ⟨ℓ₁, -, k, -, h''⟩ := mem_restSet.1 (mem_onPair.1 h).1
          rcases mem_chR h' with ⟨k', s', h3⟩ | ⟨k', s', h3⟩ <;> rw [h3] at h'' <;>
            exact absurd h'' (by simp)
        · exact hee ((mem_onPair.1 h).2.symm.trans (mem_onPair.1 h').2)
  · -- the residue avoids the used pieces
    rw [Finset.disjoint_sup_left]
    intro P hP
    rw [Finset.disjoint_right]
    intro x hx hxP
    simp only [stRes, mem_image] at hx
    obtain ⟨e, he, rfl⟩ := hx
    simp only [stU, mem_union, mem_image, mem_biUnion, mem_sdiff] at hP
    rcases hP with (⟨ℓ, hℓ, rfl⟩ | ⟨ℓ, hℓ, rfl⟩) | ⟨e', he', hP⟩
    · simp only [P1, id, mem_insert, mem_singleton] at hxP
      rcases hxP with h | h
      · exact hIp _ (hLs hℓ) _ _ _ h.symm
      · exact absurd h (by simp)
    · simp only [P0, id, mem_insert, mem_rests] at hxP
      rcases hxP with h | ⟨k, -, h⟩ <;> exact absurd h (by simp)
    · by_cases hee : e' = e
      · subst hee
        exact Finset.disjoint_left.1 (Finset.disjoint_sup_left.1 (stage_chain e' Ls).2.2.1 hP)
          hxP (mem_singleton_self _)
      · rcases mem_of_chU hP hxP with h | ⟨h, -⟩
        · rcases mem_chR h with ⟨k, s, h'⟩ | ⟨k, s, h'⟩
          · simp only [Lab.cp.injEq] at h'; exact hee h'.2.1.symm
          · exact absurd h' (by simp)
        · obtain ⟨ℓ₁, -, k, -, h'⟩ := mem_restSet.1 (mem_onPair.1 h).1
          exact absurd h' (by simp)
  · -- the union
    ext x
    have hch : ∀ e, x ∈ (chU (Lab.cp t e) (Lab.cn t e) (item t I restF e) (iw t I restF e)
        (slen t I restF e) (spres t I restF e Ls)).sup id ∨
          x = Lab.cp t e (slen t I restF e) (sig t I restF e Ls) ↔
        x ∈ chR (Lab.cp t e) (Lab.cn t e) (slen t I restF e) ∨
          (x ∈ onPair t I restF e ∧ src x ∈ Ls) := by
      intro e
      have h := congrArg (x ∈ ·) (stage_chain (t := t) (I := I) (restF := restF) e Ls).2.2.2
      simpa only [mem_union, mem_singleton, mem_filter, eq_iff_iff] using h
    simp only [stU, stRes, stR, mem_union, mem_sup, mem_image, mem_biUnion, mem_sdiff, id]
    constructor
    · rintro (⟨P, hP, hx⟩ | ⟨e, he, rfl⟩)
      · rcases hP with (⟨ℓ, hℓ, rfl⟩ | ⟨ℓ, hℓ, rfl⟩) | ⟨e, he, hP⟩
        · simp only [P1, mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Or.inr hℓ
          · exact Or.inl (Or.inl (Or.inl ⟨ℓ, hLs hℓ, rfl⟩))
        · simp only [P0, mem_insert] at hx
          rcases hx with rfl | hx
          · exact Or.inl (Or.inl (Or.inl ⟨ℓ, hℓ.1, rfl⟩))
          · exact Or.inl (Or.inl (Or.inr (mem_biUnion.2 ⟨ℓ, hℓ.1, hx⟩)))
        · rcases (hch e).1 (Or.inl (mem_sup.2 ⟨P, hP, hx⟩)) with h | ⟨h, -⟩
          · exact Or.inl (Or.inr ⟨e, he, h⟩)
          · exact Or.inl (Or.inl (Or.inr (mem_onPair.1 h).1))
      · rcases (hch e).1 (Or.inr rfl) with h | ⟨h, -⟩
        · exact Or.inl (Or.inr ⟨e, he, h⟩)
        · exact Or.inl (Or.inl (Or.inr (mem_onPair.1 h).1))
    · rintro (((⟨ℓ, hℓ, rfl⟩ | hx) | ⟨e, he, hx⟩) | hx)
      · by_cases hL : ℓ ∈ Ls
        · exact Or.inl ⟨P1 t ℓ, Or.inl (Or.inl ⟨ℓ, hL, rfl⟩), by simp [P1]⟩
        · exact Or.inl ⟨P0 t restF ℓ, Or.inl (Or.inr ⟨ℓ, ⟨hℓ, hL⟩, rfl⟩), by simp [P0]⟩
      · obtain ⟨ℓ, hℓ, k, hk, rfl⟩ := mem_restSet.1 hx
        by_cases hL : ℓ ∈ Ls
        · have hon : Lab.rest t ℓ k ∈ onPair t I restF (restPair restF (Lab.rest t ℓ k)) :=
            mem_onPair.2 ⟨hx, rfl⟩
          have he : restPair restF (Lab.rest t ℓ k) ∈ outs t I restF := mem_image_of_mem _ hx
          rcases (hch _).2 (Or.inr ⟨hon, hL⟩) with h | h
          · obtain ⟨P, hP, hxP⟩ := mem_sup.1 h
            exact Or.inl ⟨P, Or.inr ⟨_, he, hP⟩, hxP⟩
          · exact Or.inr ⟨_, he, h.symm⟩
        · refine Or.inl ⟨P0 t restF ℓ, Or.inl (Or.inr ⟨ℓ, ⟨hℓ, hL⟩, rfl⟩), ?_⟩
          simp only [P0, mem_insert, mem_rests]
          exact Or.inr ⟨k, hk, rfl⟩
      · rcases (hch e).2 (Or.inl hx) with h | h
        · obtain ⟨P, hP, hxP⟩ := mem_sup.1 h
          exact Or.inl ⟨P, Or.inr ⟨e, he, hP⟩, hxP⟩
        · exact Or.inr ⟨e, he, h.symm⟩
      · exact Or.inl ⟨P1 t x, Or.inl (Or.inl ⟨x, hx, rfl⟩), by simp [P1]⟩

end RefinedAbsorption.OddGrid
