module
public import RefinedAbsorption.HyperPlan.Segment

/-!
# Local plans restrict to subfamilies

A stage specification is *local* (`LocalSpec`) if the route of a set does not depend on the
current family.  A list of local specifications can be designed once for a whole *structure*
(a large family of `r`-sets) and then applied to any subfamily of it:

* `prunR_mono_local`: the sets present at every stage only shrink when the input shrinks;
* `rtR_local`: the routes do not depend on the input;
* `allowedR_anti`: a smaller family has more lone faces, hence fewer allowed values;
* `SegOKR.mono_local`, `PlanOKR.mono_local`: validity passes to subfamilies;
* `passR_mono_local`, `passSumR_mono_local`: loads only decrease;
* `card_prunR_mono_local`: the final family only shrinks.

So a valid local plan on a structure, with good loads and a bounded final family, is a valid plan
with the same bounds for every subfamily of the structure.
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset

variable {n K : ℕ}

/-- A specification whose routes do not depend on the current family. -/
def LocalSpec (s : SpecR n K) : Prop := ∀ P Q : Finset (Finset (Fin n)), ∀ e, s P e = s Q e

/-- All specifications of a list are local. -/
def LocalList (l : List (SpecR n K)) : Prop := ∀ s ∈ l, LocalSpec s

lemma localSpec_idSpecR : LocalSpec (idSpecR (n := n) (K := K)) := fun _ _ _ => rfl

lemma LocalList.getD {l : List (SpecR n K)} (h : LocalList l) (t : ℕ) :
    LocalSpec (l.getD t idSpecR) := by
  rw [List.getD_eq_getElem?_getD]
  cases hl : l[t]? with
  | none => exact localSpec_idSpecR
  | some s => exact h s (List.mem_of_getElem? hl)

lemma LocalList.nil : LocalList ([] : List (SpecR n K)) := fun _ h => by simp at h

lemma LocalList.append {l₁ l₂ : List (SpecR n K)} (h₁ : LocalList l₁) (h₂ : LocalList l₂) :
    LocalList (l₁ ++ l₂) := fun s hs => by
  rcases List.mem_append.1 hs with h | h
  · exact h₁ s h
  · exact h₂ s h

variable [NeZero K] {l : List (SpecR n K)} {X Y : Finset (Finset (Fin n))}

/-- **Routes of a local list do not depend on the input.** -/
lemma rtR_local (hl : LocalList l) (X Y : Finset (Finset (Fin n))) (t : ℕ) (e : Finset (Fin n)) :
    rtR l Y t e = rtR l X t e :=
  hl.getD t _ _ e

/-- **The sets of a local list only shrink when the input shrinks.** -/
lemma prunR_mono_local (hl : LocalList l) (hXY : Y ⊆ X) (t : ℕ) :
    prunR l Y t ⊆ prunR l X t := by
  induction t with
  | zero => exact hXY
  | succ t ih =>
    rw [prunR_succ, prunR_succ]
    intro f hf
    obtain ⟨e, he, hfe⟩ := mem_biUnion.1 hf
    refine mem_biUnion.2 ⟨e, ih he, ?_⟩
    rwa [rtR_local hl X Y t e] at hfe

/-- A smaller family has fewer allowed values. -/
lemma allowedR_anti {q r : ℕ} {P P' : Finset (Finset (Fin n))} (h : P' ⊆ P)
    (e : Finset (Fin n)) : allowedR (K := K) q r P' e ⊆ allowedR q r P e := by
  intro s hs
  simp only [allowedR, mem_filter, mem_univ, true_and] at hs ⊢
  intro S hS hc hlone
  exact hs S hS hc fun f hf hSf => hlone f (h hf) hSf

/-- Validity of a route is preserved when the set of weights shrinks. -/
lemma RouteOKR.mono_wts {q r : ℕ} {e : Finset (Fin n)} {ro : List (Finset (Fin n) × ZMod K)}
    {A B : Finset (ZMod K)} (h : RouteOKR q r e ro A) (hBA : B ⊆ A) : RouteOKR q r e ro B :=
  ⟨h.1, fun s hs => h.2 s (hBA hs)⟩

variable {q r L : ℕ}

/-- **Validity of a local segment passes to subfamilies.** -/
theorem SegOKR.mono_local (h : SegOKR q r L l X) (hl : LocalList l) (hXY : Y ⊆ X) :
    SegOKR q r L l Y := by
  refine ⟨fun e he => h.rg e (hXY he), ?_, ?_⟩
  · intro t ht e he
    have he' := prunR_mono_local hl hXY t he
    rw [rtR_local hl X Y t e]
    exact (h.route t ht e he').mono_wts (allowedR_anti (prunR_mono_local hl hXY t) e)
  · intro t ht e he
    rw [rtR_local hl X Y t e]
    exact h.len t ht e (prunR_mono_local hl hXY t he)

/-- **Validity of a local plan passes to subfamilies.** -/
theorem PlanOKR.mono_local (h : PlanOKR q r L l X) (hl : LocalList l) (hXY : Y ⊆ X) :
    PlanOKR q r L l Y := by
  refine ⟨fun e he => h.rg e (hXY he), ?_, ?_⟩
  · intro t ht e he
    have he' := prunR_mono_local hl hXY t he
    rw [rtR_local hl X Y t e]
    refine (h.route t ht e he').mono_wts ?_
    unfold wts
    split_ifs
    · exact subset_refl _
    · exact allowedR_anti (prunR_mono_local hl hXY t) e
  · intro t ht e he
    rw [rtR_local hl X Y t e]
    exact h.len t ht e (prunR_mono_local hl hXY t he)

/-- **Loads of a local list only decrease on subfamilies.** -/
lemma passR_mono_local (hl : LocalList l) (hXY : Y ⊆ X) (t : ℕ) (S : Finset (Fin n)) :
    passR l Y t S ≤ passR l X t S := by
  unfold passR
  refine card_le_card fun e he => ?_
  rw [mem_filter] at he ⊢
  rw [rtR_local hl X Y t e] at he
  exact ⟨prunR_mono_local hl hXY t he.1, he.2⟩

lemma passSumR_mono_local (hl : LocalList l) (hXY : Y ⊆ X) (S : Finset (Fin n)) :
    passSumR l Y S ≤ passSumR l X S :=
  sum_le_sum fun t _ => passR_mono_local hl hXY t S

/-- The final family of a local list only shrinks on subfamilies. -/
lemma card_prunR_mono_local (hl : LocalList l) (hXY : Y ⊆ X) (t : ℕ) :
    (prunR l Y t).card ≤ (prunR l X t).card :=
  card_le_card (prunR_mono_local hl hXY t)

end RefinedAbsorption.HyperPlan
