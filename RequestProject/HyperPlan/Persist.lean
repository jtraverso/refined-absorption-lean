module
public import RequestProject.HyperPlan.Mono

/-!
# Faces persist along valid plans

A structural constraint on every valid plan, for every uniformity `r < q`:

* `route_covers_face`: a valid route of `e` for a set of weights containing `1` covers every face
  `S ⊆ e` with `|S| < r` (some set of the route contains `S`);
* `face_persists_zero`: hence every face of size `< r` of an input set is still a face of a set
  present after the first stage;
* `face_persists`: the same at every later stage, for sets whose allowed weights contain `1`
  (for instance sets without lone faces, `one_mem_allowedR_of_noLone`).

So a face of an input set can only disappear through a route on a set in which some face is lone.
This is the formal reason why a plan with small loads must first make faces lone (collapse their
links) before it can remove them.
-/

@[expose] public section

namespace RefinedAbsorption.HyperPlan

open Finset

variable {n K : ℕ} {q r : ℕ}

lemma lfcl_eq_zero_of_not_covered {ro : List (Finset (Fin n) × ZMod K)} {S : Finset (Fin n)}
    (h : ∀ p ∈ ro, ¬ S ⊆ p.1) : lfcl ro S = 0 := by
  unfold lfcl
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  simp [h p hp]

lemma two_le_choose_of_lt {q r i : ℕ} (hi : i < r) (hrq : r < q) : 2 ≤ (q - i).choose (r - i) := by
  obtain ⟨a, ha⟩ : ∃ a, q - i = a + 1 := ⟨q - i - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, r - i = b + 1 := ⟨r - i - 1, by omega⟩
  rw [ha, hb, Nat.choose_succ_succ, Nat.succ_eq_add_one]
  have h1 := Nat.choose_pos (show b ≤ a by omega)
  have h2 := Nat.choose_pos (show b + 1 ≤ a by omega)
  omega

/-- **A valid route covers every face.** If `1` is an allowed weight, every face `S ⊆ e` with
`|S| < r` lies in some set of the route. -/
theorem route_covers_face [NeZero K] (hK : ModsOK q r K) (hrq : r < q) {e S : Finset (Fin n)}
    {ro : List (Finset (Fin n) × ZMod K)} {A : Finset (ZMod K)} (hro : RouteOKR q r e ro A)
    (h1 : (1 : ZMod K) ∈ A) (hS : S ⊆ e) (hSr : S.card < r) : ∃ p ∈ ro, S ⊆ p.1 := by
  by_contra hcon
  push_neg at hcon
  have hdvd := hro.2 1 h1 S hSr
  rw [defect, lfcl_eq_zero_of_not_covered hcon, if_pos hS, mul_one, zero_sub] at hdvd
  set b := (q - S.card).choose (r - S.card) with hb
  have hb2 : 2 ≤ b := two_le_choose_of_lt hSr hrq
  have hbK : b ∣ K := hK _ hSr
  have hK1 : 1 < K := lt_of_lt_of_le (by omega) (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne K)) hbK)
  haveI : Fact (1 < K) := ⟨hK1⟩
  have hval : ((-1 : ZMod K)).val = K - 1 := by
    rw [ZMod.val_neg_of_ne_zero, ZMod.val_one]
  rw [hval] at hdvd
  have h3 : b ∣ K - (K - 1) := Nat.dvd_sub hbK hdvd
  rw [show K - (K - 1) = 1 by omega] at h3
  have := Nat.le_of_dvd one_pos h3
  omega

/-- Without lone faces, every weight (in particular `1`) is allowed. -/
lemma one_mem_allowedR_of_noLone [NeZero K] {P : Finset (Finset (Fin n))} {e : Finset (Fin n)}
    (h : ∀ S ⊆ e, S.card < r → ¬ LoneIn P e S) : (1 : ZMod K) ∈ allowedR q r P e := by
  simp only [allowedR, mem_filter, mem_univ, true_and, mem_powerset]
  intro S hS hSr hl
  exact absurd hl (h S hS hSr)

/-- **Faces persist** at a stage `t` of a valid plan, for a set `e` on which the weight `1` can
occur. -/
theorem face_persists [NeZero K] (hK : ModsOK q r K) (hrq : r < q) {L : ℕ} {sp : List (SpecR n K)}
    {X : Finset (Finset (Fin n))} (hok : PlanOKR q r L sp X) {t : ℕ} (ht : t < sp.length)
    {e S : Finset (Fin n)} (he : e ∈ prunR sp X t) (h1 : (1 : ZMod K) ∈ wts q r sp X t e)
    (hS : S ⊆ e) (hSr : S.card < r) : ∃ f ∈ prunR sp X (t + 1), S ⊆ f := by
  obtain ⟨p, hp, hSp⟩ := route_covers_face hK hrq (hok.route t ht e he) h1 hS hSr
  refine ⟨p.1, ?_, hSp⟩
  rw [prunR_succ]
  exact mem_biUnion.2 ⟨e, he, List.mem_toFinset.2 (List.mem_map_of_mem hp)⟩

/-- **Faces of the input persist** through the first stage of a valid plan. -/
theorem face_persists_zero [NeZero K] (hK : ModsOK q r K) (hrq : r < q) {L : ℕ} {sp : List (SpecR n K)}
    {X : Finset (Finset (Fin n))} (hok : PlanOKR q r L sp X) (hT : 1 ≤ sp.length)
    {e S : Finset (Fin n)} (he : e ∈ X) (hS : S ⊆ e) (hSr : S.card < r) :
    ∃ f ∈ prunR sp X 1, S ⊆ f :=
  face_persists hK hrq hok hT he (by simp [wts]) hS hSr

end RefinedAbsorption.HyperPlan
