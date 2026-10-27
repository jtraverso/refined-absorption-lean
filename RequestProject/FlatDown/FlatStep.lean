module
public import RequestProject.FlatDown.Completion

/-!
# The step from `i`-flat to `(i-1)`-flat

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855 (Refine Down, induction on
uniformity).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

Let `Y` be `i`-flat with respect to the reserve `Z` (`1 ≤ i < r`).  For an `i`-set `T` outside `Z`,
the *link* of `T` is the `(r-i)`-multigraph `{x ∩ Z : x ∈ Y, x \ Z = T}` on `Z`.

* `link_divisible`: the link of a `K_q^r`-divisible `L ⊆ Y` is `K_{q-i}^{r-i}`-divisible.
* Given, for every outside part `T`, a `K_{q-i}^{r-i}`-multi-refiner of the link of `T` inside `Z`
  (lower uniformity), every piece `W` of it is lifted to `T * W` and completed (via a local
  integral decomposition `gjw_local`) by edges that contain fewer than `i` vertices outside `Z`.
  The paired step then gives `flatStep`: a residual refiner of `Y` whose residue is
  `(i-1)`-flat.  Its constant depends only on `q`, `r` and the constant of the link refiners.
-/

@[expose] public section

namespace RefinedAbsorption.FlatDown

open Finset RefinedAbsorption.MultiRefiner

variable {V E N : Type} [DecidableEq V] [DecidableEq E] [DecidableEq N]

/-- Labels of the completion copies: `(T, W, k, Q, j, e)`. -/
abbrev CLab (V E N : Type) := Finset V × Finset (E ⊕ N) × ℕ × Finset V × ℕ × Finset V

/-- Labels of the new copies of a flat step: lifted link copies `(T, y)` and completion copies. -/
abbrev FLab (V E N : Type) := (Finset V × N) ⊕ CLab V E N

instance instDecEqCLab : DecidableEq (CLab V E N) :=
  have : DecidableEq (Finset (E ⊕ N) × ℕ × Finset V × ℕ × Finset V) := inferInstance
  inferInstanceAs (DecidableEq (Finset V × Finset (E ⊕ N) × ℕ × Finset V × ℕ × Finset V))

instance instDecEqFLab : DecidableEq (FLab V E N) :=
  inferInstanceAs (DecidableEq ((Finset V × N) ⊕ CLab V E N))

section Defs

variable (ends : E → Finset V) (Z : Finset V) (endsN : Finset V → N → Finset V)

/-- The link ends: the part inside the reserve. -/
def lk (x : E) : Finset V := ends x ∩ Z

/-- The link ends for the outside part `T`. -/
def lE (T : Finset V) : E ⊕ N → Finset V := Sum.elim (lk ends Z) (endsN T)

/-- The link of `T`: the copies of `Y` whose outside part is `T`. -/
def lnk (Y : Finset E) (T : Finset V) : Finset E := Y.filter fun x => ends x \ Z = T

/-- The outside parts of size `i`. -/
def outParts (i : ℕ) (Y : Finset E) : Finset (Finset V) :=
  (Y.filter fun x => (ends x \ Z).card = i).image fun x => ends x \ Z

/-- The ends of the flat step. -/
def fEnds : E ⊕ FLab V E N → Finset V :=
  Sum.elim ends (Sum.elim (fun p => p.1 ∪ endsN p.1 p.2) fun l => l.2.2.2.2.2)

/-- Lifting the link copies of `T`. -/
def liftT (T : Finset V) : E ⊕ N → E ⊕ FLab V E N :=
  Sum.elim Sum.inl fun y => Sum.inr (Sum.inl (T, y))

/-- The support of the integral decomposition of the piece `W`. -/
def AW (Z₀ : Finset V) (T : Finset V) (W : Finset (E ⊕ N)) : Finset V :=
  Z₀ ∪ W.biUnion (lE ends Z endsN T)

/-- The decomposition identity. -/
def GJWId (q r i : ℕ) (Z₀ : Finset V) (T : Finset V) (W : Finset (E ⊕ N)) (c : Finset V → ℤ) :
    Prop :=
  ∀ g : Finset V, ((W.filter fun w => lE ends Z endsN T w = g).card : ℤ) =
    ∑ Q ∈ (AW ends Z endsN Z₀ T W).powersetCard (q - i),
      c Q * (if g.card = r - i ∧ g ⊆ Q then 1 else 0)

open Classical in
/-- A choice of integral decomposition (zero if none exists). -/
noncomputable def cf (q r i : ℕ) (Z₀ : Finset V) (T : Finset V) (W : Finset (E ⊕ N)) :
    Finset V → ℤ :=
  if h : ∃ c, GJWId ends Z endsN q r i Z₀ T W c then Classical.choose h else 0

/-- The `k`-th copy of the completion of the lifted piece `T * W`. -/
noncomputable def compLab (q r i M : ℕ) (Z₀ : Finset V) (T : Finset V) (W : Finset (E ⊕ N))
    (k : ℕ) : Finset (E ⊕ FLab V E N) :=
  ((AW ends Z endsN Z₀ T W).powersetCard (q - i)).biUnion fun Q =>
    (range (resMod M (cf ends Z endsN q r i Z₀ T W Q))).biUnion fun j =>
      (compE r T Q).image fun e => Sum.inr (Sum.inr (T, W, k, Q, j, e))

end Defs

variable {ends : E → Finset V} {Z : Finset V} {endsN : Finset V → N → Finset V}

theorem mem_compLab {q r i M : ℕ} {Z₀ T : Finset V} {W : Finset (E ⊕ N)} {k : ℕ}
    {c : E ⊕ FLab V E N} : c ∈ compLab ends Z endsN q r i M Z₀ T W k ↔
      ∃ Q ∈ (AW ends Z endsN Z₀ T W).powersetCard (q - i),
        ∃ j < resMod M (cf ends Z endsN q r i Z₀ T W Q), ∃ e ∈ compE r T Q,
          c = Sum.inr (Sum.inr (T, W, k, Q, j, e)) := by
  simp only [compLab, mem_biUnion, mem_range, mem_image]
  constructor
  · rintro ⟨Q, hQ, j, hj, e, he, rfl⟩; exact ⟨Q, hQ, j, hj, e, he, rfl⟩
  · rintro ⟨Q, hQ, j, hj, e, he, rfl⟩; exact ⟨Q, hQ, j, hj, e, he, rfl⟩

theorem compLab_tag {q r i M : ℕ} {Z₀ T : Finset V} {W : Finset (E ⊕ N)} {k : ℕ}
    {c : E ⊕ FLab V E N} (hc : c ∈ compLab ends Z endsN q r i M Z₀ T W k) :
    ∃ l : CLab V E N, c = Sum.inr (Sum.inr l) ∧ l.1 = T ∧ l.2.1 = W ∧ l.2.2.1 = k ∧
      l.2.2.2.2.2 ∈ compE r T l.2.2.2.1 := by
  obtain ⟨Q, -, j, -, e, he, rfl⟩ := mem_compLab.1 hc
  exact ⟨_, rfl, rfl, rfl, rfl, he⟩

theorem fEnds_liftT_inr (T : Finset V) (y : N) :
    fEnds ends endsN (liftT T (Sum.inr y) : E ⊕ FLab V E N) = T ∪ endsN T y := rfl

theorem liftT_injective (T : Finset V) : Function.Injective (liftT (E := E) (N := N) T) := by
  intro a b h
  rcases a with x | y <;> rcases b with x' | y' <;> simp_all [liftT]

theorem mdeg_compLab {q r i M : ℕ} {Z₀ T : Finset V} {W : Finset (E ⊕ N)} {k : ℕ}
    (S : Finset V) : mdeg (fEnds ends endsN) (compLab ends Z endsN q r i M Z₀ T W k) S =
      ∑ Q ∈ (AW ends Z endsN Z₀ T W).powersetCard (q - i),
        resMod M (cf ends Z endsN q r i Z₀ T W Q) * ((compE r T Q).filter fun e => S ⊆ e).card := by
  unfold mdeg compLab
  rw [filter_biUnion, card_biUnion]
  · refine sum_congr rfl fun Q _ => ?_
    rw [filter_biUnion, card_biUnion]
    · rw [sum_congr rfl fun j _ => ?_, sum_const, card_range, smul_eq_mul]
      rw [filter_image, card_image_of_injective _ (fun e e' h => by simpa using h)]
      rfl
    · intro j _ j' _ hne
      refine disjoint_filter_filter ?_
      rw [disjoint_left]
      intro c hc hc'
      obtain ⟨e, -, rfl⟩ := mem_image.1 hc
      obtain ⟨e', -, h⟩ := mem_image.1 hc'
      simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      exact hne h.2.2.2.2.1.symm
  · intro Q _ Q' _ hne
    refine disjoint_filter_filter ?_
    rw [disjoint_left]
    intro c hc hc'
    simp only [mem_biUnion, mem_image] at hc hc'
    obtain ⟨j, -, e, -, rfl⟩ := hc
    obtain ⟨j', -, e', -, h⟩ := hc'
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact hne h.2.2.2.1.symm

theorem card_compLab_le {q r i M : ℕ} {Z₀ T : Finset V} {W : Finset (E ⊕ N)} {k : ℕ}
    (hM : 0 < M) (hTQ : ∀ Q ∈ (AW ends Z endsN Z₀ T W).powersetCard (q - i), (T ∪ Q).card ≤ q) :
    (compLab ends Z endsN q r i M Z₀ T W k).card ≤
      2 ^ (AW ends Z endsN Z₀ T W).card * M * 2 ^ q := by
  calc (compLab ends Z endsN q r i M Z₀ T W k).card
      ≤ ∑ Q ∈ (AW ends Z endsN Z₀ T W).powersetCard (q - i),
          ∑ j ∈ range (resMod M (cf ends Z endsN q r i Z₀ T W Q)), (compE r T Q).card := by
        unfold compLab
        refine card_biUnion_le.trans (sum_le_sum fun Q _ => card_biUnion_le.trans
          (sum_le_sum fun j _ => card_image_le))
    _ ≤ ∑ _Q ∈ (AW ends Z endsN Z₀ T W).powersetCard (q - i), M * 2 ^ q := by
        refine sum_le_sum fun Q hQ => ?_
        rw [sum_const, card_range, smul_eq_mul]
        have h1 : resMod M (cf ends Z endsN q r i Z₀ T W Q) ≤ M := by
          have h0 : 0 ≤ cf ends Z endsN q r i Z₀ T W Q % (M : ℤ) :=
            Int.emod_nonneg _ (by exact_mod_cast hM.ne')
          have h2 : cf ends Z endsN q r i Z₀ T W Q % (M : ℤ) < M :=
            Int.emod_lt_of_pos _ (by exact_mod_cast hM)
          unfold resMod; omega
        have h2 : (compE r T Q).card ≤ 2 ^ q := by
          refine (card_filter_le _ _).trans ?_
          rw [card_powersetCard]
          exact (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (hTQ Q hQ))
        exact Nat.mul_le_mul h1 h2
    _ = ((AW ends Z endsN Z₀ T W).powersetCard (q - i)).card * (M * 2 ^ q) := by
        rw [sum_const, smul_eq_mul]
    _ ≤ 2 ^ (AW ends Z endsN Z₀ T W).card * (M * 2 ^ q) := by
        gcongr
        rw [card_powersetCard]; exact Nat.choose_le_two_pow _ _
    _ = _ := by ring

/-! ### Divisibility of links -/

omit [DecidableEq E] in
/-- Degrees in the link of `T` are degrees of `T ∪ S` in `L`. -/
theorem mdeg_lnk {i : ℕ} {L : Finset E} (hflat : IsFlat i Z ends L) {T : Finset V}
    (hT : T.card = i) (hTZ : Disjoint T Z) {S : Finset V} (hSZ : S ⊆ Z) :
    mdeg (lk ends Z) (lnk ends Z L T) S = mdeg ends L (T ∪ S) := by
  unfold mdeg lnk lk
  rw [filter_filter]
  congr 1
  refine filter_congr fun x hx => ?_
  constructor
  · rintro ⟨h1, h2⟩
    refine union_subset ?_ (h2.trans inter_subset_left)
    rw [← h1]; exact sdiff_subset
  · intro h
    have hT' : T ⊆ ends x \ Z := fun v hv =>
      mem_sdiff.2 ⟨h (mem_union_left _ hv), disjoint_left.1 hTZ hv⟩
    have hEq : ends x \ Z = T :=
      (eq_of_subset_of_card_le hT' (by rw [hT]; exact hflat x hx)).symm
    exact ⟨hEq, subset_inter (fun v hv => h (mem_union_right _ hv)) hSZ⟩

omit [DecidableEq E] in
/-- **Links of divisible flat multigraphs are divisible** (lower uniformity). -/
theorem link_divisible {q r i : ℕ} {L : Finset E} (hflat : IsFlat i Z ends L) {T : Finset V}
    (hT : T.card = i) (hTZ : Disjoint T Z) (hL : MIsDivisible q r ends L) :
    MIsDivisible (q - i) (r - i) (lk ends Z) (lnk ends Z L T) := by
  intro S hS
  by_cases hSZ : S ⊆ Z
  · rw [mdeg_lnk hflat hT hTZ hSZ]
    have hdisj : Disjoint T S := disjoint_of_subset_right hSZ hTZ
    have hc : (T ∪ S).card = i + S.card := by rw [card_union_of_disjoint hdisj, hT]
    have := hL (T ∪ S) (by omega)
    rw [hc] at this
    have e1 : q - (i + S.card) = q - i - S.card := by omega
    have e2 : r - (i + S.card) = r - i - S.card := by omega
    rwa [e1, e2] at this
  · have : mdeg (lk ends Z) (lnk ends Z L T) S = 0 := by
      unfold mdeg
      rw [card_eq_zero, filter_eq_empty_iff]
      intro x _ hx
      exact hSZ (hx.trans inter_subset_right)
    rw [this]; exact dvd_zero _

end RefinedAbsorption.FlatDown
