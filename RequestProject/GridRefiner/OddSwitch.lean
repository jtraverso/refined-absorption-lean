module
public import RequestProject.GridRefiner.Parity

/-!
# One switch stage with partner tokens (`r = 2`)

Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

For odd `q` there is no local unit token (`no_local_unit_token`), so the switch of an edge
`e = uv` uses *partner tokens* (`partnerTok_deg`): the token at `u` is `tok t (x e) u`, with
helper `hw t u` and partner `π u = pi t u`, and has degree class `1_u - 1_{π u}` modulo `q - 1`
(`tok_cls`).  The switch pieces of `e` are

* `swP1 e = {x e, anti e}` (`q (q - 1)` copies of `e`), used when `e` is selected;
* `swP0 e = {anti e} ∪ swRest e`, used when `e` is not selected, where the *rest*
  `swRest e = {tok u, tok v, path t (x e) 0}` consists of the two partner tokens and the
  *remainder*: a single copy of the edge `π u π v` (`remainder_lift`).

Results (nothing here assumes `NativeStrongMultiRefiners`; the target budget is not touched):

* `swP0_divisible`, `swP1_divisible`: the pieces are divisible.
* `switch_decomp`: for selected edges `L ⊆ X` the residue is exactly `swRes L`, the union of the
  rests of the edges of `L`.
* **`switch_residual`**: via `lift_residual`, the stage is an `IsResidualMultiRefiner` with
  constant `3 q (q - 1)`.
* **`swRest_classes`, `swRes_classes`**: the rest of `e` has the degree classes of `e` and
  `2 q (q - 1) + 1 ≡ 1 (mod binom(q, 2))` copies; the residue of `L` has degree `≡ deg_L`.
* **`switch_load`, `switch_load_inj`**: loads; for injective partner and helper maps the load is
  at most `9 q (q - 1) D`, i.e. `O(D)`.
* **`switch_needs_remainder`** (`q ≥ 3`): the remainder cannot be dropped.
* **`oddSwitch_stage`**: all of this for the concrete shift plan, for every graph on `Fin n`.

What is *not* proved here is the global closure: absorbing the tokens (per-vertex chains) and
the remainder graph `π(L)`, which still has `|L|` edges.
-/

@[expose] public section

namespace RefinedAbsorption.GridRefiner

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.LocalRefiner

variable {n : ℕ} (P : Plan n) (t : ℕ)

/-- The piece used when the edge `e` is selected: `q(q-1)` copies of `e`. -/
def swP1 (e : Finset (Fin n)) : Finset (GLab n) := {.x e, .anti t (.x e)}

/-- The *rest* of the switch of `e`: the partner tokens at the ends of `e` and the remainder
label `path t (x e) 0`, a single copy of the image of `e` under the partner map. -/
def swRest (e : Finset (Fin n)) : Finset (GLab n) :=
  insert (.path t (.x e) 0) (e.image (.tok t (.x e)))

/-- The piece used when the edge `e` is not selected. -/
def swP0 (e : Finset (Fin n)) : Finset (GLab n) := insert (.anti t (.x e)) (swRest t e)

/-- Inputs: one label per edge of `X`. -/
def swI (X : Finset (Finset (Fin n))) : Finset (GLab n) := X.image .x

/-- Reservoir. -/
def swR (X : Finset (Finset (Fin n))) : Finset (GLab n) := X.biUnion (swP0 t)

/-- Allowed residue. -/
def swY (X : Finset (Finset (Fin n))) : Finset (GLab n) := X.biUnion (swRest t)

/-- Pieces. -/
def swW (X : Finset (Finset (Fin n))) : Finset (Finset (GLab n)) :=
  X.image (swP1 t) ∪ X.image (swP0 t)

/-- Hypotheses on the plan of the stage `t` for the graph `X`. -/
structure SwitchHyp (X : Finset (Finset (Fin n))) : Prop where
  card_two : ∀ e ∈ X, e.card = 2
  ne_hw : ∀ u, u ≠ P.hw t u
  ne_pi : ∀ u, u ≠ P.pi t u
  hw_ne_pi : ∀ u, P.hw t u ≠ P.pi t u
  pi_inj : ∀ e ∈ X, ∀ u ∈ e, ∀ v ∈ e, P.pi t u = P.pi t v → u = v
  shape : ∀ e ∈ X, P.shape t e = [e.image (P.pi t)]

variable {P t}

/-! ### Degrees of the labels -/

lemma wdeg_x (q : ℕ) (e S : Finset (Fin n)) :
    wdeg (sg P q) (.x e) S = if S ⊆ e then 1 else 0 := by
  rw [wdeg_list]; simp [sg]

lemma wdeg_anti (q : ℕ) (e S : Finset (Fin n)) :
    wdeg (sg P q) (.anti t (.x e)) S = if S ⊆ e then q * (q - 1) - 1 else 0 := by
  rw [wdeg_list]; simp [sg, pe]

lemma wdeg_path (q : ℕ) {e : Finset (Fin n)} (he : P.shape t e = [e.image (P.pi t)])
    (S : Finset (Fin n)) :
    wdeg (sg P q) (.path t (.x e) 0) S = if S ⊆ e.image (P.pi t) then 1 else 0 := by
  rw [wdeg_list]; simp [sg, pe, he]

/-- The token labels are the partner tokens of `Parity.lean`. -/
lemma wdeg_tok (q : ℕ) (ℓ : GLab n) (u : Fin n) (S : Finset (Fin n)) :
    wdeg (sg P q) (.tok t ℓ u) S = wdeg (partnerTokSg q u (P.hw t u) (P.pi t u)) () S := rfl

lemma wdeg_tok_empty {q : ℕ} (hq : 2 ≤ q) (ℓ : GLab n) (u : Fin n) :
    wdeg (sg P q) (.tok t ℓ u) ∅ = q * (q - 1) := by
  rw [wdeg_tok, wdeg_list]
  simp only [partnerTokSg, empty_subset, if_true, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  obtain ⟨d, rfl⟩ : ∃ d, q = d + 2 := ⟨q - 2, by omega⟩
  simp only [Nat.add_sub_cancel, show d + 2 - 1 = d + 1 by omega]
  ring

/-- **Class of a partner token** (built with `partnerTok_deg`): `1_u - 1_{π u}` modulo `q - 1`. -/
lemma tok_cls {q : ℕ} (hq : 2 ≤ q) (ℓ : GLab n) (u x : Fin n) (h1 : u ≠ P.hw t u)
    (h2 : u ≠ P.pi t u) (h3 : P.hw t u ≠ P.pi t u) :
    ((wdeg (sg P q) (.tok t ℓ u) {x} : ℕ) : ZMod (q - 1)) =
      (if x = u then 1 else 0) - (if x = P.pi t u then 1 else 0) := by
  obtain ⟨-, hu, hp, ho⟩ := partnerTok_deg hq h1 h2 h3
  have hw : ∀ y, mdeg (cpEnds (partnerTokSg q u (P.hw t u) (P.pi t u)))
      (liftS (partnerTokSg q u (P.hw t u) (P.pi t u)) {()}) {y} =
      wdeg (sg P q) (.tok t ℓ u) {y} := fun y => by
    rw [mdeg_liftS, sum_singleton, wdeg_tok]
  rw [← hw]
  by_cases hxu : x = u
  · subst hxu; rw [hu]; simp [h2]
  · by_cases hxp : x = P.pi t u
    · subst hxp; rw [hp]; simp [hxu]
    · rw [ho x hxu hxp]; simp [hxu, hxp]


lemma cast_anti {q : ℕ} (hq : 2 ≤ q) : ((q * (q - 1) - 1 : ℕ) : ZMod (q - 1)) = -1 := by
  obtain ⟨d, rfl⟩ : ∃ d, q = d + 2 := ⟨q - 2, by omega⟩
  have h1 : d + 2 - 1 = d + 1 := by omega
  rw [h1, Nat.cast_sub (by nlinarith)]
  have hz : ((d + 1 : ℕ) : ZMod (d + 1)) = 0 := ZMod.natCast_self _
  push_cast at hz ⊢
  linear_combination ((d : ZMod (d + 1)) + 2) * hz

lemma ite_pair {R : Type*} [AddMonoidWithOne R] {a b x : Fin n} (h : a ≠ b) :
    (((if {x} ⊆ ({a, b} : Finset (Fin n)) then 1 else 0 : ℕ)) : R) =
      (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
  by_cases hxa : x = a
  · subst hxa; simp [h]
  · by_cases hxb : x = b
    · subst hxb; simp [hxa]
    · simp [hxa, hxb]

/-! ### The pieces are divisible -/

lemma sum_swP0 {M : Type*} [AddCommMonoid M] {u v : Fin n} (huv : u ≠ v) (f : GLab n → M) :
    ∑ ℓ ∈ swP0 t {u, v}, f ℓ = f (.anti t (.x {u, v})) +
      (f (.path t (.x {u, v}) 0) + (f (.tok t (.x {u, v}) u) + f (.tok t (.x {u, v}) v))) := by
  have hP0 : swP0 t {u, v} = insert (GLab.anti t (.x {u, v})) (insert (.path t (.x {u, v}) 0)
      (insert (.tok t (.x {u, v}) u) {.tok t (.x {u, v}) v})) := by
    simp [swP0, swRest, image_insert]
  rw [hP0, sum_insert (by simp), sum_insert (by simp), sum_pair (by simp [huv])]

theorem swP1_divisible {q : ℕ} (hq : 2 ≤ q) (e : Finset (Fin n)) :
    MIsDivisible q 2 (endsG P q) (liftS (sg P q) (swP1 t e)) := by
  have hne : (GLab.x e : GLab n) ≠ .anti t (.x e) := by simp
  have hpos : 1 ≤ q * (q - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  apply divisible_of_zmod
  · rw [swP1, sum_pair hne, wdeg_x, wdeg_anti]
    simp only [empty_subset, if_true]
    rw [show 1 + (q * (q - 1) - 1) = 2 * q.choose 2 by rw [two_mul_choose_two]; omega]
    push_cast; rw [ZMod.natCast_self, mul_zero]
  · intro x
    rw [swP1, sum_pair hne, wdeg_x, wdeg_anti]
    split_ifs
    · rw [show 1 + (q * (q - 1) - 1) = q * (q - 1) by omega]
      push_cast; rw [ZMod.natCast_self, mul_zero]
    · simp

theorem swP0_divisible {q : ℕ} (hq : 2 ≤ q) {X : Finset (Finset (Fin n))} (H : SwitchHyp P t X)
    {e : Finset (Fin n)} (he : e ∈ X) :
    MIsDivisible q 2 (endsG P q) (liftS (sg P q) (swP0 t e)) := by
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.1 (H.card_two e he)
  have hpi : P.pi t u ≠ P.pi t v := fun h =>
    huv (H.pi_inj _ he u (by simp) v (by simp) h)
  have hsum := sum_swP0 (t := t) (M := ℕ) huv
  have hsh := H.shape _ he
  have hpos : 1 ≤ q * (q - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  apply divisible_of_zmod
  · rw [hsum, wdeg_anti, wdeg_path q hsh, wdeg_tok_empty hq, wdeg_tok_empty hq]
    simp only [empty_subset, if_true]
    rw [show q * (q - 1) - 1 + (1 + (q * (q - 1) + q * (q - 1))) = 6 * q.choose 2 by
      have := two_mul_choose_two q; omega]
    push_cast; rw [ZMod.natCast_self, mul_zero]
  · intro x
    rw [hsum]
    push_cast
    rw [tok_cls hq _ _ _ (H.ne_hw u) (H.ne_pi u) (H.hw_ne_pi u),
      tok_cls hq _ _ _ (H.ne_hw v) (H.ne_pi v) (H.hw_ne_pi v), wdeg_anti, wdeg_path q hsh,
      image_insert, image_singleton]
    have ha : (((if {x} ⊆ ({u, v} : Finset (Fin n)) then q * (q - 1) - 1 else 0 : ℕ)) :
        ZMod (q - 1)) = -((if x = u then 1 else 0) + (if x = v then 1 else 0)) := by
      rw [← ite_pair huv]
      split_ifs <;> simp [cast_anti hq]
    rw [ha, ite_pair hpi]
    ring


/-! ### Owners and the decomposition -/

/-- The edge a switch label belongs to. -/
def own : GLab n → Finset (Fin n)
  | .x e => e
  | .anti _ (.x e) => e
  | .tok _ (.x e) _ => e
  | .path _ (.x e) _ => e
  | _ => ∅

lemma mem_swP1 {e : Finset (Fin n)} {ℓ : GLab n} :
    ℓ ∈ swP1 t e ↔ ℓ = .x e ∨ ℓ = .anti t (.x e) := by
  simp [swP1]

lemma mem_swRest {e : Finset (Fin n)} {ℓ : GLab n} :
    ℓ ∈ swRest t e ↔ ℓ = .path t (.x e) 0 ∨ ∃ u ∈ e, ℓ = .tok t (.x e) u := by
  simp [swRest, eq_comm]

lemma mem_swP0 {e : Finset (Fin n)} {ℓ : GLab n} :
    ℓ ∈ swP0 t e ↔ ℓ = .anti t (.x e) ∨ ℓ ∈ swRest t e := by
  simp [swP0]

lemma own_of_mem_swP1 {e : Finset (Fin n)} {ℓ : GLab n} (h : ℓ ∈ swP1 t e) : own ℓ = e := by
  rcases mem_swP1.1 h with rfl | rfl <;> rfl

lemma own_of_mem_swRest {e : Finset (Fin n)} {ℓ : GLab n} (h : ℓ ∈ swRest t e) : own ℓ = e := by
  rcases mem_swRest.1 h with rfl | ⟨u, -, rfl⟩ <;> rfl

lemma own_of_mem_swP0 {e : Finset (Fin n)} {ℓ : GLab n} (h : ℓ ∈ swP0 t e) : own ℓ = e := by
  rcases mem_swP0.1 h with rfl | h
  · rfl
  · exact own_of_mem_swRest h

lemma swP1_disjoint_swRest (e : Finset (Fin n)) : Disjoint (swP1 t e) (swRest t e) := by
  rw [Finset.disjoint_left]
  intro ℓ h1 h2
  rcases mem_swP1.1 h1 with rfl | rfl <;> rcases mem_swRest.1 h2 with h | ⟨u, -, h⟩ <;> cases h

/-- Pieces of different edges are disjoint. -/
lemma disjoint_of_own {e e' : Finset (Fin n)} (hne : e ≠ e') {W W' : Finset (GLab n)}
    (hW : ∀ ℓ ∈ W, own ℓ = e) (hW' : ∀ ℓ ∈ W', own ℓ = e') : Disjoint W W' := by
  rw [Finset.disjoint_left]
  intro ℓ h h'
  exact hne ((hW ℓ h).symm.trans (hW' ℓ h'))

/-- The pieces chosen for the selected edges `L ⊆ X`. -/
def swU (t : ℕ) (X L : Finset (Finset (Fin n))) : Finset (Finset (GLab n)) :=
  L.image (swP1 t) ∪ (X \ L).image (swP0 t)

/-- The residue of the switch for the selected edges `L`: the rest of every selected edge. -/
def swRes (t : ℕ) (L : Finset (Finset (Fin n))) : Finset (GLab n) := L.biUnion (swRest t)

lemma swU_subset (X L : Finset (Finset (Fin n))) (hL : L ⊆ X) : swU t X L ⊆ swW t X := by
  unfold swU swW
  exact union_subset_union (image_subset_image hL) (image_subset_image sdiff_subset)

lemma swU_pairwise (X L : Finset (Finset (Fin n))) :
    ((swU t X L : Finset (Finset (GLab n))) : Set (Finset (GLab n))).PairwiseDisjoint id := by
  intro W hW W' hW' hne
  simp only [swU, coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe, mem_sdiff] at hW hW'
  have key : ∀ e e' : Finset (Fin n), ∀ W W' : Finset (GLab n), (∀ ℓ ∈ W, own ℓ = e) →
      (∀ ℓ ∈ W', own ℓ = e') → (e = e' → W = W') → W ≠ W' → Disjoint (id W) (id W') :=
    fun e e' W W' h h' heq hne => disjoint_of_own (fun he => hne (heq he)) h h'
  rcases hW with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩ <;> rcases hW' with ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
  · exact key e e' _ _ (fun _ => own_of_mem_swP1) (fun _ => own_of_mem_swP1)
      (fun h => by rw [h]) hne
  · exact key e e' _ _ (fun _ => own_of_mem_swP1) (fun _ => own_of_mem_swP0)
      (fun h => absurd (h ▸ he) he'.2) hne
  · exact key e e' _ _ (fun _ => own_of_mem_swP0) (fun _ => own_of_mem_swP1)
      (fun h => absurd (h ▸ he') he.2) hne
  · exact key e e' _ _ (fun _ => own_of_mem_swP0) (fun _ => own_of_mem_swP0)
      (fun h => by rw [h]) hne

lemma mem_swU_sup {X L : Finset (Finset (Fin n))} {ℓ : GLab n} :
    ℓ ∈ (swU t X L).sup id ↔ (∃ e ∈ L, ℓ ∈ swP1 t e) ∨ ∃ e ∈ X \ L, ℓ ∈ swP0 t e := by
  simp only [mem_sup, swU, mem_union, mem_image, id]
  constructor
  · rintro ⟨W, ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩, h⟩
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩
  · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩)
    · exact ⟨_, Or.inl ⟨e, he, rfl⟩, h⟩
    · exact ⟨_, Or.inr ⟨e, he, rfl⟩, h⟩

/-- **The rest of the switch.**  For every set `L ⊆ X` of selected edges, the reservoir together
with the selected inputs is the disjoint union of the chosen pieces and of the residue
`swRes L`, which consists exactly of the partner tokens and the remainder labels of the selected
edges. -/
theorem switch_decomp (X L : Finset (Finset (Fin n))) (hL : L ⊆ X) :
    ((swU t X L : Finset (Finset (GLab n))) : Set (Finset (GLab n))).PairwiseDisjoint id ∧
      Disjoint ((swU t X L).sup id) (swRes t L) ∧
      (swU t X L).sup id ∪ swRes t L = swR t X ∪ L.image GLab.x := by
  refine ⟨swU_pairwise X L, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro ℓ h1 h2
    rw [mem_swU_sup] at h1
    obtain ⟨e', he', h2⟩ := mem_biUnion.1 h2
    rcases h1 with ⟨e, he, h⟩ | ⟨e, he, h⟩
    · obtain rfl := (own_of_mem_swP1 h).symm.trans (own_of_mem_swRest h2)
      exact Finset.disjoint_left.1 (swP1_disjoint_swRest e) h h2
    · obtain rfl := (own_of_mem_swP0 h).symm.trans (own_of_mem_swRest h2)
      exact (mem_sdiff.1 he).2 he'
  · ext ℓ
    simp only [mem_union, mem_swU_sup, swRes, swR, mem_biUnion, mem_image]
    constructor
    · rintro ((⟨e, he, h⟩ | ⟨e, he, h⟩) | ⟨e, he, h⟩)
      · rcases mem_swP1.1 h with rfl | rfl
        · exact Or.inr ⟨e, he, rfl⟩
        · exact Or.inl ⟨e, hL he, mem_swP0.2 (Or.inl rfl)⟩
      · exact Or.inl ⟨e, (mem_sdiff.1 he).1, h⟩
      · exact Or.inl ⟨e, hL he, mem_swP0.2 (Or.inr h)⟩
    · rintro (⟨e, he, h⟩ | ⟨e, he, rfl⟩)
      · by_cases heL : e ∈ L
        · rcases mem_swP0.1 h with rfl | h
          · exact Or.inl (Or.inl ⟨e, heL, mem_swP1.2 (Or.inr rfl)⟩)
          · exact Or.inr ⟨e, heL, h⟩
        · exact Or.inl (Or.inr ⟨e, mem_sdiff.2 ⟨he, heL⟩, h⟩)
      · exact Or.inl (Or.inl ⟨e, he, mem_swP1.2 (Or.inl rfl)⟩)


/-! ### The switch stage as a residual multi-refiner -/

lemma swP0_pairwise (X : Finset (Finset (Fin n))) :
    (X : Set (Finset (Fin n))).PairwiseDisjoint (swP0 t) :=
  fun _ _ _ _ hne => disjoint_of_own hne (fun _ => own_of_mem_swP0) (fun _ => own_of_mem_swP0)

/-- Lifts of pairwise disjoint unions of label sets with divisible lifts are divisible. -/
lemma divisible_liftS_biUnion {Λ V ι : Type} [DecidableEq Λ] [DecidableEq V] {q r : ℕ}
    {sg' : Λ → List (Finset V × ℕ)} (s : Finset ι) (f : ι → Finset Λ)
    (hf : (s : Set ι).PairwiseDisjoint f)
    (h : ∀ i ∈ s, MIsDivisible q r (cpEnds sg') (liftS sg' (f i))) :
    MIsDivisible q r (cpEnds sg') (liftS sg' (s.biUnion f)) := by
  intro S hS
  rw [mdeg_liftS, sum_biUnion hf]
  exact dvd_sum fun i hi => by rw [← mdeg_liftS]; exact h i hi S hS

lemma card_liftS_swP1 (q : ℕ) (e : Finset (Fin n)) :
    (liftS (sg P q) (swP1 t e)).card = 1 + (q * (q - 1) - 1) := by
  rw [card_liftS, swP1, sum_pair (by simp), wdeg_x, wdeg_anti]
  simp

lemma card_liftS_swP0 {q : ℕ} (hq : 2 ≤ q) {X : Finset (Finset (Fin n))} (H : SwitchHyp P t X)
    {e : Finset (Fin n)} (he : e ∈ X) :
    (liftS (sg P q) (swP0 t e)).card = 3 * (q * (q - 1)) := by
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.1 (H.card_two e he)
  have hpos : 1 ≤ q * (q - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  rw [card_liftS, sum_swP0 huv, wdeg_anti, wdeg_path q (H.shape _ he), wdeg_tok_empty hq,
    wdeg_tok_empty hq]
  simp only [empty_subset, if_true]
  omega

/-- **One switch stage with partner tokens is a residual multi-refiner** (`r = 2`, any `q ≥ 2`;
the relevant case is odd `q`, where local unit tokens do not exist).  It is obtained from
`lift_residual`: inputs are the edges of `X`, the reservoir consists of the pieces `swP0 e`, the
residue lies in the rests `swRest e`, and pieces have size and multiplicity at most
`3 q (q - 1)`. -/
theorem switch_residual {q : ℕ} (hq : 2 ≤ q) {X : Finset (Finset (Fin n))} (H : SwitchHyp P t X) :
    IsResidualMultiRefiner q 2 (3 * (q * (q - 1))) (endsG P q) (liftS (sg P q) (swI X))
      (liftS (sg P q) (swR t X)) (liftS (sg P q) (swY t X)) ((swW t X).image (liftS (sg P q))) := by
  have hpos : 1 ≤ q * (q - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  apply lift_residual (sg P q) (pe P)
  · intro ℓ hℓ
    obtain ⟨e, -, rfl⟩ := mem_image.1 hℓ
    rfl
  · intro ℓ hℓ s hs
    rcases mem_union.1 hℓ with hℓ | hℓ
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hℓ
      simp only [sg, List.mem_singleton] at hs
      subst hs
      exact H.card_two e he
    · obtain ⟨e, he, hℓ⟩ := mem_biUnion.1 hℓ
      rcases mem_swP0.1 hℓ with rfl | hℓ
      · simp only [sg, List.mem_singleton] at hs
        subst hs
        exact H.card_two e he
      · rcases mem_swRest.1 hℓ with rfl | ⟨u, -, rfl⟩
        · simp only [sg, List.mem_singleton] at hs
          subst hs
          simp only [pe, H.shape e he, List.getD_cons_zero]
          rw [card_image_of_injOn (fun a ha b hb h => H.pi_inj e he a ha b hb h)]
          exact H.card_two e he
        · simp only [sg, tokSg, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · exact card_pair (H.ne_hw u)
          · exact card_pair (H.hw_ne_pi u)
  · rw [Finset.disjoint_left]
    intro ℓ h1 h2
    obtain ⟨e, -, rfl⟩ := mem_image.1 h1
    obtain ⟨e', -, h2⟩ := mem_biUnion.1 h2
    rcases mem_swP0.1 h2 with h | h
    · cases h
    · rcases mem_swRest.1 h with h | ⟨u, -, h⟩ <;> cases h
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨e, -, rfl⟩ := mem_image.1 hW
      exact swP1_divisible hq e
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hW
      exact swP0_divisible hq H he
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hW
      intro ℓ hℓ
      rcases mem_swP1.1 hℓ with rfl | rfl
      · exact mem_union_left _ (mem_image_of_mem _ he)
      · exact mem_union_right _ (mem_biUnion.2 ⟨e, he, mem_swP0.2 (Or.inl rfl)⟩)
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hW
      exact (subset_biUnion_of_mem (swP0 t) he).trans subset_union_right
  · intro W hW
    rcases mem_union.1 hW with hW | hW
    · obtain ⟨e, -, rfl⟩ := mem_image.1 hW
      rw [card_liftS_swP1]; omega
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hW
      rw [card_liftS_swP0 hq H he]
  · intro ℓ
    have hsub : (swW t X).filter (ℓ ∈ ·) ⊆ {swP1 t (own ℓ), swP0 t (own ℓ)} := by
      intro W hW
      rw [mem_filter] at hW
      obtain ⟨hW, hℓ⟩ := hW
      rcases mem_union.1 hW with hW | hW
      · obtain ⟨e, -, rfl⟩ := mem_image.1 hW
        rw [own_of_mem_swP1 hℓ]; simp
      · obtain ⟨e, -, rfl⟩ := mem_image.1 hW
        rw [own_of_mem_swP0 hℓ]; simp
    exact (card_le_card hsub).trans (card_insert_le _ _ |>.trans (by simp; omega))
  · exact divisible_liftS_biUnion X (swP0 t) (swP0_pairwise X) fun e he => swP0_divisible hq H he
  · intro Ls hLs _
    set L := X.filter (fun e => GLab.x e ∈ Ls) with hLdef
    have hLX : L ⊆ X := filter_subset _ _
    have hLs' : Ls = L.image GLab.x := by
      ext ℓ
      constructor
      · intro h
        obtain ⟨e, he, rfl⟩ := mem_image.1 (hLs h)
        exact mem_image_of_mem _ (mem_filter.2 ⟨he, h⟩)
      · intro h
        obtain ⟨e, he, rfl⟩ := mem_image.1 h
        exact (mem_filter.1 he).2
    obtain ⟨h1, h2, h3⟩ := switch_decomp X L hLX
    refine ⟨swU t X L, swU_subset X L hLX, swRes t L,
      biUnion_subset_biUnion_of_subset_left _ hLX, h1, h2, ?_⟩
    rw [h3, hLs']

/-! ### The rest: degree classes and sizes -/

lemma sum_swRest {M : Type*} [AddCommMonoid M] {u v : Fin n} (huv : u ≠ v) (f : GLab n → M) :
    ∑ ℓ ∈ swRest t {u, v}, f ℓ =
      f (.path t (.x {u, v}) 0) + (f (.tok t (.x {u, v}) u) + f (.tok t (.x {u, v}) v)) := by
  have h : swRest t {u, v} = insert (GLab.path t (.x {u, v}) 0)
      (insert (.tok t (.x {u, v}) u) {.tok t (.x {u, v}) v}) := by
    simp [swRest, image_insert]
  rw [h, sum_insert (by simp), sum_pair (by simp [huv])]

/-- **The remainder label is one copy of the image edge.**  The lift of the remainder label of
`e` is a single copy, whose ends are the partners of the ends of `e`. -/
theorem remainder_lift (q : ℕ) {e : Finset (Fin n)} (he : P.shape t e = [e.image (P.pi t)]) :
    liftS (sg P q) {.path t (.x e) 0} = {(.path t (.x e) 0, 0, 0)} ∧
      endsG P q (.path t (.x e) 0, 0, 0) = e.image (P.pi t) := by
  refine ⟨?_, ?_⟩
  · ext c
    obtain ⟨ℓ, a, b⟩ := c
    simp only [mem_liftS, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, ha, hb⟩
      simp only [sg, List.length_singleton, Nat.lt_one_iff] at ha
      subst ha
      simp only [segAt, sg, List.getD_cons_zero, Nat.lt_one_iff] at hb
      exact ⟨rfl, rfl, hb⟩
    · rintro ⟨rfl, rfl, rfl⟩
      simp [sg, segAt]
  · simp [endsG, cpEnds, segAt, sg, pe, he]

/-- **Degree classes of the rest of an edge.**  The rest of `e = uv` (two partner tokens of
classes `1_u - 1_{π u}`, `1_v - 1_{π v}` and the remainder copy of `π u π v`) has the same
degree classes modulo `q - 1` as the edge `e` itself, and `2 q (q - 1) + 1` copies. -/
theorem swRest_classes {q : ℕ} (hq : 2 ≤ q) {X : Finset (Finset (Fin n))} (H : SwitchHyp P t X)
    {e : Finset (Fin n)} (he : e ∈ X) (x : Fin n) :
    ((mdeg (endsG P q) (liftS (sg P q) (swRest t e)) {x} : ℕ) : ZMod (q - 1)) =
      (if x ∈ e then 1 else 0) ∧
    (liftS (sg P q) (swRest t e)).card = 2 * (q * (q - 1)) + 1 := by
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.1 (H.card_two e he)
  have hpi : P.pi t u ≠ P.pi t v := fun h =>
    huv (H.pi_inj _ he u (by simp) v (by simp) h)
  have hsh := H.shape _ he
  refine ⟨?_, ?_⟩
  · rw [mdeg_liftS, sum_swRest huv]
    push_cast
    rw [tok_cls hq _ _ _ (H.ne_hw u) (H.ne_pi u) (H.hw_ne_pi u),
      tok_cls hq _ _ _ (H.ne_hw v) (H.ne_pi v) (H.hw_ne_pi v), wdeg_path q hsh,
      image_insert, image_singleton, ite_pair hpi]
    have h : ((if x ∈ ({u, v} : Finset (Fin n)) then 1 else 0 : ZMod (q - 1))) =
        (if x = u then 1 else 0) + (if x = v then 1 else 0) := by
      have := ite_pair (R := ZMod (q - 1)) (x := x) huv
      simp only [singleton_subset_iff] at this
      rw [← this]; split_ifs <;> simp
    rw [h]; ring
  · rw [card_liftS, sum_swRest huv, wdeg_path q hsh, wdeg_tok_empty hq, wdeg_tok_empty hq]
    simp only [empty_subset, if_true]
    ring

lemma swRest_pairwise (L : Finset (Finset (Fin n))) :
    (L : Set (Finset (Fin n))).PairwiseDisjoint (swRest t) :=
  fun _ _ _ _ hne => disjoint_of_own hne (fun _ => own_of_mem_swRest) (fun _ => own_of_mem_swRest)

/-- **Degree classes of the residue.**  For selected edges `L ⊆ X`, the residue `swRes L` has
degree `≡ deg_L x (mod q - 1)` at every vertex `x` and `(2 q (q - 1) + 1) |L|` copies; so it
carries exactly the divisibility data of `L`. -/
theorem swRes_classes {q : ℕ} (hq : 2 ≤ q) {X : Finset (Finset (Fin n))} (H : SwitchHyp P t X)
    {L : Finset (Finset (Fin n))} (hL : L ⊆ X) (x : Fin n) :
    ((mdeg (endsG P q) (liftS (sg P q) (swRes t L)) {x} : ℕ) : ZMod (q - 1)) =
      ((L.filter (x ∈ ·)).card : ZMod (q - 1)) ∧
    (liftS (sg P q) (swRes t L)).card = (2 * (q * (q - 1)) + 1) * L.card := by
  refine ⟨?_, ?_⟩
  · rw [mdeg_liftS, swRes, sum_biUnion (swRest_pairwise L), Nat.cast_sum, card_filter,
      Nat.cast_sum]
    refine sum_congr rfl fun e he => ?_
    have h := (swRest_classes hq H (hL he) x).1
    rw [mdeg_liftS] at h
    rw [h]; split_ifs <;> simp
  · rw [card_liftS, swRes, sum_biUnion (swRest_pairwise L), mul_comm, ← smul_eq_mul,
      ← sum_const]
    refine sum_congr rfl fun e he => ?_
    rw [← card_liftS]
    exact (swRest_classes hq H (hL he) x).2

/-! ### Obstruction: the remainder cannot be dropped -/

/-- **The remainder is necessary** (`q ≥ 3`).  Without the remainder label, the switch piece of
an edge (its anti-edge and its two partner tokens) is never divisible: it has
`3 q (q - 1) - 1 ≡ -1 (mod binom(q, 2))` copies. -/
theorem switch_needs_remainder {q : ℕ} (hq : 3 ≤ q) {X : Finset (Finset (Fin n))}
    (H : SwitchHyp P t X) {e : Finset (Fin n)} (he : e ∈ X) :
    ¬ MIsDivisible q 2 (endsG P q)
      (liftS (sg P q) (insert (.anti t (.x e)) (e.image (.tok t (.x e))))) := by
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.1 (H.card_two e he)
  intro h
  have h0 := h ∅ (by simp)
  have hcard : mdeg (endsG P q)
      (liftS (sg P q) (insert (.anti t (.x {u, v})) (({u, v} : Finset (Fin n)).image
        (.tok t (.x {u, v}))))) ∅ = 6 * q.choose 2 - 1 := by
    rw [mdeg_liftS, image_insert, image_singleton, sum_insert (by simp), sum_pair (by simp [huv]),
      wdeg_anti, wdeg_tok_empty (by omega), wdeg_tok_empty (by omega)]
    simp only [empty_subset, if_true]
    have := two_mul_choose_two q
    have : 1 ≤ q * (q - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    omega
  simp only [card_empty, Nat.sub_zero] at h0
  rw [hcard] at h0
  have h3 : 3 ≤ q.choose 2 := by
    calc 3 = (3 : ℕ).choose 2 := rfl
      _ ≤ q.choose 2 := Nat.choose_le_choose 2 hq
  have h6 : q.choose 2 ∣ 6 * q.choose 2 := dvd_mul_left _ _
  have h1 : q.choose 2 ∣ 1 := by
    have := (Nat.dvd_sub_iff_right (by omega) h6).2 h0
    rwa [show 6 * q.choose 2 - (6 * q.choose 2 - 1) = 1 by omega] at this
  have := Nat.le_of_dvd one_pos h1
  omega

/-! ### Loads -/

/-- Every label of the stage has at most `q (q - 1)` copies. -/
lemma wdeg_le_of_mem {q : ℕ} (hq : 2 ≤ q) {X : Finset (Finset (Fin n))} (H : SwitchHyp P t X)
    {ℓ : GLab n} (hℓ : ℓ ∈ swI X ∪ swR t X) : wdeg (sg P q) ℓ ∅ ≤ q * (q - 1) := by
  have hpos : 1 ≤ q * (q - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  rcases mem_union.1 hℓ with hℓ | hℓ
  · obtain ⟨e, -, rfl⟩ := mem_image.1 hℓ
    rw [wdeg_x]; simpa using hpos
  · obtain ⟨e, he, hℓ⟩ := mem_biUnion.1 hℓ
    rcases mem_swP0.1 hℓ with rfl | hℓ
    · rw [wdeg_anti]; simp
    · rcases mem_swRest.1 hℓ with rfl | ⟨u, -, rfl⟩
      · rw [wdeg_path q (H.shape e he)]; simpa using hpos
      · rw [wdeg_tok_empty hq]

/-- **Load of the switch stage.**  The degree of a vertex `x` in the lifted inputs and reservoir
is at most `q (q - 1) · 3 (|A_x| + |B_x|)`, where `A_x` is the set of edges of `X` at `x` and
`B_x` the set of edges of `X` with an end `u` such that `π u = x` or `hw u = x`. -/
theorem switch_load {q : ℕ} (hq : 2 ≤ q) {X : Finset (Finset (Fin n))} (H : SwitchHyp P t X)
    (x : Fin n) :
    mdeg (endsG P q) (liftS (sg P q) (swI X ∪ swR t X)) {x} ≤
      q * (q - 1) * (3 * (X.filter (x ∈ ·)).card +
        3 * (X.filter fun e => ∃ u ∈ e, P.pi t u = x ∨ P.hw t u = x).card) := by
  set A := X.filter (x ∈ ·) with hA
  set B := X.filter fun e => ∃ u ∈ e, P.pi t u = x ∨ P.hw t u = x with hB
  refine (mdeg_liftS_le _ x (q * (q - 1)) fun ℓ hℓ => wdeg_le_of_mem hq H hℓ).trans ?_
  refine Nat.mul_le_mul_left _ ?_
  have hsub : (swI X ∪ swR t X).filter (touch (sg P q) x ·) ⊆
      ((A.image GLab.x ∪ A.image (fun e => GLab.anti t (.x e))) ∪
        A.image (fun e => GLab.tok t (.x e) x)) ∪
      (B.image (fun e => GLab.path t (.x e) 0) ∪ B.biUnion fun e => e.image (.tok t (.x e))) := by
    intro ℓ hℓ
    rw [mem_filter, touch_iff] at hℓ
    obtain ⟨hℓ, p, hp, hx⟩ := hℓ
    simp only [mem_union, mem_image, mem_biUnion, hA, hB, mem_filter]
    rcases mem_union.1 hℓ with hℓ | hℓ
    · obtain ⟨e, he, rfl⟩ := mem_image.1 hℓ
      simp only [sg, List.mem_singleton] at hp
      subst hp
      exact Or.inl (Or.inl (Or.inl ⟨e, ⟨he, hx⟩, rfl⟩))
    · obtain ⟨e, he, hℓ⟩ := mem_biUnion.1 hℓ
      rcases mem_swP0.1 hℓ with rfl | hℓ
      · simp only [sg, List.mem_singleton] at hp
        subst hp
        exact Or.inl (Or.inl (Or.inr ⟨e, ⟨he, hx⟩, rfl⟩))
      · rcases mem_swRest.1 hℓ with rfl | ⟨u, hu, rfl⟩
        · simp only [sg, List.mem_singleton] at hp
          subst hp
          simp only [pe, H.shape e he, List.getD_cons_zero, mem_image] at hx
          obtain ⟨u, hu, hux⟩ := hx
          exact Or.inr (Or.inl ⟨e, ⟨he, u, hu, Or.inl hux⟩, rfl⟩)
        · simp only [sg, tokSg, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl <;> simp only [mem_insert, mem_singleton] at hx
          · rcases hx with rfl | rfl
            · exact Or.inl (Or.inr ⟨e, ⟨he, hu⟩, rfl⟩)
            · exact Or.inr (Or.inr ⟨e, ⟨he, u, hu, Or.inr rfl⟩, u, hu, rfl⟩)
          · rcases hx with rfl | rfl
            · exact Or.inr (Or.inr ⟨e, ⟨he, u, hu, Or.inr rfl⟩, u, hu, rfl⟩)
            · exact Or.inr (Or.inr ⟨e, ⟨he, u, hu, Or.inl rfl⟩, u, hu, rfl⟩)
  refine (card_le_card hsub).trans ?_
  have hBi : (B.biUnion fun e => e.image (GLab.tok t (.x e))).card ≤ 2 * B.card := by
    refine card_biUnion_le.trans ?_
    rw [mul_comm, ← smul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun e he => ?_
    exact card_image_le.trans (H.card_two e (mem_filter.1 he).1).le
  have h1 := card_union_le (A.image GLab.x ∪ A.image (fun e => GLab.anti t (.x e)) ∪
    A.image (fun e => GLab.tok t (.x e) x))
    (B.image (fun e => GLab.path t (.x e) 0) ∪ B.biUnion fun e => e.image (.tok t (.x e)))
  have h2 := card_union_le (A.image GLab.x ∪ A.image (fun e => GLab.anti t (.x e)))
    (A.image (fun e => GLab.tok t (.x e) x))
  have h3 := card_union_le (A.image GLab.x) (A.image (fun e => GLab.anti t (.x e)))
  have h4 := card_union_le (B.image (fun e => GLab.path t (.x e) 0))
    (B.biUnion fun e => e.image (.tok t (.x e)))
  have i1 : (A.image GLab.x).card ≤ A.card := card_image_le
  have i2 : (A.image (fun e => GLab.anti t (.x e))).card ≤ A.card := card_image_le
  have i3 : (A.image (fun e => GLab.tok t (.x e) x)).card ≤ A.card := card_image_le
  have i4 : (B.image (fun e => GLab.path t (.x e) 0)).card ≤ B.card := card_image_le
  omega

/-- Edges with an end in the fibre of an injective map over `x`. -/
lemma card_fibre_edges_le {X : Finset (Finset (Fin n))} {f : Fin n → Fin n}
    (hf : Function.Injective f) {D : ℕ} (hD : ∀ y, (X.filter (y ∈ ·)).card ≤ D) (x : Fin n) :
    (X.filter fun e => ∃ u ∈ e, f u = x).card ≤ D := by
  by_cases h : ∃ y, f y = x
  · obtain ⟨y, rfl⟩ := h
    refine le_trans (card_le_card fun e he => ?_) (hD y)
    obtain ⟨he, u, hu, hfu⟩ := mem_filter.1 he
    exact mem_filter.2 ⟨he, hf hfu ▸ hu⟩
  · push_neg at h
    rw [filter_false_of_mem fun e _ => fun ⟨u, _, hu⟩ => h u hu, card_empty]
    exact Nat.zero_le _

/-- **The switch stage has load `O(D)`** when the partner and helper maps are injective: every
vertex has degree at most `9 q (q - 1) D` in the lifted inputs and reservoir, where `D` bounds
the degrees of `X`. -/
theorem switch_load_inj {q : ℕ} (hq : 2 ≤ q) {X : Finset (Finset (Fin n))} (H : SwitchHyp P t X)
    (hpi : Function.Injective (P.pi t)) (hhw : Function.Injective (P.hw t)) {D : ℕ}
    (hD : ∀ y, (X.filter (y ∈ ·)).card ≤ D) (x : Fin n) :
    mdeg (endsG P q) (liftS (sg P q) (swI X ∪ swR t X)) {x} ≤ 9 * (q * (q - 1)) * D := by
  refine (switch_load hq H x).trans ?_
  have hB : (X.filter fun e => ∃ u ∈ e, P.pi t u = x ∨ P.hw t u = x).card ≤ 2 * D := by
    have hsub : (X.filter fun e => ∃ u ∈ e, P.pi t u = x ∨ P.hw t u = x) ⊆
        (X.filter fun e => ∃ u ∈ e, P.pi t u = x) ∪ (X.filter fun e => ∃ u ∈ e, P.hw t u = x) := by
      intro e he
      obtain ⟨he, u, hu, h⟩ := mem_filter.1 he
      rcases h with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨he, u, hu, h⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨he, u, hu, h⟩)
    have := card_fibre_edges_le hpi hD x
    have := card_fibre_edges_le hhw hD x
    have := card_union_le (X.filter fun e => ∃ u ∈ e, P.pi t u = x)
      (X.filter fun e => ∃ u ∈ e, P.hw t u = x)
    have := card_le_card hsub
    omega
  have hA := hD x
  calc q * (q - 1) * (3 * (X.filter (x ∈ ·)).card +
        3 * (X.filter fun e => ∃ u ∈ e, P.pi t u = x ∨ P.hw t u = x).card)
      ≤ q * (q - 1) * (3 * D + 3 * (2 * D)) := Nat.mul_le_mul_left _ (by omega)
    _ = 9 * (q * (q - 1)) * D := by ring

/-! ### A concrete plan -/

/-- The shift plan on `Fin n`: partner `u + 1`, helper `u + 2`. -/
def shiftPlan (n : ℕ) [NeZero n] : Plan n where
  pi _ u := u + 1
  hw _ u := u + 2
  shape _ e := [e.image (· + 1)]

lemma shiftPlan_hyp {n : ℕ} [NeZero n] (hn : 3 ≤ n) (t : ℕ) {X : Finset (Finset (Fin n))}
    (hX : ∀ e ∈ X, e.card = 2) : SwitchHyp (shiftPlan n) t X where
  card_two := hX
  ne_hw u := tok_ne₂ hn u
  ne_pi u := tok_ne₁ hn u
  hw_ne_pi u := (tok_ne₁₂ hn u).symm
  pi_inj _ _ _ _ _ _ h := add_right_cancel h
  shape _ _ := rfl

/-- **One switch stage with partner tokens, for any graph** (`r = 2`, `q ≥ 2`, `n ≥ 3`).  For every
graph `X` on `Fin n` with maximum degree at most `D`, the switch stage of the shift plan is a
residual multi-refiner with constant `3 q (q - 1)`, whose lifted inputs and reservoir have
maximum degree at most `9 q (q - 1) D`.  The residue for selected edges `L` is the rest of the
edges of `L` (`switch_decomp`, `swRes_classes`). -/
theorem oddSwitch_stage {n : ℕ} [NeZero n] (hn : 3 ≤ n) {q : ℕ} (hq : 2 ≤ q) (t : ℕ)
    {X : Finset (Finset (Fin n))} (hX : ∀ e ∈ X, e.card = 2) {D : ℕ}
    (hD : ∀ y, (X.filter (y ∈ ·)).card ≤ D) :
    IsResidualMultiRefiner q 2 (3 * (q * (q - 1))) (endsG (shiftPlan n) q)
      (liftS (sg (shiftPlan n) q) (swI X)) (liftS (sg (shiftPlan n) q) (swR t X))
      (liftS (sg (shiftPlan n) q) (swY t X)) ((swW t X).image (liftS (sg (shiftPlan n) q))) ∧
    ∀ x, mdeg (endsG (shiftPlan n) q) (liftS (sg (shiftPlan n) q) (swI X ∪ swR t X)) {x} ≤
      9 * (q * (q - 1)) * D :=
  ⟨switch_residual hq (shiftPlan_hyp hn t hX),
    switch_load_inj hq (shiftPlan_hyp hn t hX) (fun _ _ h => add_right_cancel h)
      (fun _ _ h => add_right_cancel h) hD⟩

end RefinedAbsorption.GridRefiner
