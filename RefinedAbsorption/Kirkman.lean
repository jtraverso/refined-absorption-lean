module
public import RefinedAbsorption.Statements

/-!
# Kirkman's theorem

Kirkman's theorem (Section 1.1): an `(n, 3, 2)`-Steiner system exists if and only if
`n ≡ 1, 3 (mod 6)`.  The necessity is `IsSteinerSystem.mod_six`; here we prove sufficiency via
*Steiner quasigroups*: a commutative binary operation `t` with `t a a = a` and
`t a (t a b) = b` yields the Steiner triple system `{{a, b, t a b} : a ≠ b}`.

* `n = 6k + 3`: Bose's construction on `ℤ_{2k+1} × ℤ_3`;
* `n = 6k + 1`: Skolem's construction on `{∞} ∪ ℤ_{2k} × ℤ_3`, using a half-idempotent
  commutative quasigroup on `ℤ_{2k}`.
-/

@[expose] public section

namespace RefinedAbsorption

open Finset

/-! ### Steiner quasigroups give Steiner triple systems -/

section Quasigroup

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The triples `{a, b, t a b}` for `a ≠ b`. -/
def quasigroupBlocks (t : V → V → V) : Finset (Finset V) :=
  (univ.filter (fun p : V × V => p.1 ≠ p.2)).image (fun p => {p.1, p.2, t p.1 p.2})

/-- A Steiner quasigroup yields a Steiner triple system. -/
theorem isSteinerSystem_quasigroupBlocks (t : V → V → V) (ht0 : ∀ a, t a a = a)
    (ht1 : ∀ a b, t a b = t b a) (ht2 : ∀ a b, t a (t a b) = b) :
    IsSteinerSystem 3 2 (quasigroupBlocks t) := by
  have hne1 : ∀ a b, a ≠ b → t a b ≠ a := by
    intro a b hab h; apply hab; rw [← ht2 a b, h, ht0]
  have hne2 : ∀ a b, a ≠ b → t a b ≠ b := by
    intro a b hab h; apply hab; rw [ht1] at h; rw [← ht2 b a, h, ht0]
  have key : ∀ x y, ∀ u ∈ ({x, y, t x y} : Finset V), ∀ v ∈ ({x, y, t x y} : Finset V),
      u ≠ v → ({x, y, t x y} : Finset V) = {u, v, t u v} := by
    intro x y u hu v hv huv
    have e1 : t x (t x y) = y := ht2 x y
    have e2 : t (t x y) x = y := by rw [ht1]; exact ht2 x y
    have e3 : t y (t x y) = x := by rw [ht1 x y]; exact ht2 y x
    have e4 : t (t x y) y = x := by rw [ht1, ht1 x y]; exact ht2 y x
    have e5 : t y x = t x y := ht1 y x
    simp only [mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      (try simp only [e1, e2, e3, e4, e5]) <;>
      (try exact absurd rfl huv) <;> (ext z; simp only [mem_insert, mem_singleton]; tauto)
  refine ⟨?_, ?_⟩
  · intro B hB
    simp only [quasigroupBlocks, mem_image, mem_filter, mem_univ, true_and] at hB
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hB
    rw [card_insert_of_notMem, card_pair (hne2 a b hab).symm]
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hab, (hne1 a b hab).symm⟩
  · intro T hT
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hT
    rw [cliqueMult, card_eq_one]
    refine ⟨{a, b, t a b}, ?_⟩
    ext B
    simp only [quasigroupBlocks, mem_filter, mem_image, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨⟨⟨x, y⟩, -, rfl⟩, hsub⟩
      exact key x y a (hsub (by simp)) b (hsub (by simp)) hab
    · rintro rfl
      exact ⟨⟨⟨a, b⟩, hab, rfl⟩, by intro z; simp; tauto⟩

/-- A Steiner quasigroup on a type with `n` elements yields a Steiner triple system on
`Fin n`. -/
theorem exists_steinerSystem_of_quasigroup {W : Type*} [Fintype W] (t : W → W → W)
    (ht0 : ∀ a, t a a = a) (ht1 : ∀ a b, t a b = t b a) (ht2 : ∀ a b, t a (t a b) = b)
    {n : ℕ} (hn : Fintype.card W = n) :
    ∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem 3 2 𝒮 := by
  let e : W ≃ Fin n := Fintype.equivFinOfCardEq hn
  let t' : Fin n → Fin n → Fin n := fun a b => e (t (e.symm a) (e.symm b))
  refine ⟨quasigroupBlocks t', isSteinerSystem_quasigroupBlocks t' ?_ ?_ ?_⟩
  · intro a; simp [t', ht0]
  · intro a b; simp only [t']; rw [ht1]
  · intro a b; simp [t', ht2]

end Quasigroup

/-! ### Bose's construction: `n = 6k + 3` -/

section Bose

variable (k : ℕ)

instance boseNeZero : NeZero (2 * k + 1) := ⟨by omega⟩

/-- Bose's Steiner quasigroup on `ℤ_{2k+1} × ℤ_3`, built from the idempotent commutative
quasigroup `x ∘ y = (x + y) / 2` on `ℤ_{2k+1}`. -/
def boseT (a b : ZMod (2 * k + 1) × ZMod 3) : ZMod (2 * k + 1) × ZMod 3 :=
  if a.2 = b.2 then
    (if a.1 = b.1 then a else (((k + 1 : ℕ) : ZMod (2 * k + 1)) * (a.1 + b.1), a.2 + 1))
  else if a.1 = b.1 then (a.1, -(a.2 + b.2))
  else if b.2 = a.2 + 1 then (2 * b.1 - a.1, a.2)
  else (2 * a.1 - b.1, b.2)

theorem two_mul_half : (2 : ZMod (2 * k + 1)) * ((k + 1 : ℕ) : ZMod (2 * k + 1)) = 1 := by
  have : ((2 * (k + 1) : ℕ) : ZMod (2 * k + 1)) = ((2 * k + 1 : ℕ) : ZMod (2 * k + 1)) + 1 := by
    push_cast; ring
  rw [ZMod.natCast_self, zero_add] at this
  rw [← this]; push_cast; ring

theorem two_cancel {x y : ZMod (2 * k + 1)} (h : 2 * x = 2 * y) : x = y := by
  have hh := two_mul_half k
  linear_combination ((k + 1 : ℕ) : ZMod (2 * k + 1)) * h - (x - y) * hh

theorem z3_facts : ∀ i j : ZMod 3, i ≠ j → (j = i + 1 ∨ i = j + 1) ∧ ¬ (j = i + 1 ∧ i = j + 1) ∧
    -(i + j) ≠ i ∧ -(i + j) ≠ j ∧ -(i + -(i + j)) = j := by decide

theorem z3_succ_ne : ∀ i : ZMod 3, i + 1 ≠ i ∧ i + 1 + 1 ≠ i := by decide

theorem boseT_L1 {x y : ZMod (2 * k + 1)} (i : ZMod 3) (hxy : x ≠ y) :
    boseT k (x, i) (y, i) = (((k + 1 : ℕ) : ZMod (2 * k + 1)) * (x + y), i + 1) := by
  simp [boseT, hxy]

theorem boseT_L2 (x : ZMod (2 * k + 1)) {i j : ZMod 3} (hij : i ≠ j) :
    boseT k (x, i) (x, j) = (x, -(i + j)) := by simp [boseT, hij]

theorem boseT_L3 {x y : ZMod (2 * k + 1)} {i j : ZMod 3} (hxy : x ≠ y) (h : j = i + 1) :
    boseT k (x, i) (y, j) = (2 * y - x, i) := by
  simp [boseT, hxy, h]

theorem boseT_L4 {x y : ZMod (2 * k + 1)} {i j : ZMod 3} (hxy : x ≠ y) (h : i = j + 1) :
    boseT k (x, i) (y, j) = (2 * x - y, j) := by
  have hij : i ≠ j := by rw [h]; exact (z3_succ_ne j).1
  have h' : ¬ j = i + 1 := by rw [h]; exact (z3_succ_ne j).2.symm
  simp [boseT, hij, hxy, h']

theorem boseT_self (a) : boseT k a a = a := by simp [boseT]

theorem boseT_comm (a b) : boseT k a b = boseT k b a := by
  obtain ⟨x, i⟩ := a
  obtain ⟨y, j⟩ := b
  by_cases hij : i = j
  · subst hij
    by_cases hxy : x = y
    · subst hxy; rfl
    · rw [boseT_L1 k i hxy, boseT_L1 k i (Ne.symm hxy), add_comm x]
  · obtain ⟨h1, -, -⟩ := z3_facts i j hij
    by_cases hxy : x = y
    · subst hxy; rw [boseT_L2 k x hij, boseT_L2 k x (Ne.symm hij), add_comm i]
    · rcases h1 with h1 | h1
      · rw [boseT_L3 k hxy h1, boseT_L4 k (Ne.symm hxy) h1]
      · rw [boseT_L4 k hxy h1, boseT_L3 k (Ne.symm hxy) h1]

theorem boseT_invol (a b) : boseT k a (boseT k a b) = b := by
  obtain ⟨x, i⟩ := a
  obtain ⟨y, j⟩ := b
  have hh := two_mul_half k
  by_cases hij : i = j
  · subst hij
    by_cases hxy : x = y
    · subst hxy; simp [boseT]
    · have hne : x ≠ ((k + 1 : ℕ) : ZMod (2 * k + 1)) * (x + y) := by
        intro he; apply hxy
        linear_combination 2 * he + (x + y) * hh
      rw [boseT_L1 k i hxy, boseT_L3 k hne rfl]
      congr 1
      linear_combination (x + y) * hh
  · obtain ⟨h1, -, h3, -, h5⟩ := z3_facts i j hij
    by_cases hxy : x = y
    · subst hxy; rw [boseT_L2 k x hij, boseT_L2 k x h3.symm, h5]
    · rcases h1 with h1 | h1
      · have hne : x ≠ 2 * y - x := by
          intro he; apply hxy; apply two_cancel k; linear_combination he
        rw [boseT_L3 k hxy h1, boseT_L1 k i hne, h1]
        congr 1
        linear_combination y * hh
      · have hne : x ≠ 2 * x - y := by
          intro he; apply hxy; linear_combination -he
        rw [boseT_L4 k hxy h1, boseT_L4 k hne h1]
        congr 1; ring

/-- **Kirkman's theorem for `n ≡ 3 (mod 6)`** (Bose's construction). -/
theorem exists_steinerTripleSystem_six_mul_add_three :
    ∃ 𝒮 : Finset (Finset (Fin (6 * k + 3))), IsSteinerSystem 3 2 𝒮 :=
  exists_steinerSystem_of_quasigroup (boseT k) (boseT_self k) (boseT_comm k) (boseT_invol k)
    (by simp [ZMod.card]; ring)

end Bose

/-! ### Skolem's construction: `n = 6k + 1` -/

section Skolem

variable (k : ℕ)

instance skolemNeZero : NeZero (2 * (k + 1)) := ⟨by omega⟩

/-- The bijection `τ` of `ℤ_{2m}` (`m = k + 1`) with `τ(i) = 2i`, `τ(m + i) = 2i + 1` for
`0 ≤ i < m`. -/
def tauS (z : ZMod (2 * (k + 1))) : ZMod (2 * (k + 1)) :=
  ((if z.val < k + 1 then 2 * z.val else 2 * (z.val - (k + 1)) + 1 : ℕ) : ZMod (2 * (k + 1)))

/-- The inverse `σ` of `τ`.  The operation `x ∘ y = σ(x + y)` is the half-idempotent
commutative quasigroup on `ℤ_{2m}` used by Skolem. -/
def sigS (z : ZMod (2 * (k + 1))) : ZMod (2 * (k + 1)) :=
  ((if z.val % 2 = 0 then z.val / 2 else z.val / 2 + (k + 1) : ℕ) : ZMod (2 * (k + 1)))

theorem val_tauS (z : ZMod (2 * (k + 1))) : (tauS k z).val =
    if z.val < k + 1 then 2 * z.val else 2 * (z.val - (k + 1)) + 1 := by
  have := ZMod.val_lt z
  unfold tauS; rw [ZMod.val_natCast_of_lt]; split_ifs <;> omega

theorem val_sigS (z : ZMod (2 * (k + 1))) : (sigS k z).val =
    if z.val % 2 = 0 then z.val / 2 else z.val / 2 + (k + 1) := by
  have := ZMod.val_lt z
  unfold sigS; rw [ZMod.val_natCast_of_lt]; split_ifs <;> omega

theorem sigS_tauS (z : ZMod (2 * (k + 1))) : sigS k (tauS k z) = z := by
  apply ZMod.val_injective
  rw [val_sigS, val_tauS]
  have := ZMod.val_lt z
  split_ifs <;> omega

theorem tauS_sigS (z : ZMod (2 * (k + 1))) : tauS k (sigS k z) = z := by
  apply ZMod.val_injective
  rw [val_tauS, val_sigS]
  have := ZMod.val_lt z
  split_ifs <;> omega

theorem sigS_inj {a b : ZMod (2 * (k + 1))} (h : sigS k a = sigS k b) : a = b := by
  rw [← tauS_sigS k a, h, tauS_sigS]

theorem two_mul_K : (2 : ZMod (2 * (k + 1))) * ((k : ZMod (2 * (k + 1))) + 1) = 0 := by
  have : ((2 * (k + 1) : ℕ) : ZMod (2 * (k + 1))) = 0 := ZMod.natCast_self _
  push_cast at this; exact this

theorem val_add_K (x : ZMod (2 * (k + 1))) : (x + ((k : ZMod (2 * (k + 1))) + 1)).val =
    if x.val < k + 1 then x.val + (k + 1) else x.val - (k + 1) := by
  have := ZMod.val_lt x
  have hK : ((k : ZMod (2 * (k + 1))) + 1) = ((k + 1 : ℕ) : ZMod (2 * (k + 1))) := by push_cast; rfl
  rw [hK, ZMod.val_add, ZMod.val_natCast_of_lt (by omega)]
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem add_K_add_K (x : ZMod (2 * (k + 1))) :
    x + ((k : ZMod (2 * (k + 1))) + 1) + ((k : ZMod (2 * (k + 1))) + 1) = x := by
  linear_combination two_mul_K k

theorem sigS_two_mul_of_lt {x : ZMod (2 * (k + 1))} (h : x.val < k + 1) :
    sigS k (2 * x) = x := by
  have : tauS k x = 2 * x := by
    unfold tauS; rw [if_pos h]; push_cast; rw [ZMod.natCast_zmod_val]
  rw [← this, sigS_tauS]

theorem sigS_two_mul_of_ge {x : ZMod (2 * (k + 1))} (h : ¬ x.val < k + 1) :
    sigS k (2 * x) = x + ((k : ZMod (2 * (k + 1))) + 1) := by
  have hv := val_add_K k x
  rw [if_neg h] at hv
  have : tauS k (x + ((k : ZMod (2 * (k + 1))) + 1)) = 2 * x := by
    unfold tauS
    rw [if_pos (by rw [hv]; have := ZMod.val_lt x; omega)]
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination two_mul_K k
  rw [← this, sigS_tauS]

/-- Skolem's Steiner quasigroup on `{∞} ∪ ℤ_{2m} × ℤ_3` (with `∞ = none`).  Its blocks are
`{(x,0),(x,1),(x,2)}` and `{∞, (x+m, i), (x, i+1)}` for `0 ≤ x < m`, and
`{(x,i), (y,i), (x ∘ y, i+1)}` for `x ≠ y`. -/
def skolemT : Option (ZMod (2 * (k + 1)) × ZMod 3) → Option (ZMod (2 * (k + 1)) × ZMod 3) →
    Option (ZMod (2 * (k + 1)) × ZMod 3)
  | none, none => none
  | none, some (z, i) => some (z + ((k : ZMod (2 * (k + 1))) + 1),
      if z.val < k + 1 then i - 1 else i + 1)
  | some (z, i), none => some (z + ((k : ZMod (2 * (k + 1))) + 1),
      if z.val < k + 1 then i - 1 else i + 1)
  | some (x, i), some (y, j) =>
    if i = j then (if x = y then some (x, i) else some (sigS k (x + y), i + 1))
    else if j = i + 1 then
      (if y = sigS k (2 * x) then (if x.val < k + 1 then some (x, i + 2) else none)
       else some (tauS k y - x, i))
    else
      (if x = sigS k (2 * y) then (if y.val < k + 1 then some (y, j + 2) else none)
       else some (tauS k x - y, j))

theorem z3_skolem : ∀ i : ZMod 3, i + 1 ≠ i ∧ i - 1 ≠ i ∧ i + 2 ≠ i ∧ i - 1 ≠ i + 1 ∧
    i - 1 + 1 = i ∧ i + 1 - 1 = i ∧ i + 2 = i - 1 ∧ i + 2 + 2 = i + 1 ∧ i + 1 + 2 = i ∧
    ¬ (i + 1 = i + 1 + 1) := by decide

theorem skolemT_none_some (z : ZMod (2 * (k + 1))) (i : ZMod 3) :
    skolemT k none (some (z, i)) = some (z + ((k : ZMod (2 * (k + 1))) + 1),
      if z.val < k + 1 then i - 1 else i + 1) := rfl

theorem skolemT_some_none (z : ZMod (2 * (k + 1))) (i : ZMod 3) :
    skolemT k (some (z, i)) none = some (z + ((k : ZMod (2 * (k + 1))) + 1),
      if z.val < k + 1 then i - 1 else i + 1) := rfl

theorem skolemT_same {x y : ZMod (2 * (k + 1))} (i : ZMod 3) (hxy : x ≠ y) :
    skolemT k (some (x, i)) (some (y, i)) = some (sigS k (x + y), i + 1) := by
  simp [skolemT, hxy]

theorem skolemT_up {x w : ZMod (2 * (k + 1))} (i : ZMod 3) :
    skolemT k (some (x, i)) (some (w, i + 1)) =
      if w = sigS k (2 * x) then (if x.val < k + 1 then some (x, i + 2) else none)
      else some (tauS k w - x, i) := by
  simp [skolemT, (z3_skolem i).1.symm]

theorem skolemT_down {x w : ZMod (2 * (k + 1))} (i : ZMod 3) :
    skolemT k (some (w, i + 1)) (some (x, i)) =
      if w = sigS k (2 * x) then (if x.val < k + 1 then some (x, i + 2) else none)
      else some (tauS k w - x, i) := by
  have h1 := (z3_skolem i).1
  have h2 : ¬ i = i + 1 + 1 := by revert i; decide
  simp [skolemT, h1, h2]

end Skolem

section Skolem2

variable (k : ℕ)

theorem skolemT_up' {x w : ZMod (2 * (k + 1))} {i j : ZMod 3} (h : j = i + 1) :
    skolemT k (some (x, i)) (some (w, j)) =
      if w = sigS k (2 * x) then (if x.val < k + 1 then some (x, i + 2) else none)
      else some (tauS k w - x, i) := by
  subst h; exact skolemT_up k i

theorem skolemT_down' {x w : ZMod (2 * (k + 1))} {i j : ZMod 3} (h : i = j + 1) :
    skolemT k (some (w, i)) (some (x, j)) =
      if w = sigS k (2 * x) then (if x.val < k + 1 then some (x, j + 2) else none)
      else some (tauS k w - x, j) := by
  subst h; exact skolemT_down k j

theorem z3_two : ∀ i j : ZMod 3, i ≠ j → (j = i + 1 ∨ i = j + 1) := by decide

theorem z3_a : ∀ i : ZMod 3, i + 2 + 2 = i + 1 := by decide
theorem z3_c : ∀ i : ZMod 3, i = i + 2 + 1 := by decide
theorem z3_d : ∀ j : ZMod 3, j + 1 + 2 = j := by decide
theorem z3_e : ∀ i : ZMod 3, i = i - 1 + 1 := by decide

theorem skolemT_self (a) : skolemT k a a = a := by
  rcases a with _ | ⟨x, i⟩
  · rfl
  · simp [skolemT]

theorem skolemT_comm (a b) : skolemT k a b = skolemT k b a := by
  rcases a with _ | ⟨x, i⟩ <;> rcases b with _ | ⟨y, j⟩
  · rfl
  · rfl
  · rfl
  · by_cases hij : i = j
    · subst hij
      by_cases hxy : x = y
      · subst hxy; rfl
      · rw [skolemT_same k i hxy, skolemT_same k i (Ne.symm hxy), add_comm x]
    · rcases z3_two i j hij with h | h
      · rw [skolemT_up' k h, skolemT_down' k h]
      · rw [skolemT_down' k h, skolemT_up' k h]

theorem skolemT_invol (a b) : skolemT k a (skolemT k a b) = b := by
  have hK := two_mul_K k
  rcases a with _ | ⟨x, i⟩ <;> rcases b with _ | ⟨y, j⟩
  · rfl
  · -- a = ∞, b = (y, j)
    rw [skolemT_none_some, skolemT_none_some, add_K_add_K, val_add_K]
    by_cases hy : y.val < k + 1
    · have h' : ¬ (y.val + (k + 1) < k + 1) := by omega
      simp only [hy, h', if_true, if_false]
      congr 2; revert j; decide
    · have h' : y.val - (k + 1) < k + 1 := by have := ZMod.val_lt y; omega
      simp only [hy, h', if_true, if_false]
      congr 2; revert j; decide
  · -- a = (x, i), b = ∞
    rw [skolemT_some_none]
    by_cases hx : x.val < k + 1
    · rw [if_pos hx, skolemT_down' k (z3_e i)]
      have h1 : x = sigS k (2 * (x + ((k : ZMod (2 * (k + 1))) + 1))) := by
        rw [show 2 * (x + ((k : ZMod (2 * (k + 1))) + 1)) = 2 * x by linear_combination hK,
          sigS_two_mul_of_lt k hx]
      rw [if_pos h1, if_neg (by rw [val_add_K, if_pos hx]; omega)]
    · rw [if_neg hx, skolemT_up' k rfl, if_pos (sigS_two_mul_of_ge k hx).symm, if_neg hx]
  · by_cases hij : i = j
    · subst hij
      by_cases hxy : x = y
      · subst hxy; rw [skolemT_self, skolemT_self]
      · rw [skolemT_same k i hxy, skolemT_up' k rfl]
        have hne : sigS k (x + y) ≠ sigS k (2 * x) := by
          intro h; apply hxy; have := sigS_inj k h; linear_combination -this
        rw [if_neg hne, tauS_sigS]; congr 2; ring
    · rcases z3_two i j hij with h | h
      · rw [skolemT_up' k h]
        by_cases hy : y = sigS k (2 * x)
        · rw [if_pos hy]
          by_cases hx : x.val < k + 1
          · rw [if_pos hx, skolemT_down' k (z3_c i),
              if_pos (sigS_two_mul_of_lt k hx).symm, if_pos hx, h, hy, sigS_two_mul_of_lt k hx,
              z3_a]
          · rw [if_neg hx, skolemT_some_none, if_neg hx, hy, sigS_two_mul_of_ge k hx, h]
        · rw [if_neg hy]
          have hne : x ≠ tauS k y - x := by
            intro he; apply hy
            rw [show 2 * x = tauS k y by linear_combination 2 * he - he, sigS_tauS]
          rw [skolemT_same k i hne, show x + (tauS k y - x) = tauS k y by ring, sigS_tauS, h]
      · rw [skolemT_down' k h]
        by_cases hx : x = sigS k (2 * y)
        · rw [if_pos hx]
          by_cases hy : y.val < k + 1
          · rw [if_pos hy, sigS_two_mul_of_lt k hy] at *
            subst hx
            rw [skolemT_up' k (by rw [h]; ring : j + 2 = i + 1), if_pos (sigS_two_mul_of_lt k hy).symm,
              if_pos hy, h]
            congr 2; exact z3_d j
          · rw [if_neg hy, skolemT_some_none, hx, sigS_two_mul_of_ge k hy, val_add_K, if_neg hy,
              if_pos (by have := ZMod.val_lt y; omega), add_K_add_K, h]
            congr 2; ring
        · rw [if_neg hx]
          have hne : x ≠ sigS k (2 * (tauS k x - y)) := by
            intro he; apply hx
            have h2 := congrArg (tauS k) he
            rw [tauS_sigS] at h2
            rw [show 2 * y = tauS k x by linear_combination h2, sigS_tauS]
          rw [skolemT_down' k h, if_neg hne]
          congr 2; ring

/-- **Kirkman's theorem for `n ≡ 1 (mod 6)`** (Skolem's construction). -/
theorem exists_steinerTripleSystem_six_mul_add_one :
    ∃ 𝒮 : Finset (Finset (Fin (6 * k + 1))), IsSteinerSystem 3 2 𝒮 := by
  rcases k with _ | k
  · refine ⟨∅, fun B hB => by simp at hB, fun T hT => ?_⟩
    exfalso
    have := Finset.card_le_univ T
    simp at this; omega
  · exact exists_steinerSystem_of_quasigroup (skolemT k) (skolemT_self k) (skolemT_comm k)
      (skolemT_invol k) (by simp [ZMod.card]; ring)

end Skolem2

/-- **Kirkman's theorem** (1847): a Steiner triple system on `n` points exists whenever
`n ≡ 1, 3 (mod 6)`. -/
theorem kirkmanTheorem : KirkmanTheorem := by
  intro n hn
  rcases hn with hn | hn
  · obtain ⟨k, rfl⟩ : ∃ k, n = 6 * k + 1 := ⟨n / 6, by omega⟩
    exact exists_steinerTripleSystem_six_mul_add_one k
  · obtain ⟨k, rfl⟩ : ∃ k, n = 6 * k + 3 := ⟨n / 6, by omega⟩
    exact exists_steinerTripleSystem_six_mul_add_three k

/-- **Kirkman's theorem, both directions.**  For `n ≥ 1`, there is a Steiner triple system on
`n` points if and only if `n ≡ 1` or `3 (mod 6)`. -/
theorem exists_steinerTripleSystem_iff {n : ℕ} (hn : 1 ≤ n) :
    (∃ 𝒮 : Finset (Finset (Fin n)), IsSteinerSystem 3 2 𝒮) ↔ n % 6 = 1 ∨ n % 6 = 3 := by
  constructor
  · rintro ⟨𝒮, h⟩
    simpa using h.mod_six (by simpa using hn)
  · exact kirkmanTheorem n

end RefinedAbsorption
