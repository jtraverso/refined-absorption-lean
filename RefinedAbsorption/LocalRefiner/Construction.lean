module
public import RefinedAbsorption.LocalRefiner.OwnedChains
public import RefinedAbsorption.LocalRefiner.Gadgets

/-!
# The local refiner at the level of labels

Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

For a graph `X` on `Fin n` we define the labels of the refiner and its pieces:

* for every edge `e ∈ X` a *switch*: `P1 e = {xe e, ae e}` (used when `e ∈ L`) and
  `P0 e = {ae e, ke e} ∪ {tk e u : u ∈ e}` (used when `e ∉ L`);
* for every vertex `u` its own chain refiner (`q = d`), whose inputs are the tokens `tk e u` of
  the edges at `u` and whose reservoir consists of further tokens `vb u i j` at `u`; it absorbs
  the tokens left over at `u`, which are `≡ 0 (mod d)` in number since `deg_L u ≡ 0`;
* one global chain refiner (`q = N`), the *connector*, whose inputs are the labels `ke e` and
  whose reservoir consists of labels `gb i j`; it absorbs the labels `ke e, e ∈ L`, which are
  `≡ 0 (mod N)` in number since `N ∣ |L|`.

`pc_cover` and `pc_unique` show that the chosen pieces partition the reservoir together with the
selected edges, for every `L ⊆ X` satisfying the divisibility conditions.
-/

@[expose] public section

namespace RefinedAbsorption.LocalRefiner

open Finset RefinedAbsorption.ChainRefiner RefinedAbsorption.MultiRefiner

variable {n : ℕ} [NeZero n]

section Defs

variable (k : ℕ) (X : Finset (Finset (Fin n)))

/-- The edges at `u`, listed. -/
noncomputable def lstU (u : Fin n) : List (Finset (Fin n)) := (X.filter (u ∈ ·)).toList

/-- Number of edges at `u`. -/
noncomputable def mU (u : Fin n) : ℕ := (lstU X u).length

/-- The `i`-th edge at `u`. -/
noncomputable def enU (u : Fin n) (i : ℕ) : Finset (Fin n) := (lstU X u).getD i ∅

/-- Number of edges. -/
noncomputable def mG (_ : Unit) : ℕ := X.toList.length

/-- The `i`-th edge. -/
noncomputable def enX (i : ℕ) : Finset (Fin n) := X.toList.getD i ∅

/-- The pair carrying the global block `i`. -/
noncomputable def gE (i : ℕ) : Finset (Fin n) := if i < X.toList.length then enX X i else {0, 1}

/-- Relabelling of the chain of vertex `u`. -/
noncomputable def φU (u : Fin n) : Lab → Lb n
  | Sum.inl i => .tk (enU X u i) u
  | Sum.inr ij => .vb u ij.1 ij.2

/-- Relabelling of the global chain. -/
noncomputable def φG (_ : Unit) : Lab → Lb n
  | Sum.inl i => .ke (enX X i)
  | Sum.inr ij => .gb ij.1 ij.2

/-- The switch piece used when `e ∈ L`. -/
def P1 (e : Finset (Fin n)) : Finset (Lb n) := {.xe e, .ae e}

/-- The switch piece used when `e ∉ L`. -/
def P0 (e : Finset (Fin n)) : Finset (Lb n) := insert (.ae e) (insert (.ke e) (e.image (.tk e)))

/-- The tokens of the edges. -/
def TL : Finset (Lb n) := X.biUnion fun e => e.image (.tk e)

/-- The labels of the refiner. -/
noncomputable def RL : Finset (Lb n) :=
  X.image .ae ∪ X.image .ke ∪ TL X ∪ chR (2 * k + 3) (mU X) (φU X) ∪
    chR ((k + 2) * (2 * k + 3)) (mG X) (φG X)

/-- The pieces. -/
noncomputable def WL : Finset (Finset (Lb n)) :=
  X.image P1 ∪ X.image P0 ∪ chFam (2 * k + 3) (mU X) (φU X) ∪
    chFam ((k + 2) * (2 * k + 3)) (mG X) (φG X)

variable (Ls : Finset (Finset (Fin n)))

/-- Selection of the chain of `u`. -/
noncomputable def bU (u : Fin n) (i : ℕ) : Bool := decide (enU X u i ∈ Ls)

/-- Selection of the global chain. -/
noncomputable def bG (_ : Unit) (i : ℕ) : Bool := decide (enX X i ∈ Ls)

/-- Indices of the chosen pieces. -/
abbrev PIdx (n : ℕ) := Finset (Fin n) ⊕ ((Fin n × ℕ) ⊕ (Unit × ℕ))

/-- The chosen pieces. -/
noncomputable def pc : PIdx n → Finset (Lb n)
  | Sum.inl e => if e ∈ Ls then P1 e else P0 e
  | Sum.inr (Sum.inl β) => chPc (2 * k + 3) (mU X) (φU X) (bU X Ls) β
  | Sum.inr (Sum.inr γ) => chPc ((k + 2) * (2 * k + 3)) (mG X) (φG X) (bG X Ls) γ

/-- The indices used. -/
noncomputable def Ind : Finset (PIdx n) := X.disjSum ((chInd (mU X)).disjSum (chInd (mG X)))

end Defs

variable {k : ℕ} {X : Finset (Finset (Fin n))}

/-! ### Enumerations -/

omit [NeZero n] in
lemma lstU_nodup (u : Fin n) : (lstU X u).Nodup := Finset.nodup_toList _

omit [NeZero n] in
lemma enU_spec {u : Fin n} {i : ℕ} (hi : i < mU X u) : enU X u i ∈ X ∧ u ∈ enU X u i := by
  have h : enU X u i ∈ lstU X u := by
    unfold enU; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  unfold lstU at h
  rw [Finset.mem_toList, mem_filter] at h
  exact h

omit [NeZero n] in
lemma enU_inj {u : Fin n} {i j : ℕ} (hi : i < mU X u) (hj : j < mU X u)
    (h : enU X u i = enU X u j) : i = j := by
  unfold enU at h
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (List.Nodup.getElem_inj_iff (lstU_nodup u)).1 h

omit [NeZero n] in
lemma exists_enU {u : Fin n} {e : Finset (Fin n)} (he : e ∈ X) (hu : u ∈ e) :
    ∃ i < mU X u, enU X u i = e := by
  have h : e ∈ lstU X u := by
    unfold lstU; rw [Finset.mem_toList, mem_filter]; exact ⟨he, hu⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, hi, by unfold enU; rw [List.getD_eq_getElem _ _ hi]⟩

omit [NeZero n] in
lemma enX_mem {i : ℕ} (hi : i < mG X ()) : enX X i ∈ X := by
  have h : enX X i ∈ X.toList := by
    unfold enX; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  exact Finset.mem_toList.1 h

omit [NeZero n] in
lemma enX_inj {i j : ℕ} (hi : i < mG X ()) (hj : j < mG X ()) (h : enX X i = enX X j) :
    i = j := by
  unfold enX at h
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (List.Nodup.getElem_inj_iff (Finset.nodup_toList X)).1 h

omit [NeZero n] in
lemma exists_enX {e : Finset (Fin n)} (he : e ∈ X) : ∃ i < mG X (), enX X i = e := by
  have h : e ∈ X.toList := Finset.mem_toList.2 he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, hi, by unfold enX; rw [List.getD_eq_getElem _ _ hi]⟩

omit [NeZero n] in
lemma mG_eq : mG X () = X.card := Finset.length_toList X

/-- Counting the selected inputs of a chain. -/
lemma cnt_eq_card_filter (b : ℕ → Bool) (m : ℕ) : cnt b m = ((range m).filter (b ·)).card := by
  rw [cnt_eq_card, Llab, card_image_of_injective _ (fun a b h => xl_inj.1 h)]

omit [NeZero n] in
lemma cnt_bU {Ls : Finset (Finset (Fin n))} (hLs : Ls ⊆ X) (u : Fin n) :
    cnt (bU X Ls u) (mU X u) = (Ls.filter (u ∈ ·)).card := by
  rw [cnt_eq_card_filter]
  apply card_bij (fun i _ => enU X u i)
  · intro i hi
    simp only [mem_filter, mem_range, bU, decide_eq_true_eq] at hi
    exact mem_filter.2 ⟨hi.2, (enU_spec hi.1).2⟩
  · intro i hi j hj h
    simp only [mem_filter, mem_range] at hi hj
    exact enU_inj hi.1 hj.1 h
  · intro e he
    rw [mem_filter] at he
    obtain ⟨i, hi, rfl⟩ := exists_enU (hLs he.1) he.2
    exact ⟨i, by simp [bU, hi, he.1], rfl⟩

omit [NeZero n] in
lemma cnt_bG {Ls : Finset (Finset (Fin n))} (hLs : Ls ⊆ X) :
    cnt (bG X Ls ()) (mG X ()) = Ls.card := by
  rw [cnt_eq_card_filter]
  apply card_bij (fun i _ => enX X i)
  · intro i hi
    simp only [mem_filter, mem_range, bG, decide_eq_true_eq] at hi
    exact hi.2
  · intro i hi j hj h
    simp only [mem_filter, mem_range] at hi hj
    exact enX_inj hi.1 hj.1 h
  · intro e he
    obtain ⟨i, hi, rfl⟩ := exists_enX (hLs he)
    exact ⟨i, by simp [bG, hi, he], rfl⟩

/-! ### Injectivity of the relabellings -/

omit [NeZero n] in
lemma chInj_U : ChInj (2 * k + 3) (mU X) (φU X) := by
  intro u u' a a' ha ha' h
  rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩ <;>
    rcases lab_cases a' with ⟨i', rfl⟩ | ⟨i', j', rfl⟩
  · simp only [φU, xl, Lb.tk.injEq] at h
    obtain ⟨he, rfl⟩ := h
    refine ⟨rfl, ?_⟩
    rw [mem_Ulab_xl] at ha ha'
    rw [enU_inj ha ha' he]
  · simp [φU, xl, zl] at h
  · simp [φU, xl, zl] at h
  · simp only [φU, zl, Lb.vb.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

omit [NeZero n] in
lemma chInj_G : ChInj ((k + 2) * (2 * k + 3)) (mG X) (φG X) := by
  intro u u' a a' ha ha' h
  rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩ <;>
    rcases lab_cases a' with ⟨i', rfl⟩ | ⟨i', j', rfl⟩
  · simp only [φG, xl, Lb.ke.injEq] at h
    refine ⟨rfl, ?_⟩
    rw [mem_Ulab_xl] at ha ha'
    rw [enX_inj ha ha' h]
  · simp [φG, xl, zl] at h
  · simp [φG, xl, zl] at h
  · simp only [φG, zl, Lb.gb.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

/-! ### The labels of the chain pieces -/

lemma hqU : 1 ≤ 2 * k + 3 := by omega

lemma hqG : 1 ≤ (k + 2) * (2 * k + 3) := Nat.one_le_iff_ne_zero.2 (by positivity)

omit [NeZero n] in
lemma chPcU_cases {Ls : Finset (Finset (Fin n))} {β : Fin n × ℕ} {g : Lb n}
    (hg : g ∈ chPc (2 * k + 3) (mU X) (φU X) (bU X Ls) β) :
    (∃ i < mU X β.1, g = .tk (enU X β.1 i) β.1 ∧ enU X β.1 i ∈ Ls) ∨
      ∃ i j, g = .vb β.1 i j := by
  obtain ⟨a, ha, rfl, hsel⟩ := chPc_sel hqU _ β g hg
  rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · left
    have := hsel i rfl
    simp only [bU, decide_eq_true_eq] at this
    exact ⟨i, mem_Ulab_xl.1 ha, rfl, this⟩
  · right; exact ⟨i, j, rfl⟩

omit [NeZero n] in
lemma chPcG_cases {Ls : Finset (Finset (Fin n))} {γ : Unit × ℕ} {g : Lb n}
    (hg : g ∈ chPc ((k + 2) * (2 * k + 3)) (mG X) (φG X) (bG X Ls) γ) :
    (∃ i < mG X (), g = .ke (enX X i) ∧ enX X i ∈ Ls) ∨ ∃ i j, g = .gb i j := by
  obtain ⟨a, ha, rfl, hsel⟩ := chPc_sel hqG _ γ g hg
  rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · left
    have := hsel i rfl
    simp only [bG, decide_eq_true_eq] at this
    exact ⟨i, mem_Ulab_xl.1 ha, rfl, this⟩
  · right; exact ⟨i, j, rfl⟩

omit [NeZero n] in
lemma mem_P1 {e : Finset (Fin n)} {g : Lb n} : g ∈ P1 e ↔ g = .xe e ∨ g = .ae e := by
  simp [P1]

omit [NeZero n] in
lemma mem_P0 {e : Finset (Fin n)} {g : Lb n} :
    g ∈ P0 e ↔ g = .ae e ∨ g = .ke e ∨ ∃ u ∈ e, g = .tk e u := by
  simp only [P0, mem_insert, mem_image]
  constructor
  · rintro (h | h | ⟨u, hu, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨u, hu, rfl⟩)
  · rintro (h | h | ⟨u, hu, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨u, hu, rfl⟩)

/-- The edge carried by a label (`∅` for the chain reservoirs). -/
def lbE : Lb n → Finset (Fin n)
  | .xe e => e
  | .ae e => e
  | .tk e _ => e
  | .ke e => e
  | .vb _ _ _ => ∅
  | .gb _ _ => ∅

omit [NeZero n] in
lemma pcS_cases {Ls : Finset (Finset (Fin n))} {e : Finset (Fin n)} {g : Lb n}
    (hg : g ∈ pc k X Ls (Sum.inl e)) :
    lbE g = e ∧ ((g = .xe e ∧ e ∈ Ls) ∨ g = .ae e ∨
      ((g = .ke e ∨ ∃ u ∈ e, g = .tk e u) ∧ e ∉ Ls)) := by
  simp only [pc] at hg
  split_ifs at hg with h
  · rcases mem_P1.1 hg with rfl | rfl
    · exact ⟨rfl, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨rfl, Or.inr (Or.inl rfl)⟩
  · rcases mem_P0.1 hg with rfl | rfl | ⟨u, hu, rfl⟩
    · exact ⟨rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨rfl, Or.inr (Or.inr ⟨Or.inl rfl, h⟩)⟩
    · exact ⟨rfl, Or.inr (Or.inr ⟨Or.inr ⟨u, hu, rfl⟩, h⟩)⟩

/-! ### The partition -/

omit [NeZero n] in
lemma mem_Ind {α : PIdx n} : α ∈ Ind X ↔ match α with
    | Sum.inl e => e ∈ X
    | Sum.inr (Sum.inl β) => β ∈ chInd (mU X)
    | Sum.inr (Sum.inr γ) => γ ∈ chInd (mG X) := by
  rcases α with e | β | γ <;> simp [Ind]

omit [NeZero n] in
theorem pc_mem_WL (Ls : Finset (Finset (Fin n))) {α : PIdx n} (hα : α ∈ Ind X) :
    pc k X Ls α ∈ WL k X := by
  rw [mem_Ind] at hα
  rcases α with e | β | γ
  · simp only [pc, WL, mem_union, mem_image]
    split_ifs
    · exact Or.inl (Or.inl (Or.inl ⟨e, hα, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨e, hα, rfl⟩))
  · exact mem_union_left _ (mem_union_right _ (chPc_mem hqU _ hα))
  · exact mem_union_right _ (chPc_mem hqG _ hα)

omit [NeZero n] in
/-- **Uniqueness.** -/
theorem pc_unique {Ls : Finset (Finset (Fin n))} (hLs : Ls ⊆ X)
    (hdivU : ∀ u, 2 * k + 3 ∣ (Ls.filter (u ∈ ·)).card)
    (hdivG : (k + 2) * (2 * k + 3) ∣ Ls.card)
    {α β : PIdx n} (hα : α ∈ Ind X) (hβ : β ∈ Ind X) {g : Lb n}
    (h1 : g ∈ pc k X Ls α) (h2 : g ∈ pc k X Ls β) : α = β := by
  have hdU : ∀ u, 2 * k + 3 ∣ cnt (bU X Ls u) (mU X u) := fun u => by
    rw [cnt_bU hLs]; exact hdivU u
  have hdG : ∀ o, (k + 2) * (2 * k + 3) ∣ cnt (bG X Ls o) (mG X o) := fun o => by
    rw [cnt_bG hLs]; exact hdivG
  rw [mem_Ind] at hα hβ
  rcases α with e | β1 | γ1 <;> rcases β with e' | β2 | γ2
  · obtain ⟨h1e, -⟩ := pcS_cases h1
    obtain ⟨h2e, -⟩ := pcS_cases h2
    rw [← h1e, ← h2e]
  · exfalso
    obtain ⟨-, h1c⟩ := pcS_cases h1
    rcases chPcU_cases (Ls := Ls) h2 with ⟨i, -, rfl, hin⟩ | ⟨i, j, rfl⟩
    · rcases h1c with ⟨h, -⟩ | h | ⟨h | ⟨u, -, h⟩, hn⟩
      · cases h
      · cases h
      · cases h
      · simp only [Lb.tk.injEq] at h
        exact hn (h.1 ▸ hin)
    · rcases h1c with ⟨h, -⟩ | h | ⟨h | ⟨u, -, h⟩, -⟩ <;> cases h
  · exfalso
    obtain ⟨-, h1c⟩ := pcS_cases h1
    rcases chPcG_cases (Ls := Ls) h2 with ⟨i, -, rfl, hin⟩ | ⟨i, j, rfl⟩
    · rcases h1c with ⟨h, -⟩ | h | ⟨h | ⟨u, -, h⟩, hn⟩
      · cases h
      · cases h
      · simp only [Lb.ke.injEq] at h
        exact hn (h ▸ hin)
      · cases h
    · rcases h1c with ⟨h, -⟩ | h | ⟨h | ⟨u, -, h⟩, -⟩ <;> cases h
  · exfalso
    obtain ⟨-, h2c⟩ := pcS_cases h2
    rcases chPcU_cases (Ls := Ls) h1 with ⟨i, -, rfl, hin⟩ | ⟨i, j, rfl⟩
    · rcases h2c with ⟨h, -⟩ | h | ⟨h | ⟨u, -, h⟩, hn⟩
      · cases h
      · cases h
      · cases h
      · simp only [Lb.tk.injEq] at h
        exact hn (h.1 ▸ hin)
    · rcases h2c with ⟨h, -⟩ | h | ⟨h | ⟨u, -, h⟩, -⟩ <;> cases h
  · exact congrArg (Sum.inr ∘ Sum.inl) (chUnique hqU chInj_U _ hdU hα hβ h1 h2)
  · exfalso
    rcases chPcU_cases (Ls := Ls) h1 with ⟨i, -, rfl, -⟩ | ⟨i, j, rfl⟩ <;>
      rcases chPcG_cases (Ls := Ls) h2 with ⟨i', -, h, -⟩ | ⟨i', j', h⟩ <;> cases h
  · exfalso
    obtain ⟨-, h2c⟩ := pcS_cases h2
    rcases chPcG_cases (Ls := Ls) h1 with ⟨i, -, rfl, hin⟩ | ⟨i, j, rfl⟩
    · rcases h2c with ⟨h, -⟩ | h | ⟨h | ⟨u, -, h⟩, hn⟩
      · cases h
      · cases h
      · simp only [Lb.ke.injEq] at h
        exact hn (h ▸ hin)
      · cases h
    · rcases h2c with ⟨h, -⟩ | h | ⟨h | ⟨u, -, h⟩, -⟩ <;> cases h
  · exfalso
    rcases chPcU_cases (Ls := Ls) h2 with ⟨i, -, rfl, -⟩ | ⟨i, j, rfl⟩ <;>
      rcases chPcG_cases (Ls := Ls) h1 with ⟨i', -, h, -⟩ | ⟨i', j', h⟩ <;> cases h
  · exact congrArg (Sum.inr ∘ Sum.inr) (chUnique hqG chInj_G _ hdG hα hβ h1 h2)

omit [NeZero n] in
lemma chX_U_subset : chX (mU X) (φU X) ⊆ TL X := by
  intro g hg
  simp only [chX, mem_biUnion, mem_univ, true_and, mem_image] at hg
  obtain ⟨u, a, ha, rfl⟩ := hg
  rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · have hi := mem_Xlab_xl.1 ha
    obtain ⟨he, hu⟩ := enU_spec hi
    simp only [TL, mem_biUnion, mem_image]
    exact ⟨_, he, u, hu, rfl⟩
  · exact absurd ha not_mem_Xlab_zl

omit [NeZero n] in
lemma chX_G_subset : chX (mG X) (φG X) ⊆ X.image .ke := by
  intro g hg
  simp only [chX, mem_biUnion, mem_univ, true_and, mem_image] at hg
  obtain ⟨u, a, ha, rfl⟩ := hg
  rcases lab_cases a with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · exact mem_image.2 ⟨_, enX_mem (mem_Xlab_xl.1 ha), rfl⟩
  · exact absurd ha not_mem_Xlab_zl

omit [NeZero n] in
lemma mem_RL {g : Lb n} : g ∈ RL k X ↔ g ∈ X.image .ae ∨ g ∈ X.image .ke ∨ g ∈ TL X ∨
    g ∈ chR (2 * k + 3) (mU X) (φU X) ∨ g ∈ chR ((k + 2) * (2 * k + 3)) (mG X) (φG X) := by
  simp only [RL, mem_union, or_assoc]

/-- **Covering.** -/
theorem pc_cover {Ls : Finset (Finset (Fin n))} (hLs : Ls ⊆ X)
    (hdivU : ∀ u, 2 * k + 3 ∣ (Ls.filter (u ∈ ·)).card)
    (hdivG : (k + 2) * (2 * k + 3) ∣ Ls.card) (g : Lb n) :
    (∃ α ∈ Ind X, g ∈ pc k X Ls α) ↔ g ∈ RL k X ∪ Ls.image .xe := by
  have hdU : ∀ u, 2 * k + 3 ∣ cnt (bU X Ls u) (mU X u) := fun u => by
    rw [cnt_bU hLs]; exact hdivU u
  have hdG : ∀ o, (k + 2) * (2 * k + 3) ∣ cnt (bG X Ls o) (mG X o) := fun o => by
    rw [cnt_bG hLs]; exact hdivG
  have covU := chCover (φ := φU X) hqU (bU X Ls) hdU
  have covG := chCover (φ := φG X) hqG (bG X Ls) hdG
  rw [mem_union, mem_RL]
  constructor
  · rintro ⟨α, hα, hg⟩
    rw [mem_Ind] at hα
    rcases α with e | β | γ
    · simp only [pc] at hg
      split_ifs at hg with h
      · rcases mem_P1.1 hg with rfl | rfl
        · exact Or.inr (mem_image_of_mem _ h)
        · exact Or.inl (Or.inl (mem_image_of_mem _ hα))
      · rcases mem_P0.1 hg with rfl | rfl | ⟨u, hu, rfl⟩
        · exact Or.inl (Or.inl (mem_image_of_mem _ hα))
        · exact Or.inl (Or.inr (Or.inl (mem_image_of_mem _ hα)))
        · refine Or.inl (Or.inr (Or.inr (Or.inl ?_)))
          simp only [TL, mem_biUnion, mem_image]
          exact ⟨e, hα, u, hu, rfl⟩
    · have := (covU g).1 ⟨β, hα, hg⟩
      rcases mem_union.1 this with h | h
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (chX_U_subset (chL_subset _ h)))))
    · have := (covG g).1 ⟨γ, hα, hg⟩
      rcases mem_union.1 this with h | h
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact Or.inl (Or.inr (Or.inl
          (chX_G_subset (chL_subset _ h))))
  · rintro ((h | h | h | h | h) | h)
    · obtain ⟨e, he, rfl⟩ := mem_image.1 h
      refine ⟨Sum.inl e, mem_Ind.2 he, ?_⟩
      simp only [pc]; split_ifs <;> simp [P1, P0]
    · obtain ⟨e, he, rfl⟩ := mem_image.1 h
      by_cases hL : e ∈ Ls
      · obtain ⟨i, hi, rfl⟩ := exists_enX he
        have hmem : (Lb.ke (enX X i) : Lb n) ∈ chR ((k + 2) * (2 * k + 3)) (mG X) (φG X) ∪
            chL (mG X) (φG X) (bG X Ls) := by
          refine mem_union_right _ ?_
          simp only [chL, mem_biUnion, mem_univ, true_and, mem_image]
          exact ⟨(), xl i, mem_Llab_xl.2 ⟨hi, by simp [bG, hL]⟩, rfl⟩
        obtain ⟨γ, hγ, hg⟩ := (covG _).2 hmem
        exact ⟨Sum.inr (Sum.inr γ), mem_Ind.2 hγ, hg⟩
      · refine ⟨Sum.inl e, mem_Ind.2 he, ?_⟩
        simp only [pc, if_neg hL]; simp [P0]
    · simp only [TL, mem_biUnion, mem_image] at h
      obtain ⟨e, he, u, hu, rfl⟩ := h
      by_cases hL : e ∈ Ls
      · obtain ⟨i, hi, rfl⟩ := exists_enU he hu
        have hmem : (Lb.tk (enU X u i) u : Lb n) ∈ chR (2 * k + 3) (mU X) (φU X) ∪
            chL (mU X) (φU X) (bU X Ls) := by
          refine mem_union_right _ ?_
          simp only [chL, mem_biUnion, mem_univ, true_and, mem_image]
          exact ⟨u, xl i, mem_Llab_xl.2 ⟨hi, by simp [bU, hL]⟩, rfl⟩
        obtain ⟨β, hβ, hg⟩ := (covU _).2 hmem
        exact ⟨Sum.inr (Sum.inl β), mem_Ind.2 hβ, hg⟩
      · refine ⟨Sum.inl e, mem_Ind.2 he, ?_⟩
        simp only [pc, if_neg hL]
        exact mem_P0.2 (Or.inr (Or.inr ⟨u, hu, rfl⟩))
    · obtain ⟨β, hβ, hg⟩ := (covU g).2 (mem_union_left _ h)
      exact ⟨Sum.inr (Sum.inl β), mem_Ind.2 hβ, hg⟩
    · obtain ⟨γ, hγ, hg⟩ := (covG g).2 (mem_union_left _ h)
      exact ⟨Sum.inr (Sum.inr γ), mem_Ind.2 hγ, hg⟩
    · obtain ⟨e, he, rfl⟩ := mem_image.1 h
      exact ⟨Sum.inl e, mem_Ind.2 (hLs he), by simp [pc, he, P1]⟩

end RefinedAbsorption.LocalRefiner
