module
public import RefinedAbsorption.MultiRefiner.PieceDeg

/-!
# A counting bound for tagged refiners whose pieces sit in few small reserves

Mathematics: diagnosis of the open link levels `2 ≤ i < r - 1` (see the last section of
`LEDGER.md`).  Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

The staged construction of tagged refiners used at level `1` sends, at depth `t`, the residues of
all fibres into a family of pairwise disjoint reserves of size `|Z| / 4^t`.  If every fibre keeps
a piece whose span (at least `r - 1` vertices) lies inside the reserve of its class, then some
`(r-1)`-set is covered by many lifted pieces.  This is pure double counting:

* `exists_heavy_kset`: if `N` sets of size `≥ k` each lie inside one of `p` sets of size `≤ m`,
  some `k`-set lies in at least `N / (p · C(m, k))` of them;
* **`exists_heavy_pdeg`**: the same for the lifted piece degrees `∑_T pdeg (T ∪ ·) (𝒲 T) S` of
  tagged refiners.

With `N ≈ K² |Z|²` link fibres (all pairs of a set `U`, `|U| = K |Z|`, as tags, each fibre a
clique, lifted degree `D = O(1)`), `p ≤ |Z| / m` reserves of size `m` and `k = r - 1 = 3`, the
bound is of order `K² |Z| / m²`, which is not of the form `C_s D + B |Z| / 2^s` with `B`
independent of `s` once the reserve size `m` at the bottom of the recursion is bounded.
-/

@[expose] public section

namespace RefinedAbsorption.LinkSpread

open Finset

/-- **Double counting.**  If each of the sets `W x` (`x ∈ F`) has at least `k` elements and lies
inside one of the sets `Q j` (`j ∈ P`), each of size at most `m`, then some `k`-set lies in at
least `|F| / (|P| · C(m, k))` of the sets `W x`. -/
theorem exists_heavy_kset {α ι κ : Type*} [DecidableEq α] [DecidableEq κ] (F : Finset ι)
    (hF : F.Nonempty) (W : ι → Finset α) (P : Finset κ) (Q : κ → Finset α) (part : ι → κ)
    (hpart : ∀ x ∈ F, part x ∈ P) (hW : ∀ x ∈ F, W x ⊆ Q (part x)) (k m : ℕ)
    (hk : ∀ x ∈ F, k ≤ (W x).card) (hQ : ∀ j ∈ P, (Q j).card ≤ m) :
    ∃ S : Finset α, S.card = k ∧
      F.card ≤ P.card * m.choose k * (F.filter fun x => S ⊆ W x).card := by
  classical
  set 𝒮 := P.biUnion fun j => (Q j).powersetCard k with h𝒮
  -- every set `W x` contains a `k`-set of `𝒮`
  have hsub : ∀ x ∈ F, ∃ S ∈ 𝒮, S ⊆ W x := by
    intro x hx
    obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq (hk x hx)
    exact ⟨S, mem_biUnion.2 ⟨part x, hpart x hx,
      mem_powersetCard.2 ⟨hS.trans (hW x hx), hSc⟩⟩, hS⟩
  have h𝒮ne : 𝒮.Nonempty := by
    obtain ⟨x, hx⟩ := hF
    obtain ⟨S, hS, -⟩ := hsub x hx
    exact ⟨S, hS⟩
  obtain ⟨S₀, hS₀, hmax⟩ := exists_max_image 𝒮 (fun S => (F.filter fun x => S ⊆ W x).card) h𝒮ne
  have hS₀c : S₀.card = k := by
    obtain ⟨j, -, hj⟩ := mem_biUnion.1 hS₀
    exact (mem_powersetCard.1 hj).2
  refine ⟨S₀, hS₀c, ?_⟩
  have h𝒮c : 𝒮.card ≤ P.card * m.choose k := by
    refine card_biUnion_le.trans ?_
    calc ∑ j ∈ P, ((Q j).powersetCard k).card ≤ ∑ _j ∈ P, m.choose k :=
          sum_le_sum fun j hj => by
            rw [card_powersetCard]; exact Nat.choose_le_choose _ (hQ j hj)
      _ = P.card * m.choose k := by rw [sum_const, smul_eq_mul]
  -- `|F| ≤ ∑_{S ∈ 𝒮} #{x : S ⊆ W x}`
  have hcover : F.card ≤ ∑ S ∈ 𝒮, (F.filter fun x => S ⊆ W x).card := by
    calc F.card ≤ (𝒮.biUnion fun S => F.filter fun x => S ⊆ W x).card := by
          refine card_le_card fun x hx => ?_
          obtain ⟨S, hS, hSW⟩ := hsub x hx
          exact mem_biUnion.2 ⟨S, hS, mem_filter.2 ⟨hx, hSW⟩⟩
      _ ≤ _ := card_biUnion_le
  calc F.card ≤ ∑ S ∈ 𝒮, (F.filter fun x => S ⊆ W x).card := hcover
    _ ≤ ∑ _S ∈ 𝒮, (F.filter fun x => S₀ ⊆ W x).card := sum_le_sum fun S hS => hmax S hS
    _ = 𝒮.card * (F.filter fun x => S₀ ⊆ W x).card := by rw [sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ h𝒮c

/-- **Lifted piece degrees of tagged refiners whose pieces sit in few small reserves.**  Suppose
that for every tag `T ∈ Ts` one of its pieces `W T ∈ 𝒲 T` spans at least `r - 1` vertices, all
inside the reserve `Q (part T)` of its class, and that there are `|P|` reserves, each of size at
most `m`.  Then some `(r-1)`-set `S` has lifted piece degree, summed over all tags, at least
`|Ts| / (|P| · C(m, r-1))`. -/
theorem exists_heavy_pdeg {V E κ : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq κ]
    {r : ℕ} (Ts : Finset (Finset V)) (hTs : Ts.Nonempty) (ends : Finset V → E → Finset V)
    (𝒲 : Finset V → Finset (Finset E)) (W : Finset V → Finset E) (hW𝒲 : ∀ T ∈ Ts, W T ∈ 𝒲 T)
    (P : Finset κ) (Q : κ → Finset V) (part : Finset V → κ) (hpart : ∀ T ∈ Ts, part T ∈ P)
    (hspan : ∀ T ∈ Ts, (W T).biUnion (ends T) ⊆ Q (part T)) (m : ℕ)
    (hk : ∀ T ∈ Ts, r - 1 ≤ ((W T).biUnion (ends T)).card) (hQ : ∀ j ∈ P, (Q j).card ≤ m) :
    ∃ S : Finset V, S.card = r - 1 ∧
      Ts.card ≤ P.card * m.choose (r - 1) *
        ∑ T ∈ Ts, RefinedAbsorption.MultiRefiner.pdeg (fun c => T ∪ ends T c) (𝒲 T) S := by
  obtain ⟨S, hSc, hS⟩ := exists_heavy_kset Ts hTs (fun T => (W T).biUnion (ends T)) P Q part
    hpart hspan (r - 1) m hk hQ
  refine ⟨S, hSc, hS.trans (Nat.mul_le_mul_left _ ?_)⟩
  rw [card_eq_sum_ones, sum_filter]
  refine sum_le_sum fun T hT => ?_
  split_ifs with hST
  · unfold RefinedAbsorption.MultiRefiner.pdeg
    refine card_pos.2 ⟨W T, mem_filter.2 ⟨hW𝒲 T hT, hST.trans ?_⟩⟩
    exact biUnion_mono fun c _ => subset_union_right
  · exact Nat.zero_le _

end RefinedAbsorption.LinkSpread
