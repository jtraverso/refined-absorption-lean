module
public import RefinedAbsorption.Local.FlatEmbedMain
public import RefinedAbsorption.FlatOmni.Assembly

/-!
# Random embedding of flat local refiners, sparse form

Mathematics: M. Delcourt and L. Postle, arXiv:2402.17855, proof of Lemma 4.1 for `3`-graphs and
outside parts of size `1`, with the hypothesis `Δ ≤ n / C` of Theorem 3.7.
Lean formalization: Juan Pablo Traverso Gianini, Apache-2.0.

* `FlatGraphRefinersS q a`: `FlatGraphRefiners q a` with the extra hypothesis `Ch · d ≤ |P|`.
* **`flatGraphRefinersS_of_cliqueOmniS`**: sparse flat clique omni-absorbers are sparse flat local
  refiners (same proof as `flatGraphRefiners_of_cliqueOmni`).
* **`flatEmbedTaggedS`**: `flatEmbedTagged` from sparse flat local refiners, under the extra
  hypothesis `Ch · Bd₁ ≤ |Zo \ Z₁|`.
-/

@[expose] public section

namespace RefinedAbsorption.Local

open Finset RefinedAbsorption.MultiRefiner RefinedAbsorption.FlatDown RefinedAbsorption.Placement
  RefinedAbsorption.RefineDown RefinedAbsorption.LinkSpread RefinedAbsorption.Sharp
  RefinedAbsorption.Window

/-- **Sparse flat local refiners in uniformity `2`**: `FlatGraphRefiners` with the extra
hypothesis `Ch · d ≤ |P|`. -/
def FlatGraphRefinersS (q : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ K : ℕ, ∃ C Ch : ℕ, ∀ (n : ℕ) {E : Type} [DecidableEq E] (ends : E → Finset (Fin n))
    (Y P : Finset (Fin n)) (L : Finset E) (d : ℕ),
    Disjoint Y P → Y.card ≤ K * P.card → Ch ≤ P.card → Ch * d ≤ P.card →
    MIsRGraph 2 ends L → (∀ x ∈ L, ends x ⊆ Y) → (∀ v, mdeg ends L {v} ≤ d) →
    (∀ e, mult ends L e ≤ K) →
    ∃ (E' : Type) (_ : DecidableEq E') (g : E → E') (ends' : E' → Finset (Fin n))
      (R : Finset E') (𝒲 : Finset (Finset E')),
      Function.Injective g ∧ (∀ c, ends' (g c) = ends c) ∧ (∀ c ∈ R, ∀ x, g x ≠ c) ∧
      IsMultiRefiner q 2 C ends' (L.image g) R 𝒲 ∧
      (∀ c ∈ R, ends' c ⊆ Y ∪ P ∧ (ends' c ∩ P).Nonempty) ∧
      (∀ v, mdeg ends' R {v} ≤ C * (d + a P.card)) ∧
      (∀ e, mult ends' R e ≤ C) ∧
      (∀ x y, x ≠ y →
        (𝒲.filter fun W => x ∈ W.biUnion ends' ∧ y ∈ W.biUnion ends').card ≤ C) ∧
      (∀ W ∈ 𝒲, ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → x ∈ W.biUnion ends' → y ∈ W.biUnion ends' →
        ∃ c ∈ W, c ∈ L.image g ∧ ends' c = {x, y})

/-- **Sparse flat clique omni-absorbers are sparse flat local refiners.** -/
theorem flatGraphRefinersS_of_cliqueOmniS {q : ℕ} {a : ℕ → ℕ}
    (h : RefinedAbsorption.FlatOmni.FlatCliqueOmniAbsorbersS q a) : FlatGraphRefinersS q a := by
  intro K
  obtain ⟨C, Ch, hC⟩ := h K
  refine ⟨C * (K + C) + C, Ch, ?_⟩
  intro n E _ ends Y P L d hYP hYK hCh hChd hLr hLY hdeg hmult
  obtain ⟨E', _, g, ends', R, 𝒲, hg, hge, hfr, href, hflat, hdegR, hmultR, hclique⟩ :=
    hC n ends Y P L d hYP hYK hCh hChd hLr hLY hdeg hmult
  have hCC : C ≤ C * (K + C) + C := Nat.le_add_left _ _
  refine ⟨E', inferInstance, g, ends', R, 𝒲, hg, hge, hfr, href.mono hCC, hflat,
    fun v => (hdegR v).trans (Nat.mul_le_mul_right _ hCC), fun e => (hmultR e).trans hCC,
    fun x y hxy => ?_, fun W hW x hx y hy hxy hxW hyW => ?_⟩
  · -- pairs: a piece spanning `x, y` contains a copy on `{x, y}`
    refine (card_pieces_through_le href (fun W => x ∈ W.biUnion ends' ∧ y ∈ W.biUnion ends')
      {x, y} fun W hW hxyW => hclique W hW x hxyW.1 y hxyW.2 hxy).trans ?_
    have h1 := (mult_image_le (fun c _ => hge c) {x, y}).trans (hmult {x, y})
    have h2 := hmultR {x, y}
    calc C * (mult ends' (L.image g) {x, y} + mult ends' R {x, y}) ≤ C * (K + C) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := Nat.le_add_right _ _
  · obtain ⟨c, hcW, hc⟩ := hclique W hW x hxW y hyW hxy
    refine ⟨c, hcW, ?_, hc⟩
    rcases mem_union.1 (href.subset W hW hcW) with hcL | hcR
    · exact hcL
    · exfalso
      obtain ⟨z, hz⟩ := (hflat c hcR).2
      rw [hc] at hz
      obtain ⟨hz1, hz2⟩ := mem_inter.1 hz
      have hzY : z ∈ Y := by
        rcases mem_insert.1 hz1 with rfl | h
        · exact hx
        · rw [mem_singleton] at h; rw [h]; exact hy
      exact disjoint_left.1 hYP hzY hz2

set_option maxHeartbeats 1600000 in
/-- **Random embedding of flat local refiners for all tags at once** (Lemma 4.1, `r = 3`,
level `1`). -/
theorem flatEmbedTaggedS {q : ℕ} (a : ℕ → ℕ) (hF : FlatGraphRefinersS (q - 1) a)
    (ha : ∀ m m', m ≤ m' → a m ≤ sharpCost 3 m') (K M : ℕ) :
    ∃ C Ch : ℕ, ∀ (n : ℕ) (Zo Z₁ : Finset (Fin n)) {E₁ : Type} [DecidableEq E₁]
      (tg₁ bd₁ : E₁ → Finset (Fin n)) (X₁ : Finset E₁) (Bd₁ : ℕ),
      Z₁ ⊆ Zo → Ch ≤ (Zo \ Z₁).card → Ch * Bd₁ ≤ (Zo \ Z₁).card →
      Z₁.card ≤ K * (Zo \ Z₁).card →
      (X₁.image tg₁).card ≤ K * Zo.card →
      (∀ x, Disjoint (tg₁ x) Zo) → (∀ x, bd₁ x ⊆ Z₁) → (∀ x ∈ X₁, (tg₁ x).card = 1) →
      (∀ x ∈ X₁, (bd₁ x).card = 2) →
      (∀ T e, mult bd₁ (fibre tg₁ X₁ T) e ≤ M) →
      (∀ S : Finset (Fin n), S.card = 2 → mdeg (liftEnds tg₁ bd₁) X₁ S ≤ Bd₁) →
      ∃ Bd₂, Bd₂ ≤ C * (Bd₁ + sharpCost 3 Zo.card) ∧
        TRefOut q 3 1 C tg₁ bd₁ Zo X₁ (fun _ => Bd₂) := by
  classical
  obtain ⟨CF, ChF, hloc⟩ := hF (3 * K + M + 3)
  set s := 2 * CF + 2 with hs_def
  set μ := 2 * CF + 1 with hμ_def
  set cD := 2 * CF + CF * CF with hcD
  set C₁ := 20 * K * (K + 1) * s * cD + 2 * μ with hC₁
  refine ⟨C₁ + CF * (1 + CF) + 2 * CF + 1, 2 * ChF + 4, ?_⟩
  intro n Zo Z₁ E₁ _ tg₁ bd₁ X₁ Bd₁ hZ hCh hChB hZ1K htags htg hbd htgc hbdc hmult hdeg
  set sc := sharpCost 3 Zo.card with hsc
  -- the copy of `ZMod p`
  obtain ⟨p, hp, emb, hembA, hmp⟩ := exists_prime_emb (Zo \ Z₁) (by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  set P₀ : Finset (Fin n) := univ.map emb with hP₀
  have hP₀c : P₀.card = p := by rw [hP₀, card_map, card_univ, ZMod.card]
  have hmemP₀ : ∀ x, x ∈ P₀ ↔ ∃ z, emb z = x := by
    intro x; simp [hP₀]
  have hP₀sub : P₀ ⊆ Zo \ Z₁ := fun x hx => by
    obtain ⟨z, rfl⟩ := (hmemP₀ x).1 hx; exact hembA z
  have hZ₁P : ∀ x ∈ Z₁, ¬ ∃ z, emb z = x := by
    rintro x hx ⟨z, rfl⟩; exact (mem_sdiff.1 (hembA z)).2 hx
  have hdisj : Disjoint Z₁ P₀ := disjoint_left.2 fun x hx hxP => hZ₁P x hx ((hmemP₀ x).1 hxP)
  have hZoc : Zo.card = Z₁.card + (Zo \ Z₁).card := by
    rw [card_sdiff_of_subset hZ]; have := card_le_card hZ; omega
  have hpZo : p ≤ Zo.card := by
    have := card_le_card hP₀sub; rw [hP₀c] at this; omega
  have hZo1 : 1 ≤ Zo.card := by omega
  have hap : a p ≤ sc := ha p Zo.card hpZo
  -- the local refiners
  have hloc' := fun T : X₁.image tg₁ =>
    hloc n bd₁ Z₁ P₀ (fibre tg₁ X₁ T.1) Bd₁ hdisj
      (by rw [hP₀c]; nlinarith)
      (by rw [hP₀c]; omega)
      (by rw [hP₀c]; nlinarith)
      (fun x hx => hbdc x (fibre_subset _ _ _ hx))
      (fun x _ => hbd x)
      (mdeg_fibre_singleton_le (Zo := Zo) htg (fun x => (hbd x).trans hZ) T.2 htgc hdeg)
      (fun e => (hmult T.1 e).trans (by omega))
  choose E' inst g ends' R 𝒲 hg hge hfr href hflat hdegR hmultR hcod hroot using hloc'
  letI : ∀ T, DecidableEq (E' T) := inst
  simp only [hP₀c] at hdegR
  set D := Bd₁ + sc with hD
  set Δ := cD * D with hΔ
  -- all copies and pieces lie in `Z₁ ∪ P₀`
  have hcopy : ∀ T : X₁.image tg₁, ∀ c ∈ (fibre tg₁ X₁ T.1).image (g T) ∪ R T, ends' T c ⊆ Z₁ ∪ P₀ := by
    intro T c hc
    rcases mem_union.1 hc with hc | hc
    · obtain ⟨x, -, rfl⟩ := mem_image.1 hc
      rw [hge T x]; exact (hbd x).trans subset_union_left
    · exact (hflat T c hc).1
  have hspan : ∀ T : X₁.image tg₁, ∀ W ∈ 𝒲 T, W.biUnion (ends' T) ⊆ Z₁ ∪ P₀ :=
    fun T => span_subset (href T) (hcopy T)
  have hUZo : Z₁ ∪ P₀ ⊆ Zo := union_subset hZ (hP₀sub.trans sdiff_subset)
  have hmdegG : ∀ (T : X₁.image tg₁) x, mdeg (ends' T) ((fibre tg₁ X₁ T.1).image (g T)) {x} ≤ Bd₁ := by
    intro T x
    rw [mdeg_image_eq (fun c _ => hge T c) (hg T).injOn subset_rfl]
    exact mdeg_fibre_singleton_le (Zo := Zo) htg (fun x => (hbd x).trans hZ) T.2 htgc hdeg x
  have hsysdeg : ∀ (T : X₁.image tg₁) x, ((R T).filter fun c => x ∈ ends' T c).card +
      ((𝒲 T).filter fun W => x ∈ W.biUnion (ends' T)).card ≤ Δ := by
    intro T x
    refine (sys_deg_le (href T) x).trans ?_
    have h1 : mdeg (ends' T) (R T) {x} ≤ CF * D :=
      (hdegR T x).trans (Nat.mul_le_mul_left _ (by omega))
    have h2 := hmdegG T x
    have h4 : CF * (mdeg (ends' T) ((fibre tg₁ X₁ T.1).image (g T)) {x} +
        mdeg (ends' T) (R T) {x}) ≤ CF * D + CF * (CF * D) := by
      rw [← mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    rw [hΔ, hcD]
    nlinarith
  -- the set systems and the spreading
  have hAQ : ∀ (T : X₁.image tg₁) (k : {c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T}),
      Sum.elim (fun c => ends' T c.1) (fun W => W.1.biUnion (ends' T)) k ⊆ Zo := by
    rintro T (c | W)
    · exact (hcopy T c.1 (mem_union_right _ c.2)).trans hUZo
    · exact (hspan T W.1 W.2).trans hUZo
  have hsz : ∀ (T : X₁.image tg₁) (k : {c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T}),
      (Sum.elim (fun c => ends' T c.1) (fun W => W.1.biUnion (ends' T)) k).card ≤ s := by
    rintro T (c | W)
    · show (ends' T c.1).card ≤ s
      rw [(href T).rgraph c.1 (mem_union_right _ c.2)]; omega
    · show (W.1.biUnion (ends' T)).card ≤ s
      refine (card_biUnion_ends_le (r := 2) (ends' T) W.1
        fun i hi => (href T).rgraph i ((href T).subset W.1 W.2 hi)).trans ?_
      have := (href T).card_le W.1 W.2
      omega
  have hsdeg : ∀ (T : X₁.image tg₁) x, (univ.filter fun k : {c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T} =>
      x ∈ Sum.elim (fun c => ends' T c.1) (fun W => W.1.biUnion (ends' T)) k).card ≤ Δ :=
    fun T x => le_of_eq_of_le (card_univ_filter_sum (R T) (𝒲 T) (ends' T)
      (fun W => W.biUnion (ends' T)) (fun B => x ∈ B)) (hsysdeg T x)
  have hscod : ∀ (T : X₁.image tg₁) x y, x ≠ y → (univ.filter fun k : {c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T} =>
      x ∈ Sum.elim (fun c => ends' T c.1) (fun W => W.1.biUnion (ends' T)) k ∧
      y ∈ Sum.elim (fun c => ends' T c.1) (fun W => W.1.biUnion (ends' T)) k).card ≤ μ :=
    fun T x y hxy => le_of_eq_of_le (card_univ_filter_sum (R T) (𝒲 T) (ends' T)
      (fun W => W.biUnion (ends' T)) (fun B => x ∈ B ∧ y ∈ B))
      ((sys_codeg_le (href T) (hmultR T) (hcod T) hxy).trans (by omega))
  obtain ⟨gA, hgA⟩ := exists_affine_spread (ι := X₁.image tg₁)
    (κ := fun T => {c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T}) emb
    (fun T => Sum.elim (fun c => ends' T c.1) (fun W => W.1.biUnion (ends' T))) Zo
    (s := s) (Δ := Δ) (μ := μ) (fun z => (mem_sdiff.1 (hembA z)).1) hAQ hsz hsdeg hscod
    (by omega)
  -- the moved local refiners
  set ψ : X₁.image tg₁ → Fin n → Fin n := fun T => affMap emb (gA T) with hψ
  set ends'' : ∀ T : X₁.image tg₁, E' T → Finset (Fin n) := fun T c => (ends' T c).image (ψ T)
    with hends''
  have hψU : ∀ (T : X₁.image tg₁), ∀ x ∈ Z₁ ∪ P₀, ψ T x ∈ Z₁ ∪ P₀ := by
    intro T x hx
    by_cases hxr : ∃ z, emb z = x
    · obtain ⟨z, hz⟩ := (affMap_mem_range_iff emb (gA T) x).2 hxr
      exact mem_union_right _ ((hmemP₀ _).2 ⟨z, hz⟩)
    · show affMap emb (gA T) x ∈ Z₁ ∪ P₀
      rw [affMap_of_not emb _ hxr]; exact hx
  have himgU : ∀ (T : X₁.image tg₁) (B : Finset (Fin n)), B ⊆ Z₁ ∪ P₀ →
      B.image (ψ T) ⊆ Z₁ ∪ P₀ := fun T B hB x hx => by
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx; exact hψU T y (hB hy)
  have hspan'' : ∀ (T : X₁.image tg₁) (W : Finset (E' T)),
      W.biUnion (ends'' T) = (W.biUnion (ends' T)).image (ψ T) := fun T W => by
    rw [biUnion_image]
  have hfix : ∀ (T : X₁.image tg₁) (B : Finset (Fin n)), B ⊆ Z₁ → B.image (ψ T) = B :=
    fun T B hB => by
      conv_rhs => rw [← image_id (s := B)]
      exact image_congr fun x hx => affMap_of_not emb _ (hZ₁P x (hB hx))
  have hmemψ : ∀ (T : X₁.image tg₁) (B : Finset (Fin n)) (z : Fin n),
      ψ T z ∈ B.image (ψ T) ↔ z ∈ B := fun T B z =>
    (affMap_injective emb (gA T)).mem_finset_image
  -- vertex counts of the moved systems
  have h1R : ∀ (T : X₁.image tg₁) z, ((R T).filter fun c => z ∈ ends'' T c).card ≤ Δ := by
    intro T z
    obtain ⟨z', rfl⟩ := affMap_surjective emb (gA T) z
    refine le_trans (le_of_eq (congrArg card (filter_congr fun c _ => hmemψ T _ z'))) ?_
    have := hsysdeg T z'; omega
  have h1W : ∀ (T : X₁.image tg₁) z,
      ((𝒲 T).filter fun W => z ∈ W.biUnion (ends'' T)).card ≤ Δ := by
    intro T z
    obtain ⟨z', rfl⟩ := affMap_surjective emb (gA T) z
    refine le_trans (le_of_eq (congrArg card (filter_congr (q := fun W => z' ∈ W.biUnion (ends' T))
      fun W _ => by rw [hspan'']; exact hmemψ T _ z'))) ?_
    have := hsysdeg T z'; omega
  -- pair counts of the moved systems
  set b₂ := C₁ * D + CF * Bd₁ with hb₂
  have hb2 : ∀ S : Finset (Fin n), S ⊆ Zo → S.card = 2 →
      ∑ T : X₁.image tg₁, ((R T).filter fun c => S ⊆ ends'' T c).card +
        ∑ T : X₁.image tg₁, ((𝒲 T).filter fun W => S ⊆ W.biUnion (ends'' T)).card ≤ b₂ := by
    intro S hSZo hS
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hS
    have hpair : ∀ {u v : Fin n} {B : Finset (Fin n)}, ({u, v} : Finset (Fin n)) ⊆ B →
        u ∈ B ∧ v ∈ B := fun h => ⟨h (mem_insert_self _ _), h (mem_insert_of_mem (mem_singleton_self _))⟩
    -- the moved loads
    have hML : ∀ (T : X₁.image tg₁) (u v : Fin n),
        ((R T).filter fun c => ({u, v} : Finset (Fin n)) ⊆ ends'' T c).card +
        ((𝒲 T).filter fun W => ({u, v} : Finset (Fin n)) ⊆ W.biUnion (ends'' T)).card ≤
        movedLoad emb (fun T => Sum.elim (fun c : {c // c ∈ R T} => ends' T c.1)
          (fun W : {W // W ∈ 𝒲 T} => W.1.biUnion (ends' T))) u v T (gA T) := by
      intro T u v
      have hsum := card_univ_filter_sum (R T) (𝒲 T) (ends'' T) (fun W => W.biUnion (ends'' T))
        (fun B => u ∈ B ∧ v ∈ B)
      have heq : movedLoad emb (fun T => Sum.elim (fun c : {c // c ∈ R T} => ends' T c.1)
          (fun W : {W // W ∈ 𝒲 T} => W.1.biUnion (ends' T))) u v T (gA T) =
          (univ.filter fun k : {c // c ∈ R T} ⊕ {W // W ∈ 𝒲 T} =>
            (fun B => u ∈ B ∧ v ∈ B) (Sum.elim (fun a => ends'' T a.1)
              (fun b => (fun W => W.biUnion (ends'' T)) b.1) k)).card := by
        unfold movedLoad
        refine congrArg card (filter_congr fun k _ => ?_)
        rcases k with c | W
        · exact Iff.rfl
        · show _ ↔ u ∈ W.1.biUnion (ends'' T) ∧ v ∈ W.1.biUnion (ends'' T)
          rw [hspan'']
          exact Iff.rfl
      rw [heq, hsum]
      exact Nat.add_le_add (card_le_card (fun c hc => mem_filter.2 ⟨(mem_filter.1 hc).1,
        hpair (mem_filter.1 hc).2⟩)) (card_le_card (fun W hW => mem_filter.2
          ⟨(mem_filter.1 hW).1, hpair (mem_filter.1 hW).2⟩))
    -- case (a): the pair meets the copy of `ZMod p`
    have hZo' : Zo.card ≤ 3 * (K + 1) * p := by nlinarith
    have hN : Fintype.card (X₁.image tg₁) ≤ 3 * K * (K + 1) * p := by
      rw [Fintype.card_coe]
      refine htags.trans ((Nat.mul_le_mul_left K hZo').trans (le_of_eq (by ring)))
    have hLog : Real.log ((Zo.card : ℝ) ^ 2 + 1) ≤ 2 * (sc : ℝ) :=
      log_sq_add_one_le_sharpCost hZo1
    have key : ∀ u v : Fin n, u ≠ v → (∃ w, emb w = v) →
        ∑ T : X₁.image tg₁, ((R T).filter fun c => ({u, v} : Finset (Fin n)) ⊆ ends'' T c).card +
        ∑ T : X₁.image tg₁, ((𝒲 T).filter fun W =>
          ({u, v} : Finset (Fin n)) ⊆ W.biUnion (ends'' T)).card ≤ C₁ * D := by
      intro u v huv hv
      rw [← sum_add_distrib]
      refine le_trans (sum_le_sum fun T _ => hML T u v) ?_
      have h1 := hgA u v huv hv
      rw [hΔ] at h1
      have h2 := spread_bound_le K s cD μ p (Fintype.card (X₁.image tg₁)) D sc
        (Real.log ((Zo.card : ℝ) ^ 2 + 1)) hp2 hN hLog (by omega)
      have h3 := lt_of_lt_of_le h1 h2
      rw [hC₁]
      exact_mod_cast h3.le
    by_cases hv : ∃ w, emb w = y
    · exact (key x y hxy hv).trans (Nat.le_add_right _ _)
    by_cases hu : ∃ w, emb w = x
    · rw [pair_comm]; exact (key y x hxy.symm hu).trans (Nat.le_add_right _ _)
    by_cases hS1 : ({x, y} : Finset (Fin n)) ⊆ Z₁
    · -- case (c): the pair lies in `Z₁`
      have hnot : ∀ z ∈ ({x, y} : Finset (Fin n)), ¬ ∃ w, emb w = z :=
        fun z hz => hZ₁P z (hS1 hz)
      have hR0 : ∀ T : X₁.image tg₁,
          ((R T).filter fun c => ({x, y} : Finset (Fin n)) ⊆ ends'' T c).card = 0 := by
        intro T
        refine card_eq_zero.2 (filter_eq_empty_iff.2 fun c hc hsub => ?_)
        have hsub' : ({x, y} : Finset (Fin n)) ⊆ ends' T c :=
          (subset_image_affMap_iff emb (gA T) hnot).1 hsub
        have hc2 := (href T).rgraph c (mem_union_right _ hc)
        have heq : ends' T c = {x, y} :=
          (eq_of_subset_of_card_le hsub' (by rw [hc2, card_pair hxy])).symm
        obtain ⟨z, hz⟩ := (hflat T c hc).2
        rw [heq] at hz
        obtain ⟨hz1, hz2⟩ := mem_inter.1 hz
        exact disjoint_left.1 hdisj (hS1 hz1) hz2
      have hW0 : ∀ T : X₁.image tg₁, ((𝒲 T).filter fun W =>
          ({x, y} : Finset (Fin n)) ⊆ W.biUnion (ends'' T)).card ≤
          CF * mult bd₁ (fibre tg₁ X₁ T.1) {x, y} := by
        intro T
        refine (card_pieces_rooted_le (href T) _ {x, y} fun W hW hsub => ?_).trans
          (Nat.mul_le_mul_left _ (mult_image_le (fun c _ => hge T c) _))
        rw [hspan''] at hsub
        have hsub' := (subset_image_affMap_iff emb (gA T) hnot).1 hsub
        exact hroot T W hW x (hS1 (mem_insert_self _ _)) y
          (hS1 (mem_insert_of_mem (mem_singleton_self _))) hxy (hpair hsub').1 (hpair hsub').2
      rw [sum_congr rfl fun T _ => hR0 T, sum_const_zero, zero_add]
      refine (sum_le_sum fun T _ => hW0 T).trans ?_
      rw [← mul_sum]
      refine (Nat.mul_le_mul_left _ ?_).trans (Nat.le_add_left _ _)
      rw [sum_coe_sort (X₁.image tg₁) (fun T => mult bd₁ (fibre tg₁ X₁ T) {x, y})]
      exact sum_mult_fibre_le hdeg (card_pair hxy)
    · -- case (b): the pair leaves `Z₁ ∪ P₀`
      obtain ⟨v, hvS, hvZ⟩ := not_subset.1 hS1
      have hvnot : ¬ ∃ w, emb w = v := by
        rcases mem_insert.1 hvS with h | h
        · rw [h]; exact hu
        · rw [mem_singleton] at h; rw [h]; exact hv
      have hvU : v ∉ Z₁ ∪ P₀ := by
        rw [mem_union, not_or]; exact ⟨hvZ, fun h => hvnot ((hmemP₀ v).1 h)⟩
      have hR0 : ∀ T : X₁.image tg₁,
          ((R T).filter fun c => ({x, y} : Finset (Fin n)) ⊆ ends'' T c).card = 0 :=
        fun T => card_eq_zero.2 (filter_eq_empty_iff.2 fun c hc hsub =>
          hvU (himgU T _ (hcopy T c (mem_union_right _ hc)) (hsub hvS)))
      have hW0 : ∀ T : X₁.image tg₁, ((𝒲 T).filter fun W =>
          ({x, y} : Finset (Fin n)) ⊆ W.biUnion (ends'' T)).card = 0 :=
        fun T => card_eq_zero.2 (filter_eq_empty_iff.2 fun W hW hsub => by
          rw [hspan''] at hsub
          exact hvU (himgU T _ (hspan T W hW) (hsub hvS)))
      rw [sum_congr rfl fun T _ => hR0 T, sum_congr rfl fun T _ => hW0 T, sum_const_zero]
      exact Nat.zero_le _
  have hTagc : ∀ T : X₁.image tg₁, (T.1).card = 1 := fun T => by
    obtain ⟨x, hx, hxT⟩ := mem_image.1 T.2; rw [← hxT]; exact htgc x hx
  have hTagZ : ∀ T : X₁.image tg₁, Disjoint T.1 Zo := fun T => by
    obtain ⟨x, hx, hxT⟩ := mem_image.1 T.2; rw [← hxT]; exact htg x
  have hfinal : Δ + b₂ ≤ (C₁ + CF * (1 + CF) + 2 * CF + 1) * D := by
    have hB : CF * Bd₁ ≤ CF * D := Nat.mul_le_mul_left _ (by omega)
    have hc : cD + C₁ + CF ≤ C₁ + CF * (1 + CF) + 2 * CF + 1 := by
      rw [hcD, mul_add, mul_one]; omega
    calc Δ + b₂ = cD * D + C₁ * D + CF * Bd₁ := by rw [hb₂, hΔ]; ring
      _ ≤ cD * D + C₁ * D + CF * D := by omega
      _ = (cD + C₁ + CF) * D := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hc
  refine ⟨(C₁ + CF * (1 + CF) + 2 * CF + 1) * D, le_rfl, ?_⟩
  refine trefOut_of_local E' g ends'' R 𝒲 hg (fun T c hc => ?_) hfr (fun T => ?_)
    (fun T y hy => (himgU T _ (hcopy T y (mem_union_right _ hy))).trans hUZo)
    (fun S hS => ?_) (fun S hS => ?_)
  · show (ends' T (g T c)).image (ψ T) = bd₁ c
    rw [hge, hfix T _ (hbd c)]
  · have h0 := residual_mapEnds (href T) (ψ T) (fun _ _ => (affMap_injective emb (gA T)).injOn)
      (affMap_injective emb (gA T)).injOn (empty_subset _)
    have hC : CF ≤ C₁ + CF * (1 + CF) + 2 * CF + 1 := by omega
    have h1 := h0.mono hC
    exact h1
  · have hS2 : S.card = 2 := hS
    have hL := lifted_count_le (fun T : X₁.image tg₁ => T.1) hTagc hTagZ Subtype.val_injective R
      ends'' (fun T y hy => (himgU T _ (hcopy T y (mem_union_right _ hy))).trans hUZo) h1R
      (fun S' hS' hS'2 => (Nat.le_add_right _ _).trans (hb2 S' hS' hS'2)) S hS2
    exact le_trans (le_of_eq (sum_congr rfl fun T _ => rfl)) (hL.trans hfinal)
  · have hS2 : S.card = 2 := hS
    refine le_trans (sum_le_sum fun T _ => card_le_card fun W hW => ?_) ((lifted_count_le
      (fun T => T.1) hTagc hTagZ Subtype.val_injective 𝒲 (fun T W => W.biUnion (ends'' T))
      (fun T W hW => by
        show W.biUnion (ends'' T) ⊆ Zo
        rw [hspan'']; exact (himgU T _ (hspan T W hW)).trans hUZo) h1W
      (fun S' hS' hS'2 => (Nat.le_add_left _ _).trans (hb2 S' hS' hS'2)) S hS2).trans hfinal)
    obtain ⟨hW𝒲, hSW⟩ := mem_filter.1 hW
    exact mem_filter.2 ⟨hW𝒲, hSW.trans (biUnion_subset.2 fun c hc =>
      union_subset_union subset_rfl (subset_biUnion_of_mem _ hc))⟩


end RefinedAbsorption.Local
