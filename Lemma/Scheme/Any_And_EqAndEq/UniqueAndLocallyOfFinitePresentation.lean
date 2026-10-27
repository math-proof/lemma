import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma single
  {B X Y : (Scheme : Type (u + 1))} (πX : X ⟶ B) (πY : Y ⟶ B) [IsSeparated πY] (a b : X ⟶ Y)
  (ha : a ≫ πY = πX) (hb : b ≫ πY = πX) :
    ∃ (E : (Scheme : Type (u + 1))) (m : E ⟶ X), IsClosedImmersion m ∧ m ≫ a = m ≫ b ∧
      (∀ (T : (Scheme : Type (u + 1))) (g : T ⟶ X), g ≫ a = g ≫ b → ∃! g' : T ⟶ E, g' ≫ m = g) ∧
      (LocallyOfFinitePresentation (pullback.diagonal πY) → LocallyOfFinitePresentation m) := by
  have hab : a ≫ πY = b ≫ πY := ha.trans hb.symm
  have key : pullback.fst (pullback.lift a b hab) (pullback.diagonal πY) ≫ a =
      pullback.fst (pullback.lift a b hab) (pullback.diagonal πY) ≫ b := by
    have h1 := congrArg (· ≫ pullback.fst πY πY) (pullback.condition (f := pullback.lift a b hab) (g := pullback.diagonal πY))
    have h2 := congrArg (· ≫ pullback.snd πY πY) (pullback.condition (f := pullback.lift a b hab) (g := pullback.diagonal πY))
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd,
      Category.comp_id] at h1 h2
    rw [h1, h2]
  refine ⟨pullback (pullback.lift a b hab) (pullback.diagonal πY), pullback.fst _ _, inferInstance, key, ?_, ?_⟩
  ·
    intro T g hg
    have hc : g ≫ pullback.lift a b hab = (g ≫ a) ≫ pullback.diagonal πY := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hg]
    refine ⟨pullback.lift g (g ≫ a) hc, pullback.lift_fst _ _ _, ?_⟩
    intro g' hg'
    apply pullback.hom_ext
    · rwa [pullback.lift_fst]
    ·
      rw [pullback.lift_snd]
      have h1 := congrArg (· ≫ pullback.fst πY πY)
        (pullback.condition (f := pullback.lift a b hab) (g := pullback.diagonal πY))
      simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id] at h1
      rw [← hg', Category.assoc, h1]
  ·
    intro hΔ
    let _ := hΔ
    infer_instance
private lemma finN
  {B Y : (Scheme : Type (u + 1))} (πY : Y ⟶ B) [IsSeparated πY] (n : ℕ) :
    ∀ (X : (Scheme : Type (u + 1))) (πX : X ⟶ B) (a b : Fin n → (X ⟶ Y)) (_ : ∀ i, a i ≫ πY = πX) (_ : ∀ i, b i ≫ πY = πX), ∃ (E : (Scheme : Type (u + 1))) (m : E ⟶ X), IsClosedImmersion m ∧ (∀ i, m ≫ a i = m ≫ b i) ∧ (∀ (T : (Scheme : Type (u + 1))) (g : T ⟶ X), (∀ i, g ≫ a i = g ≫ b i) → ∃! g' : T ⟶ E, g' ≫ m = g) ∧ (LocallyOfFinitePresentation (pullback.diagonal πY) → LocallyOfFinitePresentation m) := by
  induction n with
  | zero =>
    intro X πX a b ha hb
    exact ⟨X, 𝟙 X, inferInstance, fun i => i.elim0, fun T g _ => ⟨g, Category.comp_id g,
      fun g' h => by simpa only [Category.comp_id] using h⟩, fun _ => inferInstance⟩
  | succ n ih =>
    intro X πX a b ha hb
    obtain ⟨E', m', hm', heq', huniv', hlfp'⟩ :=
      ih X πX (fun i => a i.succ) (fun i => b i.succ) (fun i => ha _) (fun i => hb _)
    let _ := hm'
    obtain ⟨E, m'', hm'', heq'', huniv'', hlfp''⟩ := single (m' ≫ πX) πY (m' ≫ a 0) (m' ≫ b 0)
      (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb])
    let _ := hm''
    refine ⟨E, m'' ≫ m', inferInstance, ?_, ?_, ?_⟩
    ·
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Category.assoc] using heq''
      · rw [Category.assoc, Category.assoc, heq' j]
    ·
      intro T g hg
      obtain ⟨g', hg', hu'⟩ := huniv' T g (fun i => hg i.succ)
      obtain ⟨g'', hg'', hu''⟩ := huniv'' T g'
        (by rw [← Category.assoc, ← Category.assoc, hg', hg 0])
      refine ⟨g'', show g'' ≫ m'' ≫ m' = g by rw [← Category.assoc, hg'', hg'], fun l hl => ?_⟩
      apply hu''
      apply hu'
      show (l ≫ m'') ≫ m' = g
      rwa [Category.assoc]
    ·
      intro hΔ
      let _ := hlfp' hΔ
      let _ := hlfp'' hΔ
      infer_instance
/--
[AlgebraicGeometry_exists_equalizerLocus_isClosedImmersion_of_isSeparated](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_equalizerLocus_isClosedImmersion_of_isSeparated.lean)
-/
@[path]
private lemma main
  {B X Y : (Scheme : Type (u + 1))} (πX : X ⟶ B) (πY : Y ⟶ B) (hY : IsSeparated πY)
    {ι : Type v} [Fintype ι] (a b : ι → (X ⟶ Y))
    (ha : ∀ i, a i ≫ πY = πX) (hb : ∀ i, b i ≫ πY = πX) :
    ∃ (E : (Scheme : Type (u + 1))) (m : E ⟶ X), IsClosedImmersion m ∧
      (∀ i, m ≫ a i = m ≫ b i) ∧
      (∀ (T : (Scheme : Type (u + 1))) (g : T ⟶ X), (∀ i, g ≫ a i = g ≫ b i) → ∃! g' : T ⟶ E, g' ≫ m = g) ∧
      (LocallyOfFinitePresentation (pullback.diagonal πY) → LocallyOfFinitePresentation m) := by
  let _ := hY
  obtain ⟨E, m, h1, h2, h3, h4⟩ := finN πY (Fintype.card ι) X πX
    (fun j => a ((Fintype.equivFin ι).symm j)) (fun j => b ((Fintype.equivFin ι).symm j)) (fun j => ha _) (fun j => hb _)
  refine ⟨E, m, h1, fun i => ?_, fun T g hg => h3 T g (fun j => hg _), h4⟩
  simpa only [Equiv.symm_apply_apply] using h2 (Fintype.equivFin ι i)


-- created on 2026-10-20
