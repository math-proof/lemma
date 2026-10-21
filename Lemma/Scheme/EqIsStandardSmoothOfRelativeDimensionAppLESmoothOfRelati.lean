import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma rank_kaehlerDifferential_of_isLocalization
  (A S O : Type u) [CommRing A] [CommRing S] [CommRing O] [Algebra A S] [Algebra S O] [Algebra A O]
  [IsScalarTower A S O] (M : Submonoid S) [IsLocalization M O] [Nontrivial O]
  (r : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension r A S] :
    Module.rank O (KaehlerDifferential A O) = r := by
  let _ : Nontrivial S := (algebraMap S O).domain_nontrivial
  let _ : Algebra.IsStandardSmooth A S := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth r
  let _ : IsLocalizedModule M (KaehlerDifferential.map A A S O) := KaehlerDifferential.isLocalizedModule_map A S O M
  let b := Module.Free.chooseBasis S (KaehlerDifferential A S)
  let b' := b.ofIsLocalizedModule O M (KaehlerDifferential.map A A S O)
  rw [← b'.mk_eq_rank'', ← Module.Free.rank_eq_card_chooseBasisIndex, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential r]

/--
[AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] {F : (Scheme : Type (u + 1))} (g : F ⟶ Spec (CommRingCat.of k)) (n : ℕ)
  (hg : SmoothOfRelativeDimension n g)
  (m : ℕ) (U : (Spec (CommRingCat.of k)).Opens) (W : F.Opens) (hW : IsAffineOpen W)
  (w : F) (hw : w ∈ W) (e : W ≤ ((TopologicalSpace.Opens.map g.base).obj U))
  (hm : (g.appLE U W e).hom.IsStandardSmoothOfRelativeDimension m) :
    m = n := by
  classical
  obtain ⟨U', hU', V', hV', hwV', e', hn⟩ := hg.exists_isStandardSmoothOfRelativeDimension w
  have hUtop : U = ⊤ := by
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rw [Subsingleton.elim x (g.base w)]
    apply e hw
  have hU'top : U' = ⊤ := by
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rw [Subsingleton.elim x (g.base w)]
    apply e' hwV'
  subst hUtop hU'top
  let _ : Algebra ((Spec (CommRingCat.of k)).presheaf.obj (op ⊤)) (F.presheaf.stalk w) :=
    (g.app ⊤ ≫ F.presheaf.germ ((TopologicalSpace.Opens.map g.base).obj ⊤) w (e hw)).hom.toAlgebra
  let _ : Algebra ((Spec (CommRingCat.of k)).presheaf.obj (op ⊤)) (F.presheaf.obj (op W)) := (g.appLE ⊤ W e).hom.toAlgebra
  let _ : Algebra.IsStandardSmoothOfRelativeDimension m ((Spec (CommRingCat.of k)).presheaf.obj (op ⊤)) (F.presheaf.obj (op W)) := hm
  let _ : Algebra (F.presheaf.obj (op W)) (F.presheaf.stalk w) := F.presheaf.algebra_section_stalk (⟨w, hw⟩ : W)
  have ht₁ : (g.app ⊤ ≫ F.presheaf.germ ((TopologicalSpace.Opens.map g.base).obj ⊤) w (e hw)).hom = (F.presheaf.germ W w hw).hom.comp (g.appLE ⊤ W e).hom := by
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  let _ : IsScalarTower ((Spec (CommRingCat.of k)).presheaf.obj (op ⊤)) (F.presheaf.obj (op W)) (F.presheaf.stalk w) :=
    IsScalarTower.of_algebraMap_eq' ht₁
  let _ := hW.isLocalization_stalk ⟨w, hw⟩
  have r₁ := rank_kaehlerDifferential_of_isLocalization ((Spec (CommRingCat.of k)).presheaf.obj (op ⊤)) (F.presheaf.obj (op W)) (F.presheaf.stalk w) (hW.primeIdealOf ⟨w, hw⟩).asIdeal.primeCompl m
  let _ : Algebra ((Spec (CommRingCat.of k)).presheaf.obj (op ⊤)) (F.presheaf.obj (op V')) := (g.appLE ⊤ V' e').hom.toAlgebra
  let _ : Algebra.IsStandardSmoothOfRelativeDimension n ((Spec (CommRingCat.of k)).presheaf.obj (op ⊤)) (F.presheaf.obj (op V')) := hn
  let _ : Algebra (F.presheaf.obj (op V')) (F.presheaf.stalk w) := F.presheaf.algebra_section_stalk (⟨w, hwV'⟩ : V')
  have ht₂ : (g.app ⊤ ≫ F.presheaf.germ ((TopologicalSpace.Opens.map g.base).obj ⊤) w (e hw)).hom = (F.presheaf.germ V' w hwV').hom.comp (g.appLE ⊤ V' e').hom := by
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  let _ : IsScalarTower ((Spec (CommRingCat.of k)).presheaf.obj (op ⊤)) (F.presheaf.obj (op V')) (F.presheaf.stalk w) :=
    IsScalarTower.of_algebraMap_eq' ht₂
  let _ := hV'.isLocalization_stalk ⟨w, hwV'⟩
  have r₂ := rank_kaehlerDifferential_of_isLocalization ((Spec (CommRingCat.of k)).presheaf.obj (op ⊤)) (F.presheaf.obj (op V')) (F.presheaf.stalk w) (hV'.primeIdealOf ⟨w, hwV'⟩).asIdeal.primeCompl n
  exact_mod_cast r₁.symm.trans r₂


-- created on 2026-10-20
