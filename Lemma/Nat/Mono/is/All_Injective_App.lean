import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

/--
[AlgebraicGeometry_Scheme_Modules_Hom_mono_iff_injective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_Hom_mono_iff_injective.lean)
-/
@[main]
private lemma main
  {X : Scheme.{u}}
  {M N : X.Modules}
  {φ : M ⟶ N} :
-- imply
  Mono φ ↔ ∀ U : X.Opens, Function.Injective (φ.app U) := by
-- proof
  constructor
  · intro hφ U

    let ev : TopCat.Presheaf Ab.{u} X ⥤ Ab.{u} := (CategoryTheory.evaluation _ Ab.{u}).obj (op U)
    haveI : Mono ((Scheme.Modules.toPresheaf X).map φ) :=
      preserves_mono_of_preservesLimit (Scheme.Modules.toPresheaf X) φ
    haveI : PreservesLimitsOfShape WalkingCospan ev := evaluation_preservesLimitsOfShape _
    haveI : Mono (ev.map ((Scheme.Modules.toPresheaf X).map φ)) := preserves_mono_of_preservesLimit _ _
    have h : Mono (φ.app U) := this
    exact (AddCommGrpCat.mono_iff_injective (φ.app U)).1 h
  · intro h
    refine ⟨fun g g' w => ?_⟩
    refine Scheme.Modules.hom_ext g g' fun U => ?_
    ext x
    apply h U
    have := congr(($w).app U x)
    simpa [Scheme.Modules.Hom.comp_app] using this


-- created on 2026-10-05
