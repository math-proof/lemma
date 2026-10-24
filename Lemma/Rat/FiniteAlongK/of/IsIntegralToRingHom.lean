import Mathlib
import sympy.Basic
import Definitions.Def_AlgebraicCurve_Correspondence
open AlgebraicCurve


/-- ported from external source -/
@[path]
private lemma main
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra.EssFiniteType K F']
  {φ : F →ₐ[K] F'}
-- given
  (hφ : φ.toRingHom.IsIntegral) :
-- imply
  FiniteAlong K φ := by
-- proof
  classical
    let := algebraAlong φ
    have := isScalarTower_along φ
    have := isIntegral_along φ hφ
    have : Algebra.EssFiniteType F F' := Algebra.EssFiniteType.of_comp K F F'
    obtain ⟨s, hs⟩ := IntermediateField.fg_top F F'
    have hfin : FiniteDimensional F (IntermediateField.adjoin F (s : Set F')) :=
      IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
    rw [hs] at hfin
    show Module.Finite F F'
    exact (IntermediateField.topEquiv (F := F) (E := F')).toLinearEquiv.finiteDimensional


-- created on 2026-10-23
