import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.Correspondence
import Lemma.Int.P2MUtil

open AlgebraicCurve

/--
[AlgebraicCurve_finiteAlong_of_isIntegral](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_finiteAlong_of_isIntegral.lean)
-/
@[path]
private lemma main
  {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra.EssFiniteType K F']
  {φ : F →ₐ[K] F'}
-- given
  (hφ : φ.toRingHom.IsIntegral) :
-- imply
  FiniteAlong K φ := by
-- proof
  classical
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Algebra.EssFiniteType F F' := Algebra.EssFiniteType.of_comp K F F'
  obtain ⟨s, hs⟩ := IntermediateField.fg_top F F'
  have hfin : FiniteDimensional F (IntermediateField.adjoin F (s : Set F')) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [hs] at hfin
  show Module.Finite F F'
  exact (IntermediateField.topEquiv (F := F) (E := F')).toLinearEquiv.finiteDimensional


-- created on 2026-10-23
