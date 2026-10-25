import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusLaplacianNormalization.Part4
open Finset Matrix StatMech StatMech.FrontierA


/--
[isingTorusGraph_reachable_add_nsmul_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean)
-/
@[path]
private lemma isingTorusGraph_reachable_add_nsmul_step_eq
  {d k : Nat}
  {x : IsingDyadicTorus d k}
  {i : Fin d}
  {n : Nat} :
-- imply
  (isingTorusGraph d k).Reachable x (x + n • isingTorusStep i) := by
-- proof
  apply StatMech.FrontierA.isingTorusGraph_reachable_add_nsmul_step x i n

/--
[isingTorusGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean)
-/
@[path]
private lemma isingTorusGraph_connected_eq
  {d k : Nat} :
-- imply
  (isingTorusGraph d k).Connected := by
-- proof
  apply StatMech.FrontierA.isingTorusGraph_connected

/--
[isingTorusOrientedIndexedDart_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean)
-/
@[path]
private lemma isingTorusOrientedIndexedDart_bijective_eq
  {d k : Nat} :
-- imply
  Function.Bijective (isingTorusOrientedIndexedDart (d := d) (k := k)) := by
-- proof
  apply StatMech.FrontierA.isingTorusOrientedIndexedDart_bijective

/--
[isingTorusDirichlet_eq_lapMatrix_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean)
-/
@[path]
private lemma isingTorusDirichlet_eq_lapMatrix_quadratic_eq
  {d k : Nat}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  isingTorusDirichlet h = h ⬝ᵥ ((isingTorusGraph d k).lapMatrix Real *ᵥ h) := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichlet_eq_lapMatrix_quadratic h

/--
[isingTorusDirichletBilinear_eq_lapMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean)
-/
@[path]
private lemma isingTorusDirichletBilinear_eq_lapMatrix_eq
  {d k : Nat}
-- given
  (u h : IsingDyadicTorus d k → Real) :
-- imply
  isingTorusDirichletBilinear u h = u ⬝ᵥ ((isingTorusGraph d k).lapMatrix Real *ᵥ h) := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichletBilinear_eq_lapMatrix u h

/--
[isingTorus_lapMatrix_range_eq_zeroSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean)
-/
@[path]
private lemma isingTorus_lapMatrix_range_eq_zeroSum_eq
  {d k : Nat} :
-- imply
  LinearMap.range (Matrix.toLin' ((isingTorusGraph d k).lapMatrix Real)) = LinearMap.ker (isingTorusSumLinear (d := d) (k := k)) := by
-- proof
  apply StatMech.FrontierA.isingTorus_lapMatrix_range_eq_zeroSum

/--
[exists_isingTorusDirichlet_potential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean)
-/
@[path]
private lemma exists_isingTorusDirichlet_potential_eq
  {d k : Nat}
  {f : IsingDyadicTorus d k → Real}
-- given
  (hzero : ∑ x, f x = 0) :
-- imply
  ∃ h : IsingDyadicTorus d k → Real, ∀ u : IsingDyadicTorus d k → Real, isingTorusDirichletBilinear u h = ∑ x, u x * f x := by
-- proof
  apply StatMech.FrontierA.exists_isingTorusDirichlet_potential f hzero

/--
[isingTorus_linear_expMoment_le_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean)
-/
@[path]
private lemma isingTorus_linear_expMoment_le_unconditional_eq
  {d k : Nat}
  {beta : Real}
  {s : Real}
-- given
  (hbeta : 0 < beta)
  (f h : IsingDyadicTorus d k → Real)
  (hpotential : ∀ u : IsingDyadicTorus d k → Real, isingTorusDirichletBilinear u h = ∑ x, u x * f x) :
-- imply
  (∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * Real.exp (s * ∑ x, isingTorusSpinField sigma x * f x)) / isingTorusShiftedPartition (d := d) (k := k) beta 0 ≤ Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
-- proof
  apply StatMech.FrontierA.isingTorus_linear_expMoment_le_unconditional beta hbeta f h hpotential s

/--
[isingTorus_linear_expAbsMoment_le_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean)
-/
@[path]
private lemma isingTorus_linear_expAbsMoment_le_unconditional_eq
  {d k : Nat}
  {beta : Real}
  {s : Real}
-- given
  (hbeta : 0 < beta)
  (f h : IsingDyadicTorus d k → Real)
  (hpotential : ∀ u : IsingDyadicTorus d k → Real, isingTorusDirichletBilinear u h = ∑ x, u x * f x) :
-- imply
  (∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * Real.exp (s * |∑ x, isingTorusSpinField sigma x * f x|)) / isingTorusShiftedPartition (d := d) (k := k) beta 0 ≤ 2 * Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta)) := by
-- proof
  apply StatMech.FrontierA.isingTorus_linear_expAbsMoment_le_unconditional beta hbeta f h hpotential s

/--
[exists_isingTorus_linear_expMoment_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusLaplacianNormalization.lean)
-/
@[path]
private lemma exists_isingTorus_linear_expMoment_bounds_eq
  {d k : Nat}
  {beta : Real}
  {f : IsingDyadicTorus d k → Real}
-- given
  (hbeta : 0 < beta)
  (hzero : ∑ x, f x = 0) :
-- imply
  ∃ h : IsingDyadicTorus d k → Real, (∀ u : IsingDyadicTorus d k → Real, isingTorusDirichletBilinear u h = ∑ x, u x * f x) ∧ (∀ s : Real, (∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * Real.exp (s * ∑ x, isingTorusSpinField sigma x * f x)) / isingTorusShiftedPartition (d := d) (k := k) beta 0 ≤ Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta))) ∧ (∀ s : Real, (∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * Real.exp (s * |∑ x, isingTorusSpinField sigma x * f x|)) / isingTorusShiftedPartition (d := d) (k := k) beta 0 ≤ 2 * Real.exp (s ^ 2 * isingTorusDirichlet h / (2 * beta))) := by
-- proof
  apply StatMech.FrontierA.exists_isingTorus_linear_expMoment_bounds beta hbeta f hzero


-- created on 2026-10-23
