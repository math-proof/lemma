import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination
open Finset Filter Set Topology StatMech StatMech.FrontierA


/--
[isingTorusDirichletBilinear_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma isingTorusDirichletBilinear_symm_eq
  {d k : Nat}
  {u v : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusDirichletBilinear u v = isingTorusDirichletBilinear v u := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichletBilinear_symm u v

/--
[isingTorusDirichletBilinear_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma isingTorusDirichletBilinear_add_left_eq
  {d k : Nat}
  {u v w : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusDirichletBilinear (u + v) w = isingTorusDirichletBilinear u w + isingTorusDirichletBilinear v w := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichletBilinear_add_left u v w

/--
[isingTorusDirichletBilinear_smul_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma isingTorusDirichletBilinear_smul_left_eq
  {d k : Nat}
  {t : Real}
  {u v : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusDirichletBilinear (t • u) v = t * isingTorusDirichletBilinear u v := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichletBilinear_smul_left t u v

/--
[isingTorusDirichlet_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma isingTorusDirichlet_add_eq
  {d k : Nat}
  {u v : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusDirichlet (u + v) = isingTorusDirichlet u + 2 * isingTorusDirichletBilinear u v + isingTorusDirichlet v := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichlet_add u v

/--
[isingTorusDirichlet_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma isingTorusDirichlet_smul_eq
  {d k : Nat}
  {t : Real}
  {u : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusDirichlet (t • u) = t ^ 2 * isingTorusDirichlet u := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichlet_smul t u

/--
[isingTorusShiftedPartition_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma isingTorusShiftedPartition_smul_eq
  {d k : Nat}
  {beta t : Real}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  isingTorusShiftedPartition beta (t • h) = Real.exp (-(beta / 2) * t ^ 2 * isingTorusDirichlet h) * ∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * Real.exp (-beta * t * isingTorusDirichletBilinear (isingTorusSpinField sigma) h) := by
-- proof
  apply StatMech.FrontierA.isingTorusShiftedPartition_smul beta t h

/--
[isingTorusShiftedPartition_zero_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma isingTorusShiftedPartition_zero_pos_eq
  {d k : Nat}
  {beta : Real} :
-- imply
  0 < isingTorusShiftedPartition (d := d) (k := k) beta 0 := by
-- proof
  apply StatMech.FrontierA.isingTorusShiftedPartition_zero_pos beta

/--
[iteratedDeriv_two_nonpos_of_global_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma iteratedDeriv_two_nonpos_of_global_max_eq
  {d k : Nat}
  {f : Real → Real}
-- given
  (hf : ContDiff Real 2 f)
  (hmax : ∀ x, f x ≤ f 0) :
-- imply
  iteratedDeriv 2 f 0 ≤ 0 := by
-- proof
  apply StatMech.FrontierA.iteratedDeriv_two_nonpos_of_global_max f hf hmax

/--
[hasDerivAt_isingTorusShiftedPartition_line](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma hasDerivAt_isingTorusShiftedPartition_line_eq
  {d k : Nat}
  {beta : Real}
  {t : Real}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  HasDerivAt (fun s => isingTorusShiftedPartition beta (s • h)) (isingTorusShiftedPartitionLineDeriv beta h t) t := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_isingTorusShiftedPartition_line beta h t

/--
[hasDerivAt_isingTorusShiftedPartitionLineDeriv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma hasDerivAt_isingTorusShiftedPartitionLineDeriv_zero_eq
  {d k : Nat}
  {beta : Real}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  HasDerivAt (isingTorusShiftedPartitionLineDeriv beta h) (∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * ((beta * isingTorusDirichletBilinear (isingTorusSpinField sigma) h) ^ 2 - beta * isingTorusDirichlet h)) 0 := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_isingTorusShiftedPartitionLineDeriv_zero beta h

/--
[iteratedDeriv_two_isingTorusShiftedPartition_line_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma iteratedDeriv_two_isingTorusShiftedPartition_line_zero_eq
  {d k : Nat}
  {beta : Real}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  iteratedDeriv 2 (fun t : Real => isingTorusShiftedPartition beta (t • h)) 0 = ∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * ((beta * isingTorusDirichletBilinear (isingTorusSpinField sigma) h) ^ 2 - beta * isingTorusDirichlet h) := by
-- proof
  apply StatMech.FrontierA.iteratedDeriv_two_isingTorusShiftedPartition_line_zero beta h

/--
[contDiff_isingTorusShiftedPartition_line](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma contDiff_isingTorusShiftedPartition_line_eq
  {d k : Nat}
  {beta : Real}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  ContDiff Real 2 (fun t : Real => isingTorusShiftedPartition beta (t • h)) := by
-- proof
  apply StatMech.FrontierA.contDiff_isingTorusShiftedPartition_line beta h

/--
[isingTorus_bilinear_secondMoment_le_dirichlet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean)
-/
@[path]
private lemma isingTorus_bilinear_secondMoment_le_dirichlet_eq
  {d k : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hdom : IsingTorusGaussianDominated (d := d) (k := k) beta)
  (h : IsingDyadicTorus d k → Real) :
-- imply
  (∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * (isingTorusDirichletBilinear (isingTorusSpinField sigma) h) ^ 2) ≤ isingTorusShiftedPartition (d := d) (k := k) beta 0 * (isingTorusDirichlet h / beta) := by
-- proof
  apply StatMech.FrontierA.isingTorus_bilinear_secondMoment_le_dirichlet beta hbeta hdom h


-- created on 2026-10-23
