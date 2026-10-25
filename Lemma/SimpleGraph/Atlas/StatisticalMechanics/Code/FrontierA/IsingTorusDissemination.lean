import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusDissemination.Part8
open Finset StatMech StatMech.FrontierA


/--
[isingTorusTranslateField_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusTranslateField_zero_eq
  {d k : Nat}
  {u : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusTranslateField 0 u = u := by
-- proof
  apply StatMech.FrontierA.isingTorusTranslateField_zero u

/--
[isingTorusTranslateField_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusTranslateField_add_eq
  {d k : Nat}
  {a : IsingDyadicTorus d k}
  {u v : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusTranslateField a (u + v) = isingTorusTranslateField a u + isingTorusTranslateField a v := by
-- proof
  apply StatMech.FrontierA.isingTorusTranslateField_add a u v

/--
[isingTorusTranslateField_neg_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusTranslateField_neg_add_eq
  {d k : Nat}
  {a : IsingDyadicTorus d k}
  {u : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusTranslateField (-a) (isingTorusTranslateField a u) = u := by
-- proof
  apply StatMech.FrontierA.isingTorusTranslateField_neg_add a u

/--
[isingTorusSpinField_translateConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusSpinField_translateConfig_eq
  {d k : Nat}
  {a : IsingDyadicTorus d k}
  {sigma : ConfigSpace (IsingDyadicTorus d k)} :
-- imply
  isingTorusSpinField (isingTorusTranslateConfig a sigma) = isingTorusTranslateField a (isingTorusSpinField sigma) := by
-- proof
  apply StatMech.FrontierA.isingTorusSpinField_translateConfig a sigma

/--
[isingTorusDirichlet_translateField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusDirichlet_translateField_eq
  {d k : Nat}
  {a : IsingDyadicTorus d k}
  {u : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusDirichlet (isingTorusTranslateField a u) = isingTorusDirichlet u := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichlet_translateField a u

/--
[isingTorusShiftedPartition_translateField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusShiftedPartition_translateField_eq
  {d k : Nat}
  {a : IsingDyadicTorus d k}
  {beta : Real}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  isingTorusShiftedPartition beta (isingTorusTranslateField a h) = isingTorusShiftedPartition beta h := by
-- proof
  apply StatMech.FrontierA.isingTorusShiftedPartition_translateField a beta h

/--
[isingTorusShiftedPartition_polarization_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusShiftedPartition_polarization_at_eq
  {d k : Nat}
  {i : Fin d}
  {a : IsingDyadicTorus d k}
  {beta : Real}
-- given
  (hbeta : 0 ≤ beta)
  (h : IsingDyadicTorus d k → Real) :
-- imply
  2 * isingTorusShiftedPartition beta h ≤ isingTorusShiftedPartition beta (isingTorusPolarizeLowerAt i a h) + isingTorusShiftedPartition beta (isingTorusPolarizeUpperAt i a h) := by
-- proof
  apply StatMech.FrontierA.isingTorusShiftedPartition_polarization_at i a beta hbeta h

/--
[isingTorusCoordinateShift_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusCoordinateShift_apply_same_eq
  {d k : Nat}
  {i : Fin d}
  {n : Nat} :
-- imply
  isingTorusCoordinateShift (k := k) i n i = n := by
-- proof
  apply StatMech.FrontierA.isingTorusCoordinateShift_apply_same i n

/--
[isingTorusCoordinateShift_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusCoordinateShift_apply_of_ne_eq
  {d k : Nat}
  {i j : Fin d}
  {n : Nat}
-- given
  (hji : j ≠ i) :
-- imply
  isingTorusCoordinateShift (k := k) i n j = 0 := by
-- proof
  apply StatMech.FrontierA.isingTorusCoordinateShift_apply_of_ne i j hji n

/--
[isingTorusDisseminatedBlock_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusDisseminatedBlock_one_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  IsingTorusDisseminatedBlock i 1 h := by
-- proof
  apply StatMech.FrontierA.isingTorusDisseminatedBlock_one i h

/--
[isingTorusDisseminatedBlock_double](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusDisseminatedBlock_double_eq
  {d k : Nat}
  {i : Fin d}
  {s : Nat}
-- given
  (hspos : 0 < s)
  (hs : s ≤ 2 ^ (k + 1))
  (h : IsingDyadicTorus d k → Real)
  (hblock : IsingTorusDisseminatedBlock i s h) :
-- imply
  IsingTorusDisseminatedBlock i (2 * s) (isingTorusPolarizeLowerAt i (isingTorusBlockShift i s) h) := by
-- proof
  apply StatMech.FrontierA.isingTorusDisseminatedBlock_double i s hspos hs h hblock

/--
[isingTorusIndexedField_polarizeLowerIndexAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusIndexedField_polarizeLowerIndexAt_eq
  {d k : Nat}
  {i : Fin d}
  {a : IsingDyadicTorus d k}
  {g : IsingDyadicTorus d k → IsingDyadicTorus d k}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  isingTorusIndexedField h (isingTorusPolarizeLowerIndexAt i a g) = isingTorusPolarizeLowerAt i a (isingTorusIndexedField h g) := by
-- proof
  apply StatMech.FrontierA.isingTorusIndexedField_polarizeLowerIndexAt i a h g

/--
[isingTorusIndexedField_polarizeUpperIndexAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusIndexedField_polarizeUpperIndexAt_eq
  {d k : Nat}
  {i : Fin d}
  {a : IsingDyadicTorus d k}
  {g : IsingDyadicTorus d k → IsingDyadicTorus d k}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  isingTorusIndexedField h (isingTorusPolarizeUpperIndexAt i a g) = isingTorusPolarizeUpperAt i a (isingTorusIndexedField h g) := by
-- proof
  apply StatMech.FrontierA.isingTorusIndexedField_polarizeUpperIndexAt i a h g

/--
[isingTorus_polarizeLower_preserves_indexed_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorus_polarizeLower_preserves_indexed_max_eq
  {d k : Nat}
  {i : Fin d}
  {a : IsingDyadicTorus d k}
  {beta : Real}
  {g : IsingDyadicTorus d k → IsingDyadicTorus d k}
-- given
  (hbeta : 0 ≤ beta)
  (h : IsingDyadicTorus d k → Real)
  (hmax : ∀ g' : IsingDyadicTorus d k → IsingDyadicTorus d k, isingTorusShiftedPartition beta (isingTorusIndexedField h g') ≤ isingTorusShiftedPartition beta (isingTorusIndexedField h g)) :
-- imply
  isingTorusShiftedPartition beta (isingTorusIndexedField h (isingTorusPolarizeLowerIndexAt i a g)) = isingTorusShiftedPartition beta (isingTorusIndexedField h g) := by
-- proof
  apply StatMech.FrontierA.isingTorus_polarizeLower_preserves_indexed_max i a beta hbeta h g hmax

/--
[isingTorusDisseminatedBox_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusDisseminatedBox_one_eq
  {d k : Nat}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  IsingTorusDisseminatedBox (fun _ : Fin d => 1) h := by
-- proof
  apply StatMech.FrontierA.isingTorusDisseminatedBox_one h

/--
[isingTorusDisseminatedBox_double](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusDisseminatedBox_double_eq
  {d k : Nat}
  {sizes : Fin d → Nat}
  {i : Fin d}
  {s : Nat}
-- given
  (hspos : 0 < s)
  (hs : s ≤ 2 ^ (k + 1))
  (h : IsingDyadicTorus d k → Real)
  (hbox : IsingTorusDisseminatedBox (Function.update sizes i s) h) :
-- imply
  IsingTorusDisseminatedBox (Function.update sizes i (2 * s)) (isingTorusPolarizeLowerAt i (isingTorusBlockShift i s) h) := by
-- proof
  apply StatMech.FrontierA.isingTorusDisseminatedBox_double sizes i s hspos hs h hbox

/--
[isingTorusShiftedPartition_eq_zero_of_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorusShiftedPartition_eq_zero_of_constant_eq
  {d k : Nat}
  {beta : Real}
-- given
  (h : IsingDyadicTorus d k → Real)
  (hconst : ∀ x, h x = h 0) :
-- imply
  isingTorusShiftedPartition beta h = isingTorusShiftedPartition (d := d) (k := k) beta 0 := by
-- proof
  apply StatMech.FrontierA.isingTorusShiftedPartition_eq_zero_of_constant beta h hconst

/--
[isingTorus_gaussianDominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorus_gaussianDominated_eq
  {d k : Nat}
  {beta : Real}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  IsingTorusGaussianDominated (d := d) (k := k) beta := by
-- proof
  apply StatMech.FrontierA.isingTorus_gaussianDominated beta hbeta

/--
[isingTorus_addChar_secondMoment_le_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean)
-/
@[path]
private lemma isingTorus_addChar_secondMoment_le_unconditional_eq
  {d k : Nat}
  {beta : Real}
  {chi : AddChar (IsingDyadicTorus d k) Complex}
-- given
  (hbeta : 0 < beta)
  (hdisp : 0 < isingTorusCharacterDispersion chi) :
-- imply
  (∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * Complex.normSq (∑ x : IsingDyadicTorus d k, (isingTorusSpinField sigma x : Complex) * chi x)) ≤ isingTorusShiftedPartition (d := d) (k := k) beta 0 * (Fintype.card (IsingDyadicTorus d k) / (beta * isingTorusCharacterDispersion chi)) := by
-- proof
  apply StatMech.FrontierA.isingTorus_addChar_secondMoment_le_unconditional beta hbeta chi hdisp


-- created on 2026-10-23
