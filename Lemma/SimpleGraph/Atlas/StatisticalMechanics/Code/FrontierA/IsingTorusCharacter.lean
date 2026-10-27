import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
open Finset StatMech StatMech.FrontierA


/--
[isingTorusCharacterDispersion_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean)
-/
@[path]
private lemma isingTorusCharacterDispersion_nonneg_eq
  {d k : Nat}
  {chi : AddChar (IsingDyadicTorus d k) Complex} :
-- imply
  0 ≤ isingTorusCharacterDispersion chi := by
-- proof
  apply StatMech.FrontierA.isingTorusCharacterDispersion_nonneg chi

/--
[isingTorusDirichlet_re_add_im_addChar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean)
-/
@[path]
private lemma isingTorusDirichlet_re_add_im_addChar_eq
  {d k : Nat}
  {chi : AddChar (IsingDyadicTorus d k) Complex} :
-- imply
  isingTorusDirichlet (fun x => (chi x).re) + isingTorusDirichlet (fun x => (chi x).im) = Fintype.card (IsingDyadicTorus d k) * isingTorusCharacterDispersion chi := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichlet_re_add_im_addChar chi

/--
[isingTorusDirichletBilinearComplex_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean)
-/
@[path]
private lemma isingTorusDirichletBilinearComplex_re_eq
  {d k : Nat}
  {u : IsingDyadicTorus d k → Real}
  {v : IsingDyadicTorus d k → Complex} :
-- imply
  (isingTorusDirichletBilinearComplex u v).re = isingTorusDirichletBilinear u (fun x => (v x).re) := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichletBilinearComplex_re u v

/--
[isingTorusDirichletBilinearComplex_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean)
-/
@[path]
private lemma isingTorusDirichletBilinearComplex_im_eq
  {d k : Nat}
  {u : IsingDyadicTorus d k → Real}
  {v : IsingDyadicTorus d k → Complex} :
-- imply
  (isingTorusDirichletBilinearComplex u v).im = isingTorusDirichletBilinear u (fun x => (v x).im) := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichletBilinearComplex_im u v

/--
[isingTorusDirichletBilinearComplex_addChar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean)
-/
@[path]
private lemma isingTorusDirichletBilinearComplex_addChar_eq
  {d k : Nat}
  {u : IsingDyadicTorus d k → Real}
  {chi : AddChar (IsingDyadicTorus d k) Complex} :
-- imply
  isingTorusDirichletBilinearComplex u chi = (isingTorusCharacterDispersion chi : Complex) * ∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichletBilinearComplex_addChar u chi

/--
[isingTorusDirichletBilinear_re_addChar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean)
-/
@[path]
private lemma isingTorusDirichletBilinear_re_addChar_eq
  {d k : Nat}
  {u : IsingDyadicTorus d k → Real}
  {chi : AddChar (IsingDyadicTorus d k) Complex} :
-- imply
  isingTorusDirichletBilinear u (fun x => (chi x).re) = isingTorusCharacterDispersion chi * (∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x).re := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichletBilinear_re_addChar u chi

/--
[isingTorusDirichletBilinear_im_addChar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean)
-/
@[path]
private lemma isingTorusDirichletBilinear_im_addChar_eq
  {d k : Nat}
  {u : IsingDyadicTorus d k → Real}
  {chi : AddChar (IsingDyadicTorus d k) Complex} :
-- imply
  isingTorusDirichletBilinear u (fun x => (chi x).im) = isingTorusCharacterDispersion chi * (∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x).im := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichletBilinear_im_addChar u chi

/--
[isingTorus_addChar_secondMoment_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean)
-/
@[path]
private lemma isingTorus_addChar_secondMoment_le_eq
  {d k : Nat}
  {beta : Real}
  {chi : AddChar (IsingDyadicTorus d k) Complex}
-- given
  (hbeta : 0 < beta)
  (hdom : IsingTorusGaussianDominated (d := d) (k := k) beta)
  (hdisp : 0 < isingTorusCharacterDispersion chi) :
-- imply
  (∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * Complex.normSq (∑ x : IsingDyadicTorus d k, (isingTorusSpinField sigma x : Complex) * chi x)) ≤ isingTorusShiftedPartition (d := d) (k := k) beta 0 * (Fintype.card (IsingDyadicTorus d k) / (beta * isingTorusCharacterDispersion chi)) := by
-- proof
  apply StatMech.FrontierA.isingTorus_addChar_secondMoment_le beta hbeta hdom chi hdisp

/--
[finiteTorusFourierCoeff_isingTorusAveragedTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean)
-/
@[path]
private lemma finiteTorusFourierCoeff_isingTorusAveragedTwoPoint_eq
  {d k : Nat}
  {beta : Real}
  {chi : AddChar (IsingDyadicTorus d k) Complex} :
-- imply
  finiteTorusFourierCoeff (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi = ((∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * Complex.normSq (∑ x : IsingDyadicTorus d k, (isingTorusSpinField sigma x : Complex) * chi x)) / (isingTorusShiftedPartition (d := d) (k := k) beta 0 * Fintype.card (IsingDyadicTorus d k)) : Real) := by
-- proof
  apply StatMech.FrontierA.finiteTorusFourierCoeff_isingTorusAveragedTwoPoint beta chi

/--
[isingTorusAveragedTwoPoint_fourier_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacter.lean)
-/
@[path]
private lemma isingTorusAveragedTwoPoint_fourier_bound_eq
  {d k : Nat}
  {beta : Real}
  {chi : AddChar (IsingDyadicTorus d k) Complex}
-- given
  (hbeta : 0 < beta)
  (hdom : IsingTorusGaussianDominated (d := d) (k := k) beta)
  (hdisp : 0 < isingTorusCharacterDispersion chi) :
-- imply
  0 ≤ (finiteTorusFourierCoeff (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi).re ∧ (finiteTorusFourierCoeff (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi).re ≤ 1 / (beta * isingTorusCharacterDispersion chi) := by
-- proof
  apply StatMech.FrontierA.isingTorusAveragedTwoPoint_fourier_bound beta hbeta hdom chi hdisp


-- created on 2026-10-23
