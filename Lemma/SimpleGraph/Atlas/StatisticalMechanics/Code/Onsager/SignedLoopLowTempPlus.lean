import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus.Part3
open Finset SimpleGraph MeasureTheory StatMech StatMech.Onsager


/--
[sum_bond_finset_eq_card_sub_two_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempPlus.lean)
-/
@[path]
private lemma sum_bond_finset_eq_card_sub_two_cut_eq
  {B : Finset (Sym2 V)}
  {config : ConfigSpace V} :
-- imply
  (∑ edge ∈ B, bond config edge) = (B.card : Real) - 2 * (ons_fvCutEdges B config).card := by
-- proof
  apply StatMech.Onsager.sum_bond_finset_eq_card_sub_two_cut B config

/--
[fvWeight_zero_eq_lowTempCutWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempPlus.lean)
-/
@[path]
private lemma fvWeight_zero_eq_lowTempCutWeight_eq
  {d n : Nat}
  {eta : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
  {beta : Real}
-- given
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  fvWeight eta n B beta 0 tau = Real.exp (beta * B.card) * Real.exp (-2 * beta) ^ (ons_fvCutEdges B (glue eta tau)).card := by
-- proof
  apply StatMech.Onsager.fvWeight_zero_eq_lowTempCutWeight d n eta B beta tau

/--
[ons_plusLowTempPathSign_eq_spin_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempPlus.lean)
-/
@[path]
private lemma ons_plusLowTempPathSign_eq_spin_mul_eq
  {d : Nat}
  {config : ConfigSpace (Site d)}
  {u v : Site d}
  {path : (hypercubicLattice d).Walk u v} :
-- imply
  ons_plusLowTempPathSign config path = spin config u * spin config v := by
-- proof
  apply StatMech.Onsager.ons_plusLowTempPathSign_eq_spin_mul config path

/--
[integral_plusMeasure_twoPoint_eq_lowTempPathRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempPlus.lean)
-/
@[path]
private lemma integral_plusMeasure_twoPoint_eq_lowTempPathRatio_eq
  {d n : Nat}
  {beta : Real}
  {u v : Site d}
  {path : (hypercubicLattice d).Walk u v} :
-- imply
  (∫ config, spin config u * spin config v ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) = ons_plusLowTempPathNumerator d n beta path / ons_plusLowTempContourDenominator d n beta := by
-- proof
  apply StatMech.Onsager.integral_plusMeasure_twoPoint_eq_lowTempPathRatio d n beta path


-- created on 2026-10-23
