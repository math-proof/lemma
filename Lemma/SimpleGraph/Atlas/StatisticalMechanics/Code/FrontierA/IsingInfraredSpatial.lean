import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredSpatial
open Finset StatMech StatMech.FrontierA


/--
[finiteTorusFourierCoeff_sum_mul_conj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredSpatial.lean)
-/
@[path]
private lemma finiteTorusFourierCoeff_sum_mul_conj_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {G : Gamma → Real}
  {x : Gamma} :
-- imply
  (∑ chi : AddChar Gamma Complex, finiteTorusFourierCoeff G chi * conj (chi x)) = Fintype.card Gamma * G x := by
-- proof
  apply StatMech.FrontierA.finiteTorusFourierCoeff_sum_mul_conj G x

/--
[finiteTorus_fourier_inversion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredSpatial.lean)
-/
@[path]
private lemma finiteTorus_fourier_inversion_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {G : Gamma → Real}
  {x : Gamma} :
-- imply
  (G x : Complex) = (1 / Fintype.card Gamma : Complex) * ∑ chi : AddChar Gamma Complex, finiteTorusFourierCoeff G chi * conj (chi x) := by
-- proof
  apply StatMech.FrontierA.finiteTorus_fourier_inversion G x

/--
[finiteTorus_fourier_difference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredSpatial.lean)
-/
@[path]
private lemma finiteTorus_fourier_difference_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {G : Gamma → Real}
  {x y : Gamma} :
-- imply
  ((G x - G y : Real) : Complex) = (1 / Fintype.card Gamma : Complex) * ∑ chi : AddChar Gamma Complex, finiteTorusFourierCoeff G chi * (conj (chi x) - conj (chi y)) := by
-- proof
  apply StatMech.FrontierA.finiteTorus_fourier_difference G x y

/--
[finiteTorus_fourier_difference_trivial_term_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredSpatial.lean)
-/
@[path]
private lemma finiteTorus_fourier_difference_trivial_term_zero_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {G : Gamma → Real}
  {x y : Gamma} :
-- imply
  finiteTorusFourierCoeff G (0 : AddChar Gamma Complex) * (conj ((0 : AddChar Gamma Complex) x) - conj ((0 : AddChar Gamma Complex) y)) = 0 := by
-- proof
  apply StatMech.FrontierA.finiteTorus_fourier_difference_trivial_term_zero G x y

/--
[finiteTorus_fourier_difference_erase_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredSpatial.lean)
-/
@[path]
private lemma finiteTorus_fourier_difference_erase_zero_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {G : Gamma → Real}
  {x y : Gamma} :
-- imply
  ((G x - G y : Real) : Complex) = (1 / Fintype.card Gamma : Complex) * ∑ chi ∈ (Finset.univ.erase (0 : AddChar Gamma Complex)), finiteTorusFourierCoeff G chi * (conj (chi x) - conj (chi y)) := by
-- proof
  apply StatMech.FrontierA.finiteTorus_fourier_difference_erase_zero G x y

/--
[finiteTorus_fourier_difference_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredSpatial.lean)
-/
@[path]
private lemma finiteTorus_fourier_difference_abs_le_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {G : Gamma → Real}
  {dispersion : AddChar Gamma Complex → Real}
  {C : Real}
  {x y : Gamma}
-- given
  (hbound : ∀ chi : AddChar Gamma Complex, chi ≠ 0 → ‖finiteTorusFourierCoeff G chi‖ ≤ C / dispersion chi) :
-- imply
  |G x - G y| ≤ (1 / Fintype.card Gamma : Real) * ∑ chi ∈ (Finset.univ.erase (0 : AddChar Gamma Complex)), (C / dispersion chi) * ‖conj (chi x) - conj (chi y)‖ := by
-- proof
  apply StatMech.FrontierA.finiteTorus_fourier_difference_abs_le G dispersion C x y hbound

/--
[isingTorusCharacterDispersion_pos_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredSpatial.lean)
-/
@[path]
private lemma isingTorusCharacterDispersion_pos_of_ne_zero_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {d k : Nat}
  {chi : AddChar (IsingDyadicTorus d k) Complex}
-- given
  (hchi : chi ≠ 0) :
-- imply
  0 < isingTorusCharacterDispersion chi := by
-- proof
  apply StatMech.FrontierA.isingTorusCharacterDispersion_pos_of_ne_zero chi hchi

/--
[isingTorusAveragedTwoPoint_fourierCoeff_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredSpatial.lean)
-/
@[path]
private lemma isingTorusAveragedTwoPoint_fourierCoeff_norm_le_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {d k : Nat}
  {beta : Real}
  {chi : AddChar (IsingDyadicTorus d k) Complex}
-- given
  (hbeta : 0 < beta)
  (hchi : chi ≠ 0) :
-- imply
  ‖finiteTorusFourierCoeff (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi‖ ≤ (1 / beta) / isingTorusCharacterDispersion chi := by
-- proof
  apply StatMech.FrontierA.isingTorusAveragedTwoPoint_fourierCoeff_norm_le beta hbeta chi hchi

/--
[isingTorusAveragedTwoPoint_difference_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredSpatial.lean)
-/
@[path]
private lemma isingTorusAveragedTwoPoint_difference_abs_le_eq
  [Fintype Gamma]
  [AddCommGroup Gamma]
  {d k : Nat}
  {beta : Real}
  {x y : IsingDyadicTorus d k}
-- given
  (hbeta : 0 < beta) :
-- imply
  |isingTorusAveragedTwoPoint beta x - isingTorusAveragedTwoPoint beta y| ≤ (1 / Fintype.card (IsingDyadicTorus d k) : Real) * ∑ chi ∈ (Finset.univ.erase (0 : AddChar (IsingDyadicTorus d k) Complex)), ((1 / beta) / isingTorusCharacterDispersion chi) * ‖conj (chi x) - conj (chi y)‖ := by
-- proof
  apply StatMech.FrontierA.isingTorusAveragedTwoPoint_difference_abs_le beta hbeta x y


-- created on 2026-10-23
