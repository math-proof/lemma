import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot
open StatMech StatMech.Universality


/--
[isingBinomialWeight_sub_pred_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean)
-/
@[path]
private lemma isingBinomialWeight_sub_pred_le_eq
  {n k : Nat}
-- given
  (hk : k ≤ n / 2) :
-- imply
  isingBinomialWeight n k - isingBinomialWeightPrev n k ≤ 4 / (n + 1 : Real) := by
-- proof
  apply StatMech.Universality.isingBinomialWeight_sub_pred_le n k hk

/--
[isingLineBinomialKernel_adjacentStart_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean)
-/
@[path]
private lemma isingLineBinomialKernel_adjacentStart_sub_le_eq
  {t : Nat}
  {x y : Int}
-- given
  (hy : y < x + 1) :
-- imply
  isingLineBinomialKernel t x y - isingLineBinomialKernel t (x + 2) y ≤ 4 / (t + 1 : Real) := by
-- proof
  apply StatMech.Universality.isingLineBinomialKernel_adjacentStart_sub_le t x y hy

/--
[horizontalNoHitEndpoint_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean)
-/
@[path]
private lemma horizontalNoHitEndpoint_weight_le_eq
  {t : Nat}
  {level target : Int} :
-- imply
  Nat.card (IsingHorizontalNoHitEndpointFamily t level target) / (2 : Real) ^ t ≤ 4 / (t + 1 : Real) := by
-- proof
  apply StatMech.Universality.horizontalNoHitEndpoint_weight_le t level target


-- created on 2026-10-23
