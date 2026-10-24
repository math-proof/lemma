import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianSignedCumulants
open Filter Topology StatMech StatMech.FrontierA StatMech.FrontierA.PhysicalIsing


/--
[criticalFiniteBoxWeightedSignedScaledCumulant_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianSignedCumulants.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedSignedScaledCumulant_tendsto_zero_eq
  {d order : Nat}
-- given
  (hd : 4 < d)
  (horder : Not (order = 2))
  (positive negative signed : (n : Nat) -> sctBox d n -> Real)
  (hsigned : forall n, signed n = positive n - negative n)
  (hnonneg : forall (i : Fin (order + 1)) n x, 0 <= positive n x + ((i : Nat) : Real) * negative n x)
  (hbounded : forall (i : Fin (order + 1)) n x, positive n x + ((i : Nat) : Real) * negative n x <= 1)
  (hF : forall (i : Fin (order + 1)) n, FiniteIsingWeightedHadamardFactorization (G := sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (positive n + (((i : Nat) : Real) • negative n)))
  (variance : Fin (order + 1) -> Real)
  (hvariance : forall i : Fin (order + 1), Tendsto (fun n => criticalFiniteBoxWeightedScaledCumulant d n (by omega) (positive n + (((i : Nat) : Real) • negative n)) 2) atTop (nhds (variance i))) :
-- imply
  Tendsto (fun n => criticalFiniteBoxWeightedScaledCumulant d n (by omega) (signed n) order) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.PhysicalIsing.criticalFiniteBoxWeightedSignedScaledCumulant_tendsto_zero d order hd horder positive negative signed hsigned hnonneg hbounded hF variance hvariance


-- created on 2026-10-23
