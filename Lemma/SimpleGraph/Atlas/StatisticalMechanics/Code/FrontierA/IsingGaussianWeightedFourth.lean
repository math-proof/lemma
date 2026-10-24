import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedFourth
open Filter Finset Topology StatMech StatMech.FrontierA


/--
[finiteParityFourthUrsell_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedFourth.lean)
-/
@[path]
private lemma finiteParityFourthUrsell_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e) :
-- imply
  finiteParityFourthUrsell G beta J i j k l <= 0 := by
-- proof
  apply StatMech.FrontierA.finiteParityFourthUrsell_nonpos G beta J hbeta hJ i j k l

/--
[finiteWeightedParityFourthCumulant_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedFourth.lean)
-/
@[path]
private lemma finiteWeightedParityFourthCumulant_bounds_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {M : Real}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (a : V -> Real)
  (hM : 0 <= M)
  (ha0 : forall i, 0 <= a i)
  (haM : forall i, a i <= M) :
-- imply
  0 <= -finiteWeightedParityFourthCumulant G beta J a ∧ -finiteWeightedParityFourthCumulant G beta J a <= M ^ 4 * (-(∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V, finiteParityFourthUrsell G beta J i j k l)) := by
-- proof
  apply StatMech.FrontierA.finiteWeightedParityFourthCumulant_bounds G beta J hbeta hJ a M hM ha0 haM

/--
[scalarFourthCumulant_finiteWeightedParity_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedFourth.lean)
-/
@[path]
private lemma scalarFourthCumulant_finiteWeightedParity_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (a : V -> Real) :
-- imply
  scalarFourthCumulant (finiteWeightedParityFourthMoment G beta J a) (finiteWeightedParitySecondMoment G beta J a) = finiteWeightedParityFourthCumulant G beta J a := by
-- proof
  apply StatMech.FrontierA.scalarFourthCumulant_finiteWeightedParity_eq G beta J a

/--
[criticalFiniteBoxWeightedParityFourthCumulant_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedFourth.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedParityFourthCumulant_bounds_eq
  [Fintype V]
  [DecidableEq V]
  {d n : Nat}
-- given
  (hd : 2 <= d)
  (a : sctBox d n -> Real)
  (ha0 : forall i, 0 <= a i)
  (ha1 : forall i, a i <= 1) :
-- imply
  0 <= -criticalFiniteBoxWeightedParityFourthCumulant d n a ∧ -criticalFiniteBoxWeightedParityFourthCumulant d n a <= -criticalFiniteBoxGlobalParityFourthCumulant d n := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxWeightedParityFourthCumulant_bounds d n hd a ha0 ha1

/--
[criticalFiniteBoxWeightedNormalizedFourthCumulant_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedFourth.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedNormalizedFourthCumulant_bounds_eq
  [Fintype V]
  [DecidableEq V]
  {d n : Nat}
-- given
  (hd : 2 <= d)
  (a : sctBox d n -> Real)
  (ha0 : forall i, 0 <= a i)
  (ha1 : forall i, a i <= 1) :
-- imply
  0 <= -criticalFiniteBoxWeightedNormalizedFourthCumulant d n a ∧ -criticalFiniteBoxWeightedNormalizedFourthCumulant d n a <= -criticalFiniteBoxGlobalNormalizedFourthCumulant d n := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxWeightedNormalizedFourthCumulant_bounds d n hd a ha0 ha1

/--
[criticalFiniteBoxWeightedNormalizedFourthCumulant_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedFourth.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedNormalizedFourthCumulant_tendsto_zero_eq
  [Fintype V]
  [DecidableEq V]
  {d : Nat}
-- given
  (hd : 4 < d)
  (a : (n : Nat) -> sctBox d n -> Real)
  (ha0 : forall n i, 0 <= a n i)
  (ha1 : forall n i, a n i <= 1) :
-- imply
  Tendsto (fun n => criticalFiniteBoxWeightedNormalizedFourthCumulant d n (a n)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxWeightedNormalizedFourthCumulant_tendsto_zero d hd a ha0 ha1


-- created on 2026-10-23
