import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamHeadlineAdapter
open SimpleGraph StatMech StatMech.FrontierA


/--
[grahamStrengthenedGHS_inhomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamHeadlineAdapter.lean)
-/
@[path]
private lemma grahamStrengthenedGHS_inhomogeneous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  ghsiUrsell3 G K hf i j k <= -2 * ghsiCovariance G K hf i k * ghsiCovariance G K hf j k * grahamInhomOne G K hf k := by
-- proof
  apply StatMech.FrontierA.grahamStrengthenedGHS_inhomogeneous G K hf hK hhf i j k

/--
[grahamStrengthenedGHS_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamHeadlineAdapter.lean)
-/
@[path]
private lemma grahamStrengthenedGHS_homogeneous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : Real)
  (hbeta : 0 <= beta)
  (hh : 0 <= h) :
-- imply
  eg_ursell3 G beta h i j k <= -2 * cov2 G beta h i k * cov2 G beta h j k * onePt G beta h k := by
-- proof
  apply StatMech.FrontierA.grahamStrengthenedGHS_homogeneous G beta h hbeta hh i j k


-- created on 2026-10-23
