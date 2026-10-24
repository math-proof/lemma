import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingLatticeGreen
open Filter Set Topology StatMech StatMech.FrontierA


/--
[isingDyadicTorusGreen_cauchySeq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingLatticeGreen.lean)
-/
@[path]
private lemma isingDyadicTorusGreen_cauchySeq_eq
  {d : Nat}
  {x : Site d}
-- given
  (hd : 2 < d) :
-- imply
  CauchySeq (fun k => isingDyadicTorusGreen x k) := by
-- proof
  apply StatMech.FrontierA.isingDyadicTorusGreen_cauchySeq hd x

/--
[isingDyadicTorusGreen_tendsto_latticeGreen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingLatticeGreen.lean)
-/
@[path]
private lemma isingDyadicTorusGreen_tendsto_latticeGreen_eq
  {d : Nat}
  {x : Site d}
-- given
  (hd : 2 < d) :
-- imply
  Tendsto (fun k => isingDyadicTorusGreen x k) atTop (nhds (isingLatticeGreen d x)) := by
-- proof
  apply StatMech.FrontierA.isingDyadicTorusGreen_tendsto_latticeGreen hd x

/--
[isingDyadicGreenAxisBlockAverage_tendsto_latticeGreen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingLatticeGreen.lean)
-/
@[path]
private lemma isingDyadicGreenAxisBlockAverage_tendsto_latticeGreen_eq
  {d : Nat}
  {i : Fin d}
  {r : Nat}
-- given
  (hd : 2 < d) :
-- imply
  Tendsto (isingDyadicGreenAxisBlockAverage i r) atTop (nhds (isingLatticeGreenAxisBlockAverage i r)) := by
-- proof
  apply StatMech.FrontierA.isingDyadicGreenAxisBlockAverage_tendsto_latticeGreen hd i r


-- created on 2026-10-23
