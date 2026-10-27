import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingLatticeGreenBlockDecay
open Filter Set Topology StatMech StatMech.FrontierA


/--
[isingLatticeGreenAxisBlockAverage_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingLatticeGreenBlockDecay.lean)
-/
@[path]
private lemma isingLatticeGreenAxisBlockAverage_tendsto_zero_eq
  {d : Nat}
  {i : Fin d}
-- given
  (hd : 2 < d) :
-- imply
  Tendsto (isingLatticeGreenAxisBlockAverage i) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.isingLatticeGreenAxisBlockAverage_tendsto_zero hd i


-- created on 2026-10-23
