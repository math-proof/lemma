import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.TorusConnected
open SimpleGraph StatMech StatMech.BeffaraDC


/--
[onsTorusGraph_eq_cycleGraph_boxProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusConnected.lean)
-/
@[path]
private lemma onsTorusGraph_eq_cycleGraph_boxProd_eq
  {n : ℕ}
  [Fact (2 < n + 1)] :
-- imply
  onsTorusGraph (n + 1) = cycleGraph (n + 1) □ cycleGraph (n + 1) := by
-- proof
  apply StatMech.BeffaraDC.onsTorusGraph_eq_cycleGraph_boxProd n

/--
[onsTorusGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusConnected.lean)
-/
@[path]
private lemma onsTorusGraph_connected_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  (onsTorusGraph L).Connected := by
-- proof
  apply StatMech.BeffaraDC.onsTorusGraph_connected L


-- created on 2026-10-23
