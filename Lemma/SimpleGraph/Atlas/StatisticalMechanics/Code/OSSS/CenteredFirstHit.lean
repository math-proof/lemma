import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.CenteredFirstHit
open StatMech StatMech.OSSS StatMech.OSSS.CenteredFirstHit


/--
[center_mem_centeredClosedBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CenteredFirstHit.lean)
-/
@[path]
private lemma center_mem_centeredClosedBox_eq
  {d : Nat}
  {u : Site d}
  {m : Nat} :
-- imply
  u ∈ centeredClosedBox u m := by
-- proof
  apply StatMech.OSSS.CenteredFirstHit.center_mem_centeredClosedBox u m

/--
[connected_centeredBoundary_has_within](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CenteredFirstHit.lean)
-/
@[path]
private lemma connected_centeredBoundary_has_within_eq
  {d m : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {u z : Site d}
-- given
  (hz : z ∈ centeredBoundary u m)
  (hconn : Connected d omega u z) :
-- imply
  ∃ z' : centeredClosedBox u m, (z' : Site d) ∈ centeredBoundary u m ∧ ConnectedWithin d omega (centeredClosedBox u m) ⟨u, center_mem_centeredClosedBox u m⟩ z' := by
-- proof
  apply StatMech.OSSS.CenteredFirstHit.connected_centeredBoundary_has_within hz hconn

/--
[connectedToSet_centered_has_within](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CenteredFirstHit.lean)
-/
@[path]
private lemma connectedToSet_centered_has_within_eq
  {d m : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {u : Site d}
-- given
  (hconn : ConnectedToSet d omega u (centeredBoundary u m)) :
-- imply
  ∃ z : centeredClosedBox u m, (z : Site d) ∈ centeredBoundary u m ∧ ConnectedWithin d omega (centeredClosedBox u m) ⟨u, center_mem_centeredClosedBox u m⟩ z := by
-- proof
  apply StatMech.OSSS.CenteredFirstHit.connectedToSet_centered_has_within hconn


-- created on 2026-10-23
