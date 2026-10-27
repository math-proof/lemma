import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
open Set StatMech StatMech.Lattice


/--
[adj_update_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentConn.lean)
-/
@[path]
private lemma adj_update_succ_eq
  {d : ℕ}
  {x : Site d}
  {j : Fin d}
  {a : ℤ} :
-- imply
  (hypercubicLattice d).Adj (Function.update x j a) (Function.update x j (a + 1)) := by
-- proof
  apply StatMech.Lattice.adj_update_succ x j a

/--
[segment_connectedWithin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/SegmentConn.lean)
-/
@[path]
private lemma segment_connectedWithin_eq
  {d : ℕ}
  {S : Set (Site d)}
  {j : Fin d}
  {x : Site d}
  {n : ℕ}
-- given
  (hmem : ∀ t ≤ n, Function.update x j (x j + (t : ℤ)) ∈ S) :
-- imply
  ((hypercubicLattice d).induce S).Reachable ⟨Function.update x j (x j + (0 : ℤ)), hmem 0 (Nat.zero_le n)⟩ ⟨Function.update x j (x j + (n : ℤ)), hmem n le_rfl⟩ := by
-- proof
  apply StatMech.Lattice.segment_connectedWithin S j x n hmem


-- created on 2026-10-23
