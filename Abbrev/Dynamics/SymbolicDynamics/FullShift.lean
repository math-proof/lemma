/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Homeomorph.Defs


namespace SymbolicDynamics.FullShift

/-!
# One-dimensional finite full shifts

This file provides a common API for the full two-sided shift on `N` symbols,
its unit shift and automorphism group, and the jointly periodic-point notions
used for one-dimensional cellular automata.
-/

/-- The configuration space of the two-sided full shift on `N` symbols. -/
abbrev FullShiftSpace (N : ℕ) := ℤ → Fin N

end SymbolicDynamics.FullShift
