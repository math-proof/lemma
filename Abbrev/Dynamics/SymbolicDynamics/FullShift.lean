/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean -/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section


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
