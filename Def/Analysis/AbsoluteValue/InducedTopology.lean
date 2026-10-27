import Mathlib.Analysis.AbsoluteValue.Equivalence
/-!
# Topology induced by an absolute value

This module ports ATLAS `NumberTheoryI` N176 / Corollary 8.6.
Given an absolute value `v` on a field `K`, the carrier map
`WithAbs.toAbs v : K → WithAbs v` pulls the norm topology on `WithAbs v`
back to `K`. The main theorem characterizes equality of these carrier
topologies, not equality of absolute values: two absolute values induce
the same topology on `K` if and only if they are equivalent.
-/


namespace AbsoluteValue

variable {K : Type*} [Field K]

/-- Topology on the carrier field induced by the norm topology on `WithAbs v`. -/
@[reducible]
noncomputable def inducedTopology (v : AbsoluteValue K ℝ) : TopologicalSpace K :=
  letI : NormedRing (WithAbs v) := WithAbs.normedRing v
  TopologicalSpace.induced (WithAbs.toAbs v) inferInstance

end AbsoluteValue
