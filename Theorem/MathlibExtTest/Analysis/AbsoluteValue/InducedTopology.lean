/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/AbsoluteValue/InducedTopology.lean -/


import Theorem.Analysis.AbsoluteValue.InducedTopology


namespace AbsoluteValue

variable {K : Type*} [Field K]

example (v w : AbsoluteValue K ℝ) :
    v.inducedTopology = w.inducedTopology ↔ v.IsEquiv w :=
  inducedTopology_eq_iff_isEquiv v w

example {v w : AbsoluteValue K ℝ} (h : v.IsEquiv w) :
    v.inducedTopology = w.inducedTopology :=
  (inducedTopology_eq_iff_isEquiv v w).mpr h

example (v : AbsoluteValue K ℝ) : v.inducedTopology =
    letI : NormedRing (WithAbs v) := WithAbs.normedRing v
    TopologicalSpace.induced (WithAbs.toAbs v) inferInstance :=
  rfl

example (v : AbsoluteValue K ℝ) : v.IsEquiv v :=
  (inducedTopology_eq_iff_isEquiv v v).mp rfl

end AbsoluteValue
