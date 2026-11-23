/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/CountablyMonolithic.lean -/
module

public import Class.Topology.CountablyMonolithic
public import Theorem.Set.CountablyMonolithic
public import Mathlib.Topology.Metrizable.Basic

public section

/-- Every second-countable space is countably monolithic. -/
example (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] :
    CountablyMonolithicSpace X where
  hasCountableNetwork_closure_of_countable _ _ :=
    hasCountableNetwork_of_secondCountable _

/-- Every metrizable space is countably monolithic. -/
example (X : Type*) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] :
    CountablyMonolithicSpace X where
  hasCountableNetwork_closure_of_countable {s} hs := by
    letI : SecondCountableTopology ↥(closure s) :=
      (hs.isSeparable.closure).secondCountableTopology
    exact hasCountableNetwork_of_secondCountable _

