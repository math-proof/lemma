/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/Algebra/ContinuousSemilinearRepresentation.lean -/

module

public import Class.Topology.Algebra.ContinuousSemilinearRepresentation
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Int
public import Theorem.MathlibExtTest.Topology.Algebra.ContinuousSemilinearRepresentation

@[expose] public section

-- A closed instance confirms that the conditions are jointly inhabitable.
instance : MulSemiringAction PUnit Int where
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

instance : ContinuousSMul PUnit Int where
  continuous_smul := continuous_of_discreteTopology

