/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/Algebra/ContinuousSemilinearRepresentation.lean -/


import Class.Topology.Algebra.ContinuousSemilinearRepresentation
import Mathlib.Algebra.Module.PUnit
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Int
import Theorem.MathlibExtTest.Topology.Algebra.ContinuousSemilinearRepresentation


-- A closed instance confirms that the conditions are jointly inhabitable.
instance : MulSemiringAction PUnit Int where
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

instance : ContinuousSMul PUnit Int where
  continuous_smul := continuous_of_discreteTopology

