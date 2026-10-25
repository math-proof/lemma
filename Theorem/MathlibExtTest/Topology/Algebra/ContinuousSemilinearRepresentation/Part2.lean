/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/Algebra/ContinuousSemilinearRepresentation.lean -/


import Class.Topology.Algebra.ContinuousSemilinearRepresentation
import Mathlib.Algebra.Module.PUnit
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Int
import Instance.MathlibExtTest.Topology.Algebra.ContinuousSemilinearRepresentation


example : IsContinuousSemilinearRepresentation PUnit Int Int where
  smul_distrib_smul := fun _ _ _ => by simp
  isHomeomorph_equivFun :=
    Equiv.isHomeomorph_of_discrete (Module.Free.chooseBasis Int Int).equivFun.toEquiv

