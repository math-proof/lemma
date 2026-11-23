/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Topology/Algebra/ContinuousSemilinearRepresentation.lean -/
module

public import Class.Topology.Algebra.ContinuousSemilinearRepresentation
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Int
public import Instance.MathlibExtTest.Topology.Algebra.ContinuousSemilinearRepresentation

public section

example : IsContinuousSemilinearRepresentation PUnit Int Int where
  smul_distrib_smul := fun _ _ _ => by simp
  isHomeomorph_equivFun :=
    Equiv.isHomeomorph_of_discrete (Module.Free.chooseBasis Int Int).equivFun.toEquiv

