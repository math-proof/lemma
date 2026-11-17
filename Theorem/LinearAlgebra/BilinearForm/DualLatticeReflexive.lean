/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLatticeReflexive.lean -/
module

public import Def.LinearAlgebra.BilinearForm.DualLattice
public import Theorem.Matrix.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.TorsionFree
open LinearMap (BilinForm)
open Module

public section

variable {A K V : Type*} [CommRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V]
  [IsScalarTower A K V]


