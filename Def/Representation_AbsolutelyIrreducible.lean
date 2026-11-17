module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Class.Representation_AbsolutelyIrreducible

@[expose] public section

set_option autoImplicit false

section

open LinearMap
open scoped TensorProduct

namespace Representation

universe u

variable {R V G : Type*} [CommRing R] [AddCommMonoid V] [Module R V] [Group G]

noncomputable def baseChange (R' : Type*) [CommRing R'] [Algebra R R'] (ρ : Representation R G V)
    : Representation R' G (R' ⊗[R] V) where
  toFun g := LinearMap.baseChange R' (ρ g)
  map_one' := by aesop
  map_mul' := by aesop

end Representation

end
