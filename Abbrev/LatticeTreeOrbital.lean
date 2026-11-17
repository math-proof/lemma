module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Data.Complex.Basic
public import Structure.LatticeTreeOrbital

@[expose] public section

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

section Helpers

variable {α : Type*} [CommRing α]

end Helpers

variable (R : Type*) [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]


attribute [local simp] mem_stdLattice


end LT.LatticeTree

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one

open Module
open scoped LinearAlgebra.Projectivization

section ResiduePlane

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

end ResiduePlane

section NeighbourFamily

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

end NeighbourFamily

section Gates

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

end Gates

section PadicGates

end PadicGates

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one

variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [Algebra R K]


namespace IntegralAut

end IntegralAut


abbrev twistedLatticeMap (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K)
    (L : Submodule R (Fin 2 → K)) : Submodule R (Fin 2 → K) :=
  latticeMap δ (latticeGal σ L)

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree


variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]


attribute [local simp] mem_fixedVertexSet

section Engine

variable [IsFractionRing R K]

end Engine

section Dichotomy

variable [IsFractionRing R K]

end Dichotomy

section Rigidity

variable [IsFractionRing R K]

end Rigidity

section FullLattice

variable [IsFractionRing R K]

end FullLattice

section PadicGates

end PadicGates

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree


variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

section FundamentalLemma

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']

end FundamentalLemma

end LT.LatticeTree
