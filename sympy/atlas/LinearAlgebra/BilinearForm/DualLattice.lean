/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLattice.lean -/

import Mathlib.Algebra.Module.Lattice
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Module

open scoped nonZeroDivisors

open Submodule

variable {A K V : Type*} [CommRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V]
  [IsScalarTower A K V]

/-- The canonical equivalence induced by the bilinear pairing. -/
noncomputable def LinearMap.BilinForm.dualSubmoduleLinearEquiv
    [IsDomain A] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    (hspan : Submodule.span K (M : Set V) = ⊤) :
    (B.dualSubmodule M) ≃ₗ[A] Module.Dual A M :=
  LinearEquiv.ofBijective (B.dualSubmoduleToDual M)
    (B.dualSubmoduleToDual_bijective hB M hspan)
