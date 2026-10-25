import Mathlib
import Lemma.AlgebraicGeometry.ModulesSectionsTensor
import Instance.AlgebraicGeometry_ModulesGlueOfCocycle

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type u}

namespace GlueOfCocycle


end GlueOfCocycle

open GlueOfCocycle

structure UnitCocycle (U : ι → X.Opens) where

  u : ∀ i j, Γ(X, U i ⊓ U j)

  refl : ∀ i, u i i = 1

  cocycle : ∀ i j k,
    rO (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j) (u i j) *
      rO (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k) (u j k) =
    rO (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k) (u i k)

namespace UnitCocycle

variable {U : ι → X.Opens} (c : UnitCocycle U)


variable (U) in


end UnitCocycle

namespace GlueOfCocycle

variable {U : ι → X.Opens} (c : UnitCocycle U) (T : X.Opens)


variable {c T}


variable (c T)


variable {T}


set_option maxHeartbeats 400000 in

end GlueOfCocycle

variable {U : ι → X.Opens}


end AlgebraicGeometry.Scheme.Modules
