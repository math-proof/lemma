module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.EllipticCurves.code.ModularInvariants
open Complex ModularInvariants
open scoped UpperHalfPlane


public section

namespace ModularInvariants

/--
[Δ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularInvariants.lean)
-/
@[path]
theorem Δ_eq (τ : ℍ) : Δ τ = g₂ τ ^ 3 - 27 * g₃ τ ^ 2 :=
  rfl

end ModularInvariants

namespace ModularInvariants

/--
[j_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularInvariants.lean)
-/
@[path]
theorem j_eq
  {τ : ℍ} :
-- imply
  j τ = 1728 * (ComplexLattice.ofUpperHalfPlane τ).g₂ ^ 3 / (ComplexLattice.ofUpperHalfPlane τ).discriminantLattice :=
-- proof
  rfl
end ModularInvariants



-- created on 2026-10-23
