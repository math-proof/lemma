import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryApartmentExchange
open IsometryBuilding


/--
[standardApartments_simplices_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/IsometryApartmentExchange.lean)
-/
@[path]
private lemma standardApartments_simplices_eq_eq
  [CommRing k]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
  {n : ℕ}
  {A₁ : Apartment B n}
  {A₂ : Apartment B n}
-- given
  (hA₁ : A₁ ∈ standardApartments B n)
  (hA₂ : A₂ ∈ standardApartments B n) :
-- imply
  A₁.simplices = A₂.simplices := by
-- proof
  apply IsometryBuilding.standardApartments_simplices_eq B n A₁ hA₁ A₂ hA₂


-- created on 2026-10-23
