import Mathlib
import Instance.ModularCurve_LevelModuliPackage

set_option autoImplicit false

universe u

namespace ModularCurve

structure LevelModuliPackageAbs (A : Type u) [CommRing A] (D : LevelModuliDatum.{u} A) where

  B₀ : Type u

  [instCommRing : CommRing B₀]

  [instAlgebra : Algebra A B₀]

  univ : D.Pt B₀

  represents : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : D.Pt T), ∃! φ : B₀ →ₐ[A] T, D.map φ univ = x

attribute [instance] LevelModuliPackageAbs.instCommRing LevelModuliPackageAbs.instAlgebra

namespace LevelModuliPackageAbs

variable {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P : LevelModuliPackageAbs A D)


end LevelModuliPackageAbs

end ModularCurve
