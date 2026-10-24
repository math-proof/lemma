import Mathlib
import Lemma.Definitions.Def_ModularCurve_LevelModuliPackage

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

def j₀ : P.B₀ := D.jOf P.univ

noncomputable def classify {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) : P.B₀ →ₐ[A] T :=
  (P.represents T x).choose

theorem map_classify {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) : D.map (P.classify x) P.univ = x :=
  (P.represents T x).choose_spec.1

theorem classify_unique {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) (φ : P.B₀ →ₐ[A] T)
    (h : D.map φ P.univ = x) : φ = P.classify x :=
  (P.represents T x).unique h (P.map_classify x) ▸ rfl

end LevelModuliPackageAbs

end ModularCurve
