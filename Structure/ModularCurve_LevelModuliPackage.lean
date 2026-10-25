import Mathlib
import Instance.ModularCurve_LevelModuliPackage

set_option autoImplicit false

universe u

namespace ModularCurve

structure LevelModuliDatum (A : Type u) [CommRing A] where

  Pt : (T : Type u) → [CommRing T] → [Algebra A T] → Type u

  map : {T T' : Type u} → [CommRing T] → [Algebra A T] → [CommRing T'] → [Algebra A T'] →
    (T →ₐ[A] T') → Pt T → Pt T'

  map_id : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : Pt T), map (AlgHom.id A T) x = x

  map_comp : ∀ {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T'']
    [Algebra A T''] (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') (x : Pt T), map (g.comp f) x = map g (map f x)

  jOf : {T : Type u} → [CommRing T] → [Algebra A T] → Pt T → T

  jOf_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') (x : Pt T),
    jOf (map f x) = f (jOf x)

namespace LevelModuliDatum

variable {A : Type u} [CommRing A]

structure ProblemAut (D : LevelModuliDatum.{u} A) where

  act : {T : Type u} → [CommRing T] → [Algebra A T] → D.Pt T → D.Pt T

  act_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') (x : D.Pt T),
    act (D.map f x) = D.map f (act x)

  jOf_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T), D.jOf (act x) = D.jOf x


def Twist (_σA : A ≃+* A) (T : Type u) : Type u := T


def AlgHom.twist (σA : A ≃+* A) {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T']
    (f : T →ₐ[A] T') : Twist σA T →ₐ[A] Twist σA T' where
  toRingHom := (f.toRingHom : T →+* T')
  commutes' a := f.commutes (σA a)

structure SemilinearProblemAut (D : LevelModuliDatum.{u} A) (σA : A ≃+* A) where

  act : {T : Type u} → [CommRing T] → [Algebra A T] → D.Pt T → D.Pt (Twist σA T)

  act_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') (x : D.Pt T),
    act (D.map f x) = D.map (AlgHom.twist σA f) (act x)

  jOf_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T),
    @Eq T (D.jOf (T := Twist σA T) (act x)) (D.jOf x)

end LevelModuliDatum

structure LevelModuliPackage (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K)
    (D : LevelModuliDatum.{u} A) where

  B : Subalgebra A K

  j_mem : j ∈ B

  univ : D.Pt ↥B

  jOf_univ : (D.jOf univ : ↥B) = ⟨j, j_mem⟩

  represents : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : D.Pt T), ∃! φ : ↥B →ₐ[A] T, D.map φ univ = x

namespace LevelModuliPackage

variable {A : Type u} [CommRing A] {K : Type u} [Field K] [Algebra A K] {j : K} {D : LevelModuliDatum.{u} A}
  (P : LevelModuliPackage A K j D)


end LevelModuliPackage

end ModularCurve
