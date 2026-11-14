import Mathlib
import Notation.Mathlib_Algebra_Algebra_Hom
import Instance.Mathlib_Algebra_Algebra_Hom
import Class.Mathlib_Algebra_Algebra_Hom
import Structure.Mathlib_Algebra_Algebra_Hom

section

section semialghom


end semialghom

section semialghomclass

variable (F : Type*) {R S : Type*}
  [CommSemiring R] [CommSemiring S] (φ : R →+* S) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [SemialgHomClass F φ A B]

variable {F} {φ} {A} {B} in

def SemialgHomClass.toSemialgHom (f : F) : A →ₛₐ[φ] B :=
  { (f : A →ₛₗ[φ] B), (f : A →+* B) with }

end semialghomclass

section semialghom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

def SemialgHom.comp {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} {ξ : R →+* T} [RingHomCompTriple φ ψ ξ]
    (g : B →ₛₐ[ψ] C) (f : A →ₛₐ[φ] B) :
    A →ₛₐ[ξ] C where
  __ := LinearMap.comp (SemialgHom.toLinearMap g) (SemialgHom.toLinearMap f)
  __ := RingHom.comp g.toRingHom f.toRingHom

def AlgHom.toSemialgHom {R : Type*} [CommSemiring R] {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    A →ₛₐ[RingHom.id R] B where
  __ := f
  map_smul' _ _ := by simp

def SemialgHom.compAlgHom {T : Type*} [CommSemiring T] {C : Type*} [Semiring C]
    [Algebra T C] {ψ : S →+* T} [Algebra S A] (g : B →ₛₐ[ψ] C) (f : A →ₐ[S] B) :
    A →ₛₐ[ψ] C :=
  g.comp f.toSemialgHom

def SemialgHom.prod {C : Type*} [Semiring C] [Algebra S C] (f : A →ₛₐ[φ] B)
    (g : A →ₛₐ[φ] C) :
    A →ₛₐ[φ] B × C where
  __ := RingHom.prod f.toRingHom g.toRingHom
  map_smul' r x := by simp

def SemialgHom.prodMap {C D : Type*} [Semiring C] [Semiring D]
    [Algebra S C] [Algebra S D] [Algebra R B] (f : A →ₛₐ[φ] C) (g : B →ₛₐ[φ] D) :
    A × B →ₛₐ[φ] C × D :=
  (f.compAlgHom (AlgHom.fst R A B)).prod (g.compAlgHom (AlgHom.snd R A B))

@[simps!]
def SemialgHom.restrictScalars {R S R' S' : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring R'] [CommSemiring S'] [Algebra R R'] [Algebra S S'] {φ : R →+* S}
    (ψ : R' →ₛₐ[φ] S') {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [Algebra R' A] [Algebra S' B] [IsScalarTower R R' A] [IsScalarTower S S' B]
    (f : A →ₛₐ[ψ.toRingHom] B) : A →ₛₐ[φ] B where
  __ := f.toRingHom
  map_smul' r a := by
    have map_smul (m : R') (x : A) : f (m • x) = ψ.toRingHom m • f x :=
      LinearMap.map_smul' f.toLinearMap m x
    have map_smul_ψ (m : R) (x : R') : ψ (m • x) = φ m • ψ x :=
      LinearMap.map_smul' ψ.toLinearMap m x
    have toLinearMap_eq_coe_f : f.toLinearMap = f := rfl
    have toLinearMap_eq_coe_ψ : ψ.toLinearMap = ψ := rfl
    have := map_smul (algebraMap R R' r) a
    simp_all [toLinearMap_eq_coe_f, toLinearMap_eq_coe_ψ,
      Algebra.algebraMap_eq_smul_one, map_smul_ψ, map_one, one_smul]

end semialghom