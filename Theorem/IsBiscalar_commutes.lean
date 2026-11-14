import Mathlib
import Class.Mathlib_IsModuleTopology


theorem IsBiscalar.commutes {S : Type*} (S' : Type*) {A B : Type*} [CommSemiring S']
    [CommSemiring S] [Semiring A] [Semiring B] [Algebra S' A] [Algebra S' B] [Algebra S A]
    [Algebra S B] (f : A →ₐ[S] B) [IsBiscalar S S' f] (s : S') :
    f (algebraMap S' A s) = algebraMap S' B s := by
  simpa [Algebra.algebraMap_eq_smul_one, map_one] using
    IsBiscalar.map_smul₂ (R := S) (S := S') (f := f) s (1 : A)
