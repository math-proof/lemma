import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Basis_tensorProduct_tensorProduct_linearIndependent_restrictScalars.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing K] [Algebra R K] [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
  {n : ℕ}
  {b : Module.Basis (Fin n) K A}
-- given
  (hinj : Function.Injective (algebraMap R K)) :
-- imply
  LinearIndependent R ((b.tensorProduct (b.tensorProduct b)) :
      Fin n × Fin n × Fin n → A ⊗[K] (A ⊗[K] A)) :=
-- proof
  (b.tensorProduct (b.tensorProduct b)).linearIndependent.restrict_scalars
    (Algebra.algebraMap_eq_smul_one' (R := R) (A := K) ▸ hinj)


-- created on 2026-10-05
