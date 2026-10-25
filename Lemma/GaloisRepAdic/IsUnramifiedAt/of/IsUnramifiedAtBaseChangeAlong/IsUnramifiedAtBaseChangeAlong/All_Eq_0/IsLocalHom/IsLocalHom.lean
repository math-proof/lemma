import Mathlib
import sympy.Basic
import Def.GaloisRep_LocalConditions
import Lemma.Int.P2MUtil

open scoped TensorProduct
open Module

/--
[GaloisRepAdic_isUnramifiedAt_of_jointly_injective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_isUnramifiedAt_of_jointly_injective.lean)
-/

private theorem eq_zero_of_forall_toMatrix_eq_zero {R : Type} [CommRing R] {V : Type}
    [AddCommGroup V] [Module R V] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι R V)
    (T : Module.End R V) (h : ∀ i j, LinearMap.toMatrix b b T i j = 0) : T = 0 :=
  (LinearMap.toMatrix b b).map_eq_zero_iff.mp (Matrix.ext fun i j => by rw [h, Matrix.zero_apply])

private theorem baseChange_eq_zero_iff {R : Type} [CommRing R] {V : Type} [AddCommGroup V]
    [Module R V] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι R V) (B : Type) [CommRing B]
    [Algebra R B] (T : Module.End R V) :
    T.baseChange B = 0 ↔ ∀ i j, algebraMap R B (LinearMap.toMatrix b b T i j) = 0 := by
  rw [← (LinearMap.toMatrix (Algebra.TensorProduct.basis B b)
      (Algebra.TensorProduct.basis B b)).map_eq_zero_iff, LinearMap.toMatrix_baseChange,
    ← Matrix.ext_iff]
  simp only [Matrix.map_apply, Matrix.zero_apply]

private theorem eq_zero_of_baseChange_eq_zero_of_jointly_injective {P A B : Type} [CommRing P]
    [CommRing A] [CommRing B] (πA : P →+* A) (πB : P →+* B)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) {V : Type} [AddCommGroup V] [Module P V]
    [Module.Free P V] [Module.Finite P V] (T : Module.End P V)
    (hA : letI := πA.toAlgebra; T.baseChange A = 0)
    (hB : letI := πB.toAlgebra; T.baseChange B = 0) : T = 0 := by
  classical
  let b := Module.Free.chooseBasis P V
  refine eq_zero_of_forall_toMatrix_eq_zero b T fun i j => hinj _ ?_ ?_
  · letI := πA.toAlgebra
    exact (baseChange_eq_zero_iff b A T).mp hA i j
  · letI := πB.toAlgebra
    exact (baseChange_eq_zero_iff b B T).mp hB i j
@[path]
private lemma main
  {P A B : Type} [CommRing P] [IsLocalRing P] [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  {πA : P →+* A}
  {πB : P →+* B}
  {ρ : GaloisRepAdic P}
  {q : ℕ}
-- given
  (hπA : IsLocalHom πA)
  (hπB : IsLocalHom πB)
  (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0)
  (hA : (ρ.baseChangeAlong πA hπA).IsUnramifiedAt q)
  (hB : (ρ.baseChangeAlong πB hπB).IsUnramifiedAt q) :
-- imply
  ρ.IsUnramifiedAt q := by
-- proof
  intro P' hP' σ hσ
  rw [← sub_eq_zero]
  refine eq_zero_of_baseChange_eq_zero_of_jointly_injective πA πB hinj (ρ.ρ σ - 1) ?_ ?_
  · letI := πA.toAlgebra
    have h1 : (ρ.ρ σ).baseChange A = 1 := hA P' hP' σ hσ
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_one]; exact sub_eq_zero.mpr h1
  · letI := πB.toAlgebra
    have h1 : (ρ.ρ σ).baseChange B = 1 := hB P' hP' σ hσ
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_one]; exact sub_eq_zero.mpr h1


-- created on 2026-10-23
