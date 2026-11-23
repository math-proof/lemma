import Mathlib
import Lemma.Matrix.LocalHeckeInstance
import Lemma.Matrix.IntegralSubgroupOpen
import Instance.AbstractHeckeOperator
import Def.AbstractHeckeOperator_Main

set_option autoImplicit false

open Matrix MulAction
open scoped Pointwise

namespace LocalGL2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

def unipotentR (b : R) : GL (Fin 2) R :=
  ⟨!![1, b; 0, 1], !![1, -b; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def weylR : GL (Fin 2) R :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def unipotentInt (K : Type*) [Field K] [Algebra R K] (b : R) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.map (algebraMap R K) (unipotentR b)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
def weylInt (R K : Type*) [CommRing R] [Field K] [Algebra R K] : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.map (algebraMap R K) (weylR (R := R))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
variable (ϖ : R)

section Defs

variable (hϖ0 : algebraMap R K ϖ ≠ 0)

def diagPi : GL (Fin 2) K :=
  ⟨!![algebraMap R K ϖ, 0; 0, 1], !![(algebraMap R K ϖ)⁻¹, 0; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hϖ0], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ hϖ0]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
def localRepSome (b : R) : GL (Fin 2) K :=
  unipotentInt K b * diagPi ϖ hϖ0

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
def localRepInf : GL (Fin 2) K :=
  weylInt R K * diagPi ϖ hϖ0 * weylInt R K

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
def heckeMulSet : Set (GL (Fin 2) K) :=
  (integralSubgroup R K : Set (GL (Fin 2) K)) * ({diagPi ϖ hϖ0} : Set (GL (Fin 2) K))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
noncomputable def localHeckeOperator (hϖirr : Irreducible ϖ)
    [Finite (R ⧸ Ideal.span {ϖ})]
    {A : Type*} [AddCommMonoid A] [DistribMulAction (GL (Fin 2) K) A]
    (S : Type*) [Ring S] [Module S A] [SMulCommClass (GL (Fin 2) K) S A] :
    MulAction.fixedPoints (integralSubgroup R K) A
      →ₗ[S] MulAction.fixedPoints (integralSubgroup R K) A :=
  AbstractHeckeOperator.HeckeOperator (R := S) (diagPi ϖ hϖ0) (integralSubgroup R K)
    (integralSubgroup R K) (finite_image_mul_diagPi ϖ hϖ0 hϖirr)

omit [IsDomain R] [IsDiscreteValuationRing R] in

end Defs

end LocalGL2
