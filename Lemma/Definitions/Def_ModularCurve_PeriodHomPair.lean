import Lemma.Definitions.Def_ModularCurve_PeriodMap
import Lemma.Definitions.Def_ModularCurve_PeriodMapBundled
import Mathlib.LinearAlgebra.Prod

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace ModularCurve.Period

section JConj

def jConjMat (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![A 0 0, -A 0 1; -A 1 0, A 1 1]

@[simp] theorem jConjMat_apply_zero_zero (A : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat A 0 0 = A 0 0 := by simp [jConjMat]

@[simp] theorem jConjMat_apply_zero_one (A : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat A 0 1 = -A 0 1 := by simp [jConjMat]

@[simp] theorem jConjMat_apply_one_zero (A : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat A 1 0 = -A 1 0 := by simp [jConjMat]

@[simp] theorem jConjMat_apply_one_one (A : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat A 1 1 = A 1 1 := by simp [jConjMat]

theorem jConjMat_det (A : Matrix (Fin 2) (Fin 2) ℤ) : (jConjMat A).det = A.det := by
  rw [jConjMat, Matrix.det_fin_two_of, Matrix.det_fin_two]; ring

theorem jConjMat_trace (A : Matrix (Fin 2) (Fin 2) ℤ) : (jConjMat A).trace = A.trace := by
  rw [jConjMat, Matrix.trace_fin_two_of, Matrix.trace_fin_two]

theorem jConjMat_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat (A * B) = jConjMat A * jConjMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jConjMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem jConjMat_jConjMat (A : Matrix (Fin 2) (Fin 2) ℤ) : jConjMat (jConjMat A) = A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jConjMat]

theorem jConjMat_one : jConjMat (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jConjMat]

def jConjSL : SL(2, ℤ) →* SL(2, ℤ) where
  toFun A := ⟨jConjMat ((A : Matrix (Fin 2) (Fin 2) ℤ)), by rw [jConjMat_det]; exact A.2⟩
  map_one' := by
    apply Subtype.ext
    show jConjMat ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = _
    rw [Matrix.SpecialLinearGroup.coe_one, jConjMat_one]
  map_mul' A B := by
    apply Subtype.ext
    show jConjMat (((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, jConjMat_mul]; rfl

@[simp] theorem jConjSL_coe (A : SL(2, ℤ)) :
    ((jConjSL A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = jConjMat ((A : Matrix (Fin 2) (Fin 2) ℤ)) := rfl

theorem jConjSL_jConjSL (A : SL(2, ℤ)) : jConjSL (jConjSL A) = A := by
  apply Subtype.ext; rw [jConjSL_coe, jConjSL_coe, jConjMat_jConjMat]

theorem jConjSL_mem_Gamma0 {N : ℕ} {A : SL(2, ℤ)} (hA : A ∈ Gamma0 N) :
    jConjSL A ∈ Gamma0 N := by
  have hA' : ((((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 :=
    Gamma0_mem.mp hA
  rw [Gamma0_mem]
  show ((((jConjSL A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0
  rw [jConjSL_coe, jConjMat_apply_one_zero]; push_cast; rw [hA', neg_zero]

variable (N : ℕ)

def jConjGamma0 : Gamma0 N →* Gamma0 N where
  toFun γ := ⟨jConjSL ↑γ, jConjSL_mem_Gamma0 γ.2⟩
  map_one' := by apply Subtype.ext; show jConjSL ↑(1 : Gamma0 N) = _;
                 rw [OneMemClass.coe_one, map_one]
  map_mul' γ δ := by apply Subtype.ext; show jConjSL ↑(γ * δ) = _;
                     rw [MulMemClass.coe_mul, map_mul]; rfl

@[simp] theorem jConjGamma0_coe (γ : Gamma0 N) :
    ((jConjGamma0 N γ : Gamma0 N) : SL(2, ℤ)) = jConjSL ↑γ := rfl

theorem jConjGamma0_jConjGamma0 (γ : Gamma0 N) :
    jConjGamma0 N (jConjGamma0 N γ) = γ := by
  apply Subtype.ext; rw [jConjGamma0_coe, jConjGamma0_coe, jConjSL_jConjSL]

end JConj

section CharInvolution

variable (N : ℕ) (R : Type*) [Semiring R] (A : Type*) [AddCommGroup A] [Module R A]

def charInvolution : (Additive (Gamma0 N) →+ A) →ₗ[R] (Additive (Gamma0 N) →+ A) where
  toFun ψ := ψ.comp (MonoidHom.toAdditive (jConjGamma0 N))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem charInvolution_apply (ψ : Additive (Gamma0 N) →+ A) (γ : Additive (Gamma0 N)) :
    (charInvolution N R A ψ) γ = ψ (Additive.ofMul (jConjGamma0 N (Additive.toMul γ))) := rfl

theorem charInvolution_charInvolution (ψ : Additive (Gamma0 N) →+ A) :
    charInvolution N R A (charInvolution N R A ψ) = ψ := by
  refine AddMonoidHom.ext fun γ => ?_
  show ψ (Additive.ofMul (jConjGamma0 N (jConjGamma0 N (Additive.toMul γ)))) = ψ γ
  rw [jConjGamma0_jConjGamma0]; rfl

theorem charInvolution_mem_parabolicHoms {ψ : Additive (Gamma0 N) →+ A}
    (hψ : ψ ∈ parabolicHoms R (Gamma0 N) A) :
    charInvolution N R A ψ ∈ parabolicHoms R (Gamma0 N) A := by
  rw [mem_parabolicHoms_iff] at hψ ⊢
  intro γ hγ
  refine hψ (jConjGamma0 N γ) ?_
  have htr : (((jConjGamma0 N γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = (((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
    rw [jConjGamma0_coe, jConjSL_coe, jConjMat_trace]
  rw [htr]; exact hγ

end CharInvolution

end ModularCurve.Period

namespace ModularCurve

section PeriodHomPair

open ModularCurve.Period

variable (N : ℕ)

def ExistsPeriodMapLinear : Prop :=
  ∃ pml : CuspForm (Gamma0 N) 2 →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ), ∀ f, pml f = periodMap N f

noncomputable def periodHomPair :
    (CuspForm (Gamma0 N) 2 × CuspForm (Gamma0 N) 2) →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ) :=
  open scoped Classical in
  if h : ExistsPeriodMapLinear N then
    LinearMap.coprod
      ((LinearMap.id + charInvolution N ℂ ℂ) ∘ₗ h.choose)
      ((LinearMap.id - charInvolution N ℂ ℂ) ∘ₗ h.choose)
  else 0

theorem periodHomPair_def (h : ExistsPeriodMapLinear N) :
    ∃ (pml : CuspForm (Gamma0 N) 2 →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ))
      (_ : ∀ f, pml f = periodMap N f),
      periodHomPair N = LinearMap.coprod
        ((LinearMap.id + charInvolution N ℂ ℂ) ∘ₗ pml)
        ((LinearMap.id - charInvolution N ℂ ℂ) ∘ₗ pml) := by
  refine ⟨h.choose, h.choose_spec, ?_⟩
  unfold periodHomPair
  rw [dif_pos h]

end PeriodHomPair

end ModularCurve
