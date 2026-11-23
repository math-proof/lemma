module

public import Def.ModularCurve_QAdicPlace
public import Def.ModularCurve_ArithmeticGalois

@[expose] public section

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve

namespace ModularCurve

section Fricke

variable (N : ℕ) [NeZero N]

def IsFrickeAut (σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N) : Prop :=
  σ ⟨jq, jq_mem N⟩ = ⟨jqN N, jqN_mem N⟩ ∧ σ ⟨jqN N, jqN_mem N⟩ = ⟨jq, jq_mem N⟩

open Classical in

def frickeInvolution : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N :=
  if h : ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ
  then h.choose else AlgEquiv.refl

def cuspZero : Place ℚ (modularFunctionField N) := frickeInvolution N • cuspInfty N

end Fricke

section Full

def IsFrickeAutFull (N : ℕ) [NeZero N]
    (σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N) : Prop :=
  ∀ (a b : ℕ) (hab : a * b = N) (_ : NeZero a) (_ : NeZero b),
    σ ⟨qExpand ℚ a jq, jqd_mem_full N (Dvd.intro b hab)⟩
      = ⟨qExpand ℚ b jq, jqd_mem_full N (Dvd.intro_left a hab)⟩

open Classical in

def frickeInvolutionFull (N : ℕ) [NeZero N] :
    modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N :=
  if h : ∃ σ : modularFunctionFieldFull N ≃ₐ[ℚ] modularFunctionFieldFull N, IsFrickeAutFull N σ
  then h.choose else AlgEquiv.refl

variable (N : ℕ) [NeZero N]

def cuspZeroFull : Place ℚ (modularFunctionFieldFull N) :=
  frickeInvolutionFull N • cuspInftyFull N

end Full

section Bar

variable (N : ℕ) [NeZero N]

def cuspInftyBar : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  qInftyPlaceBar (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
    ⟨⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩,
      order_coeffEmb_jq (AlgebraicClosure ℚ)⟩

end Bar

end ModularCurve

end

end
