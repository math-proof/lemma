module

public import Def.ModularCurve_JqCoeff
public import Def.ModularCurve_LaurentCoeff
public import Instance.ModularCurve_PhiGen
public import Class.AlgebraicCurve_DivisorClassGroup
public import Structure.ModularCurve_FibreModel
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

public noncomputable section

namespace ModularCurve
namespace CharPModel

open AlgebraicCurve

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)

structure FibreModel.CuspChart (fm : FibreModel N A ℓ k red) : Prop where

  tBar_mem : jNBar N * ((jBar N)⁻¹) ^ N ∈ fm.BInf

  piInf_t :
    fm.piInf ⟨jNBar N * ((jBar N)⁻¹) ^ N, tBar_mem⟩ =
      (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) *
        ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N))⁻¹ ^ N

end CharPModel
end ModularCurve
