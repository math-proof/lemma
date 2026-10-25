import Def.ModularCurve_JqCoeff
import Def.ModularCurve_LaurentCoeff
import Instance.ModularCurve_PhiGen
import Class.AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace CharPModel

open AlgebraicCurve

variable (N : ℕ) [NeZero N]

def jBar : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full N (jq_mem N))⟩

def jNBar : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

variable (A : ValuationSubring (AlgebraicClosure ℚ))

def constantsHom : A →+* laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) :=
  (algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N))).comp A.subtype

def affineBaseFin : Subring (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :=
  Subring.closure (Set.range (constantsHom N A) ∪ {jBar N})

def affineBaseInf : Subring (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :=
  Subring.closure (Set.range (constantsHom N A) ∪ {(jBar N)⁻¹})

end CharPModel

end ModularCurve

end
