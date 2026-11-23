module

public import Mathlib
public import Def.AlgebraicCurve_ConstantReduction
public import Structure.AlgebraicCurve_RegularProlongation

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]


namespace ConstantReduction

variable {A F Fbar}

@[reducible] def toRegularProlongation (R : ConstantReduction A F Fbar) : RegularProlongation A F Fbar where
  integers := R.integers
  residue := R.residue
  algebraMap_mem_iff := R.algebraMap_mem_iff
  residue_surjective := R.residue_surjective
  ker_residue := R.ker_residue
  residue_algebraMap := R.residue_algebraMap
  exists_smul_mem := R.exists_smul_mem

end ConstantReduction

end AlgebraicCurve

end

end
