-- Carved from Lemma/Definitions/Def_ModularCurve_JZeroGoodReductionV2.lean: instance decls only.
import Mathlib
import Lemma.ModularCurve.HeckeModule
import Instance.ModularCurve_SpecializationWitness
import Lemma.ModularCurve.JqCoeff
import Instance.EllipticCurve_FrobeniusTrace
import Structure.ModularCurve_JZeroGoodReductionV2

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve IsLocalRing

namespace ModularCurve

variable {A : ValuationSubring Qbar} {ℓ : ℕ} {hℓ : ℓ.Prime} {N : ℕ} [NeZero N]

noncomputable local instance instDecEqResidueFieldF3nrp : DecidableEq (ResidueField A) :=
  Classical.decEq _

set_option synthInstance.maxHeartbeats 80000 in

noncomputable local instance instAlgebraResidueFieldModularFunctionFieldCF3nrp :
    Algebra (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
  inferInstance

variable [Module HeckeAlg (JZero N)]

variable [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]

variable (A) (ℓ) (hℓ) (N) in


end ModularCurve

end
