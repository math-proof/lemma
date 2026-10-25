-- Carved from Lemma/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean:
-- torsionRep / torsionRep_apply need SemilinearAut→Pic0.torsion instances from Instance.
-- This module imports Instance; Instance must NOT import this module (would cycle).
-- The three public entangled defs smulValuationSubringEquiv / smulResidueRingEquiv /
-- degZeroSMulHom stay in Instance (used inside instance bodies).
import Instance.AlgebraicCurve_BaseChangeGalois
import Mathlib.Algebra.Module.ZMod

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

namespace SemilinearAut

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (K F) in
/-- SemilinearAut action on Pic0 n-torsion as a ZMod n-linear endomorphism. -/
def torsionRep (n : ℕ) : SemilinearAut K F →* Module.End (ZMod n) (Pic0.torsion K F n) :=
  DistribMulAction.toModuleEnd (ZMod n) (Pic0.torsion K F n)

@[simp]
theorem torsionRep_apply {n : ℕ} (g : SemilinearAut K F) (x : Pic0.torsion K F n) :
    torsionRep K F n g x = g • x := rfl

end SemilinearAut

end AlgebraicCurve
