-- Carved from Lemma/Definitions/Def_ModularCurve_JZeroSemistableSpecialization.lean: instance decls only.
import Lemma.AlgebraicCurve.GluedPic0
import Lemma.AlgebraicCurve.GluedPic0Functoriality
import Instance.ModularCurve_ArithmeticGalois
import Lemma.ModularCurve.JqCoeff
import Def.HeckeGalois_EichlerShimura
import Lemma.ModularCurve.ComponentGroup

noncomputable section

namespace ModularCurve

open AlgebraicCurve IsLocalRing


section Semistable

variable (A : ValuationSubring Qbar) (N q : ℕ) (hq : q.Prime) [NeZero N]

noncomputable local instance instDecidableEqResidueFieldSemistable :
    DecidableEq (ResidueField A) :=
  Classical.decEq _

set_option synthInstance.maxHeartbeats 80000 in

noncomputable local instance instAlgebraResidueFieldModularFunctionFieldCSemistable :
    Algebra (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
  inferInstance

variable [Module HeckeAlg (JZero (N * q))] [Module HeckeAlg (JZero N)]

end Semistable

end ModularCurve

end
