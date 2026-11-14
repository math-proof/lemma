-- Carved from Lemma/Definitions/Def_ModularCurve_JZeroSemistableSpecialization.lean: instance decls only.
import Lemma.ResidueField.GluedPic0
import Lemma.Scheme.GluedPic0Functoriality
import Instance.ModularCurve_ArithmeticGalois
import Lemma.HahnSeries.JqCoeff
import Def.HeckeGalois_EichlerShimura
import Lemma.Finset.ComponentGroup

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
