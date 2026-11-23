-- Carved from Lemma/Definitions/Def_ModularCurve_JZeroSemistableSpecialization.lean: instance decls only.
module

public import Theorem.ResidueField.GluedPic0
public import Theorem.Scheme.GluedPic0Functoriality
public import Instance.ModularCurve_ArithmeticGalois
public import Theorem.HahnSeries.JqCoeff
public import Def.HeckeGalois_EichlerShimura
public import Theorem.Finset.ComponentGroup
@[expose] public section

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
