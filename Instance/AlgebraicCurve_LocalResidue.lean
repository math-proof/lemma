-- Carved from Lemma/Definitions/Def_AlgebraicCurve_LocalResidue.lean: instance decls only.
import Mathlib
import Lemma.Scheme.CanonicalDivisorUniformizer
import Class.AlgebraicCurve_CanonicalDivisor
import Lemma.AlgebraicCurve.AdelicIndex
import Structure.AlgebraicCurve_LocalResidue
import Class.AlgebraicCurve_LocalResidue

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

instance (priority := 100) instHasLocalResidue_of_hasCanonicalLocalResidueK
    [HasCanonicalLocalResidueK K F] : HasLocalResidue K F :=
  ⟨fun v => (HasCanonicalLocalResidueK.exists_data v).map (·.toLocalResidueData)⟩

instance (priority := 100) instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
    [HasCanonicalLocalResidueKStar K F] : HasCanonicalLocalResidueK K F :=
  ⟨fun v => ⟨HasCanonicalLocalResidueKStar.dataKStar v⟩⟩


variable [HasCanonicalLocalResidueKStar K F]


end AlgebraicCurve

end
