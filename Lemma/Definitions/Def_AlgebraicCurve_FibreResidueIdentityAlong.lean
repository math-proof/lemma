import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_LocalResidue
import Lemma.Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Lemma.Definitions.Def_AlgebraicCurve_CechH1PushPull

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def FibreResidueIdentityAlong [HasPrincipalDivisors K F']
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) : Prop :=
  ∀ (v : Place K F) (ω : Ω[F⁄K]) (f' : F'),
    ∑ w ∈ Place.fiberAlong φ hφ v,
        kaehlerResidueTerm (Differential.pullbackAlong φ ω) (diagonalHom K F' f') w
      = kaehlerResidueTerm ω (diagonalHom K F (traceFunAlong φ f')) v

end AlgebraicCurve

end
