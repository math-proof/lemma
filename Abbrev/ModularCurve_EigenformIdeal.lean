import Structure.HeckeGalois_EichlerShimura
import Instance.FLTPrelim_Modularity
import Def.ModularCurve_EigenformIdeal

set_option autoImplicit false

noncomputable section

namespace ModularCurve


abbrev EigenformSupportAt (N p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J] : Prop :=
  EigenformSupport p J (IsEigenformIdeal N)

abbrev EichlerShimuraDataAt {K L : Type*} [Field K] [Field L] [Algebra K L] (N p : ℕ)
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction (L ≃ₐ[K] L) J] :
    Prop :=
  EichlerShimuraDataReduced (K := K) (L := L) N p J (IsEigenformIdeal N)

end ModularCurve
