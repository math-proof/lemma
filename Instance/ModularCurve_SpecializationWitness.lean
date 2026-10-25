-- Carved from Lemma/Definitions/Def_ModularCurve_SpecializationWitness.lean: instance decls only.
import Def.HeckeGalois_EichlerShimura
import Lemma.ModularCurve.SpecializationWitness

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section Family

variable (J' : Type*) [AddCommGroup J']

variable {J'}

namespace CommutingHeckeFamily

variable (fam : CommutingHeckeFamily J')

instance commRing_adjoin : CommRing ↥(Algebra.adjoin ℤ (Set.range fam.T)) where
  __ := (inferInstance : Ring ↥(Algebra.adjoin ℤ (Set.range fam.T)))
  mul_comm a b := fam.isMulCommutative_adjoin.is_comm.comm a b

end CommutingHeckeFamily

end Family


end ModularCurve
end
