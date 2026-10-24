import Mathlib
import Lemma.Definitions.Def_FLTPrelim_FreyPackage
import Lemma.Definitions.Def_ModularCurve_HeckeModule
import Lemma.Definitions.Def_ModularCurve_AttachmentConcrete
import Lemma.Definitions.Def_ModularCurve_HeckeInputsAll

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def EichlerShimuraRelationOn (M p : ℕ) [NeZero M] : Prop :=
  HeckeInputsAll M → HeckeOperatorsCommuteBar M →
    letI := heckeModuleBar M
    FrobeniusQuadraticConcrete M p

end ModularCurve

namespace FreyPackage

open ModularCurve

def MazurEichlerShimuraFamily (P : FreyPackage) (q : ℕ) [NeZero q] : Prop :=
  ∀ (N : ℕ) [NeZero N], ¬ q ∣ N → EichlerShimuraRelationOn (N * q) P.p

end FreyPackage

end
