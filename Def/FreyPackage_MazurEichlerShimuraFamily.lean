import Mathlib
import Lemma.FLTPrelim.FreyPackage
import Lemma.ModularCurve.HeckeModule
import Abbrev.ModularCurve_AttachmentConcrete
import Def.ModularCurve_HeckeInputsAll

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
