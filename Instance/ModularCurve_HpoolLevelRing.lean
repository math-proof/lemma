-- Carved from Lemma/Definitions/Def_ModularCurve_HpoolLevelRing.lean: instance decls only.
import Mathlib

set_option autoImplicit false

noncomputable section

namespace ModularCurve

namespace HpoolLevelRing

variable (p : ℕ) [Fact p.Prime]


instance instCommRingAfin : CommRing (Afin p) := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
instance instIsDomainAfin : IsDomain (Afin p) := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
instance instAlgebraIntAfin : Algebra ℤ (Afin p) := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
instance instModuleAfinSelf : Module (Afin p) (Afin p) := Semiring.toModule

instance instCommRingAfinAway (f : ℤ) : CommRing (AfinAway p f) := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
instance instAlgebraAfinAfinAway (f : ℤ) : Algebra (Afin p) (AfinAway p f) := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
instance instAlgebraIntAfinAway (f : ℤ) : Algebra ℤ (AfinAway p f) := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
instance instSMulAfinAfinAway (f : ℤ) : SMul (Afin p) (AfinAway p f) := Algebra.toSMul

set_option synthInstance.maxHeartbeats 200000 in
instance instModuleAfinAfinAway (f : ℤ) : Module (Afin p) (AfinAway p f) := Algebra.toModule

set_option synthInstance.maxHeartbeats 200000 in

instance algebraAway (f : ℤ) : Algebra (Localization.Away f) (AfinAway p f) :=
  (Localization.awayMap (algebraMap ℤ (Afin p)) f).toAlgebra

set_option synthInstance.maxHeartbeats 200000 in
instance instSMulAway (f : ℤ) : SMul (Localization.Away f) (AfinAway p f) := Algebra.toSMul

set_option synthInstance.maxHeartbeats 200000 in
instance instModuleAway (f : ℤ) : Module (Localization.Away f) (AfinAway p f) := Algebra.toModule

set_option synthInstance.maxHeartbeats 200000 in


instance instCommRingLevelRing (f : ℤ) (u : Afin p) (g : Polynomial ℤ) : CommRing (levelRing p f u g) := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
instance instAlgebraLevelRing (f : ℤ) (u : Afin p) (g : Polynomial ℤ) :
    Algebra (Localization.Away f) (levelRing p f u g) := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
instance instSMulLevelRing (f : ℤ) (u : Afin p) (g : Polynomial ℤ) :
    SMul (Localization.Away f) (levelRing p f u g) := Algebra.toSMul

set_option synthInstance.maxHeartbeats 200000 in
instance instModuleLevelRing (f : ℤ) (u : Afin p) (g : Polynomial ℤ) :
    Module (Localization.Away f) (levelRing p f u g) := Algebra.toModule

set_option synthInstance.maxHeartbeats 200000 in
instance instAlgebraAfinAwayLevelRing (f : ℤ) (u : Afin p) (g : Polynomial ℤ) :
    Algebra (AfinAway p f) (levelRing p f u g) := inferInstance

end HpoolLevelRing

end ModularCurve

end
