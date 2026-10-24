import Mathlib
import Lemma.Definitions.Def_ModularCurve_X0
import Lemma.Definitions.Def_ModularCurve_IgusaScheme
import Lemma.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option autoImplicit false

noncomputable section

namespace ModularCurve

namespace HpoolLevelRing

variable (p : ℕ) [Fact p.Prime]

theorem neZero_of_fact_prime : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

attribute [local instance] neZero_of_fact_prime

abbrev Afin : Type :=
  ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))

set_option synthInstance.maxHeartbeats 200000 in
instance instCommRingAfin : CommRing (Afin p) := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
instance instIsDomainAfin : IsDomain (Afin p) := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
instance instAlgebraIntAfin : Algebra ℤ (Afin p) := inferInstance

set_option synthInstance.maxHeartbeats 200000 in
instance instModuleAfinSelf : Module (Afin p) (Afin p) := Semiring.toModule

abbrev AfinAway (f : ℤ) : Type :=
  Localization.Away (algebraMap ℤ (Afin p) f)

set_option synthInstance.maxHeartbeats 200000 in
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

theorem algebraMap_awayMap_algebraMap (f : ℤ) (x : ℤ) :
    algebraMap (Localization.Away f) (AfinAway p f) (algebraMap ℤ (Localization.Away f) x) =
      algebraMap ℤ (AfinAway p f) x :=
  RingHom.congr_fun (Subsingleton.elim ((algebraMap (Localization.Away f) (AfinAway p f)).comp
    (algebraMap ℤ (Localization.Away f))) (algebraMap ℤ (AfinAway p f))) x

abbrev levelRing (f : ℤ) (u : Afin p) (g : Polynomial ℤ) : Type :=
  AfinAway p f ⧸ Ideal.span {Polynomial.aeval (algebraMap (Afin p) (AfinAway p f) u) g}

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
