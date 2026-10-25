import Mathlib
import Lemma.ModularCurve.X0
import Abbrev.ModularCurve_IgusaScheme
import Lemma.AlgebraicCurve.TwoChartIntegralModel
import Abbrev.ModularCurve_HpoolLevelRing

set_option autoImplicit false

noncomputable section

namespace ModularCurve

namespace HpoolLevelRing

variable (p : ℕ) [Fact p.Prime]

theorem neZero_of_fact_prime : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

attribute [local instance] neZero_of_fact_prime


theorem algebraMap_awayMap_algebraMap (f : ℤ) (x : ℤ) :
    algebraMap (Localization.Away f) (AfinAway p f) (algebraMap ℤ (Localization.Away f) x) =
      algebraMap ℤ (AfinAway p f) x :=
  RingHom.congr_fun (Subsingleton.elim ((algebraMap (Localization.Away f) (AfinAway p f)).comp
    (algebraMap ℤ (Localization.Away f))) (algebraMap ℤ (AfinAway p f))) x

end HpoolLevelRing

end ModularCurve

end
