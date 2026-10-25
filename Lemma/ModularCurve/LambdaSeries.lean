import Mathlib
import Lemma.ModularCurve.X0
import Lemma.ModularCurve.KroneckerTransport
import Def.ModularCurve_LambdaSeries

set_option autoImplicit false

noncomputable section

namespace ModularCurve


theorem lambdaNModC_one (L : Type*) [CommRing L] : lambdaNModC L 1 = lambdaModC L :=
  qExpand_one_apply _


theorem evalAtLambdaInt_X : evalAtLambdaInt Polynomial.X = lambdaInt :=
  Polynomial.eval₂_X _ _

end ModularCurve

end
