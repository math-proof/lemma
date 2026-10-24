import Mathlib
import Lemma.Definitions.Def_ModularCurve_X0
import Lemma.Definitions.Def_ModularCurve_KroneckerTransport

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def lambdaInt : LaurentSeries ℤ :=
  HahnSeries.single (1 : ℤ) (1 : ℤ) *
    HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 *
    qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
    qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)

def lambdaModC (L : Type*) [CommRing L] : LaurentSeries L :=
  laurentMap (Int.castRingHom L) lambdaInt

def lambdaNModC (L : Type*) [CommRing L] (N : ℕ) [NeZero N] : LaurentSeries L :=
  qExpand L N (lambdaModC L)

theorem lambdaNModC_one (L : Type*) [CommRing L] : lambdaNModC L 1 = lambdaModC L :=
  qExpand_one_apply _

def evalAtLambdaInt : Polynomial ℤ →+* LaurentSeries ℤ :=
  Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) lambdaInt

theorem evalAtLambdaInt_X : evalAtLambdaInt Polynomial.X = lambdaInt :=
  Polynomial.eval₂_X _ _

end ModularCurve

end
