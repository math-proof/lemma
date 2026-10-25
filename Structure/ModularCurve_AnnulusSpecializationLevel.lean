import Mathlib
import Def.ModularCurve_GlueData
import Lemma.AlgebraicCurve.GluedPic0
import Def.ModularCurve_NodeDepth
import Structure.ModularCurve_NodeLocalizedPlaces
import Structure.ModularCurve_ProlongationTuple
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

namespace ProlongationTuple

variable {P} (R : ProlongationTuple P)

structure AnnulusDatumLevel (W : Finset (Place k (modularFunctionFieldC k N))) where
  K : Place k (modularFunctionFieldC k N) → IntermediateField ℚ (AlgebraicClosure ℚ)
  coord : ∀ w : Place k (modularFunctionFieldC k N), w ∈ W → R.NodeCoordinates (K w) w
  width : Place k (modularFunctionFieldC k N) → ℕ

  depthQ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℚ

  unifFst : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N)
  unifSnd : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N)

  corrFst : Place k (modularFunctionFieldC k N) → Divisor k ↥(modularFunctionFieldC k N)
  corrSnd : Place k (modularFunctionFieldC k N) → Divisor k ↥(modularFunctionFieldC k N)

  u0 : Place k (modularFunctionFieldC k N) → kˣ
  lam : Place k (modularFunctionFieldC k N) → kˣ
  mu : Place k (modularFunctionFieldC k N) → kˣ

structure TwistVectorLevel (W : Finset (Place k (modularFunctionFieldC k N))) where
  aZ : ℤ
  aZ' : ℤ
  aE : Place k (modularFunctionFieldC k N) → ℕ → ℤ

variable {R}
variable {W : Finset (Place k (modularFunctionFieldC k N))} (dat : R.AnnulusDatumLevel W)

namespace AnnulusDatumLevel

open Classical in


open Classical in


open Classical in


open Classical in

open Classical in


open Classical in


open Classical in


open Classical in


open Classical in


open Classical in

end AnnulusDatumLevel

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end
