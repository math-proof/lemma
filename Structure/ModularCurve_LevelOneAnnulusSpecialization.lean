import Def.ModularCurve_LevelOneGlueData
import Lemma.AlgebraicCurve.GluedPic0
import Def.ModularCurve_NodeDepth
import Structure.ModularCurve_NodeLocalizedPlaces
import Structure.ModularCurve_ProlongationTuple
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

namespace ProlongationTuple

variable {P} (R : ProlongationTuple P)

structure AnnulusDatum (W : Finset (Place k (modularFunctionFieldC k 1))) where
  K : Place k (modularFunctionFieldC k 1) → IntermediateField ℚ (AlgebraicClosure ℚ)
  coord : ∀ w : Place k (modularFunctionFieldC k 1), w ∈ W → R.NodeCoordinates (K w) w
  width : Place k (modularFunctionFieldC k 1) → ℕ
  depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℕ

  cusp : Place k (modularFunctionFieldC k 1)

  unifFst : Place k (modularFunctionFieldC k 1) → ↥(modularFunctionFieldC k 1)
  unifSnd : Place k (modularFunctionFieldC k 1) → ↥(modularFunctionFieldC k 1)

  u0 : Place k (modularFunctionFieldC k 1) → kˣ
  lam : Place k (modularFunctionFieldC k 1) → kˣ
  mu : Place k (modularFunctionFieldC k 1) → kˣ

structure TwistVector (W : Finset (Place k (modularFunctionFieldC k 1))) where
  aZ : ℤ
  aZ' : ℤ
  aE : Place k (modularFunctionFieldC k 1) → ℕ → ℤ

variable {R}
variable {W : Finset (Place k (modularFunctionFieldC k 1))} (dat : R.AnnulusDatum W)

namespace AnnulusDatum


open Classical in

open Classical in


open Classical in


open Classical in

open Classical in


open Classical in


open Classical in


open Classical in

end AnnulusDatum

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end
