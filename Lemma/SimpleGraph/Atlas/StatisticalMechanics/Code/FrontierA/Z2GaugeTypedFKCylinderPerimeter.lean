import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderPerimeter
open StatMech StatMech.FrontierA


/--
[cubicalXYWilson_central_perimeterLower_of_l1_exponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderPerimeter.lean)
-/
@[path]
private lemma cubicalXYWilson_central_perimeterLower_of_l1_exponential_eq
  {n : Nat}
  {decay : Real}
-- given
  (K : CubicalPlaquette (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n) -> Real)
  (hK : forall p, 0 < K p)
  (hdecay : 0 < decay)
  (hcorr : forall uv, uv ∈ (cubicalLowerComplementInnerVertices (centralSquareSheetHeight n)).product (cubicalXYSheetUpperVertices (centralSquareSheetHeight n)) -> multibondIsingTwoPoint cubicalDualEnds (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <= Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) :
-- imply
  Real.exp (-(gaugePerimeterPenalty (Real.exp (-decay)) * (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) * centralSquareSide n) <= gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop (centralSquareSheetHeight n)) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilson_central_perimeterLower_of_l1_exponential n K hK decay hdecay hcorr


-- created on 2026-10-23
