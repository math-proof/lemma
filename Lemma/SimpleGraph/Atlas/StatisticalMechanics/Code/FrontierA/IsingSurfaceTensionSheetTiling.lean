import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetTiling.Part3
open Finset StatMech StatMech.FrontierA


/--
[gaugeWilsonExpectation_prod_boundary_le_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetTiling.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_prod_boundary_le_biUnion_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype P]
  [DecidableEq P]
  [DecidableEq I]
  {S : Finset I}
-- given
  (incidence : P -> Finset E)
  (K : P -> Real)
  (hK : forall p, 0 < K p)
  (D : I -> Finset P)
  (hdisj : forall i, i ∈ S -> forall j, j ∈ S -> i ≠ j -> Disjoint (D i) (D j)) :
-- imply
  (∏ i ∈ S, gaugeWilsonExpectation incidence K (gaugeSurfaceBoundary incidence (D i))) <= gaugeWilsonExpectation incidence K (gaugeSurfaceBoundary incidence (S.biUnion D)) := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_prod_boundary_le_biUnion incidence K hK S D hdisj

/--
[oddCubicalWilson_nineTile_le_central](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetTiling.lean)
-/
@[path]
private lemma oddCubicalWilson_nineTile_le_central_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  (gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ : CubicalPlaquette (tripleTileSide n) (tripleTileSide n) (tripleTileSide n) => beta) (cubicalXYLoop (a := tripleTileSide n) (b := tripleTileSide n) (c := tripleTileSide n) (0 : Fin (tripleTileSide n + 1)))) ^ 9 <= gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ : CubicalPlaquette (tripleTiledSide n) (tripleTiledSide n) (tripleTiledSide n) => beta) (cubicalXYLoop (a := tripleTiledSide n) (b := tripleTiledSide n) (c := tripleTiledSide n) (tripleCentralHeightFin n)) := by
-- proof
  apply StatMech.FrontierA.oddCubicalWilson_nineTile_le_central hbeta n

/--
[oddCubicalCentralSheetFreeEnergy_triple_le_nine_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetTiling.lean)
-/
@[path]
private lemma oddCubicalCentralSheetFreeEnergy_triple_le_nine_lower_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  oddCubicalCentralSheetFreeEnergy beta (3 * n + 1) <= 9 * oddCubicalLowerSheetFreeEnergy beta n := by
-- proof
  apply StatMech.FrontierA.oddCubicalCentralSheetFreeEnergy_triple_le_nine_lower hbeta n

/--
[centralCubicalIsingDisorderDensity_triple_le_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetTiling.lean)
-/
@[path]
private lemma centralCubicalIsingDisorderDensity_triple_le_odd_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  centralCubicalIsingDisorderDensity beta (3 * n + 1) <= oddCubicalIsingDisorderDensity beta n := by
-- proof
  apply StatMech.FrontierA.centralCubicalIsingDisorderDensity_triple_le_odd hbeta n

/--
[rectangularIsingSurfaceTension_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetTiling.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_pos_eq
  {beta : Real}
-- given
  (hcritical : StatMech.Ising.betaC 3 < beta) :
-- imply
  0 < rectangularIsingSurfaceTension beta := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_pos hcritical


-- created on 2026-10-23
