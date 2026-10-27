import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFormalMultiaffine
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[kwGraph_formalRoot_coeff_eq_zero_of_repeated_of_scaleEdge_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFormalMultiaffine.lean)
-/
@[path]
private lemma kwGraph_formalRoot_coeff_eq_zero_of_repeated_of_scaleEdge_affine_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → ℂ}
  {selected : G.Dart}
  {m : Sym2 V →₀ ℕ}
-- given
  (hrepeated : 2 ≤ m selected.edge)
  (haffine : ∀ (weight : Sym2 V → ℂ) (t : ℂ) (q : ℝ), 0 ≤ q → (∀ dart next, ‖ons_scaleColumns ({selected, selected.symm} : Finset G.Dart) t (kwGraphTransition G weight phase) dart next‖ ≤ q) → q < (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹ → (Fintype.card G.Dart : ℝ) * q < 1 → ons_detWalkRoot (kwGraphTransition G (kwScaleGraphEdgeWeight weight selected.edge t) phase) = ons_detWalkRoot (ons_maskMatrix ({selected, selected.symm} : Finset G.Dart) (kwGraphTransition G weight phase)) * (1 - t * ∑' path, ons_firstReturnWeight (kwGraphTransition G weight phase) selected selected.symm path)) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0 := by
-- proof
  apply StatMech.FrontierA.kwGraph_formalRoot_coeff_eq_zero_of_repeated_of_scaleEdge_affine G phase selected m hrepeated haffine

/--
[kw_straightLineGraph_formalRoot_coeff_eq_zero_of_repeated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFormalMultiaffine.lean)
-/
@[path]
private lemma kw_straightLineGraph_formalRoot_coeff_eq_zero_of_repeated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {selected : G.Dart}
  {m : Sym2 V →₀ ℕ}
-- given
  (hrepeated : 2 ≤ m selected.edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot G embedding.turnPhase) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_straightLineGraph_formalRoot_coeff_eq_zero_of_repeated G embedding selected m hrepeated

/--
[kw_straightLineGraph_formalRoot_coeff_eq_zero_of_repeated_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFormalMultiaffine.lean)
-/
@[path]
private lemma kw_straightLineGraph_formalRoot_coeff_eq_zero_of_repeated_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {edge : Sym2 V}
  {m : Sym2 V →₀ ℕ}
-- given
  (hedge : edge ∈ G.edgeFinset)
  (hrepeated : 2 ≤ m edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot G embedding.turnPhase) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_straightLineGraph_formalRoot_coeff_eq_zero_of_repeated_edge G embedding edge hedge m hrepeated


-- created on 2026-10-23
