import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.ghglemma1current
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[ghg_covariance_triangle_current_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghglemma1current.lean)
-/
@[path]
private lemma ghg_covariance_triangle_current_delta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : Real)
  (hbeta : 0 <= beta) :
-- imply
  Sharpness.HcovAssembly.hcaFieldDelta G beta h i j * Sharpness.HcovAssembly.hcaFieldDelta G beta h j k <= Sharpness.HcovAssembly.hcaFieldDelta G beta h j j * Sharpness.HcovAssembly.hcaFieldDelta G beta h i k := by
-- proof
  apply StatMech.Walls.ghg_covariance_triangle_current_delta G beta h hbeta i j k

/--
[ghg_covariance_triangle_sourcePairDisconnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghglemma1current.lean)
-/
@[path]
private lemma ghg_covariance_triangle_sourcePairDisconnSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (beta h : Real)
  (hbeta : 0 <= beta) :
-- imply
  Sharpness.FluxEdgeCopy.sourcePairDisconnSum (Sharpness.withGhost G) beta (Sharpness.FieldGhostDict.ghostCoupling h beta (fun _ => 1)) (Sharpness.HcovAssembly.hcaFieldSource i j) ∅ (some i) none * Sharpness.FluxEdgeCopy.sourcePairDisconnSum (Sharpness.withGhost G) beta (Sharpness.FieldGhostDict.ghostCoupling h beta (fun _ => 1)) (Sharpness.HcovAssembly.hcaFieldSource j k) ∅ (some j) none <= Sharpness.FluxEdgeCopy.sourcePairDisconnSum (Sharpness.withGhost G) beta (Sharpness.FieldGhostDict.ghostCoupling h beta (fun _ => 1)) (Sharpness.HcovAssembly.hcaFieldSource j j) ∅ (some j) none * Sharpness.FluxEdgeCopy.sourcePairDisconnSum (Sharpness.withGhost G) beta (Sharpness.FieldGhostDict.ghostCoupling h beta (fun _ => 1)) (Sharpness.HcovAssembly.hcaFieldSource i k) ∅ (some i) none := by
-- proof
  apply StatMech.Walls.ghg_covariance_triangle_sourcePairDisconnSum G beta h hbeta i j k


-- created on 2026-10-23
