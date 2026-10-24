import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.Duality
open StatMech StatMech.BeffaraDC


/--
[dlt_edgeProduct_eq_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Duality.lean)
-/
@[path]
private lemma dlt_edgeProduct_eq_count_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  StatMech.FK.edgeProduct G p ω = edgeProductCount p G.edgeFinset.card (StatMech.FK.openCount G ω) := by
-- proof
  apply StatMech.BeffaraDC.dlt_edgeProduct_eq_count G p ω

/--
[dlt_edgeProductCount_yates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Duality.lean)
-/
@[path]
private lemma dlt_edgeProductCount_yates_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {m o : ℕ}
-- given
  (hp1 : p < 1)
  (hom : o ≤ m) :
-- imply
  edgeProductCount p m o = (1 - p) ^ m * (p / (1 - p)) ^ o := by
-- proof
  apply StatMech.BeffaraDC.dlt_edgeProductCount_yates G hp1 m o hom

/--
[dlt_dual_ratio_rel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Duality.lean)
-/
@[path]
private lemma dlt_dual_ratio_rel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (p / (1 - p)) * (dualParam p q / (1 - dualParam p q)) = q := by
-- proof
  apply StatMech.BeffaraDC.dlt_dual_ratio_rel G hp hp1 hq

/--
[dlt_edgeProduct_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Duality.lean)
-/
@[path]
private lemma dlt_edgeProduct_duality_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {m o : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hom : o ≤ m) :
-- imply
  edgeProductCount p m o * q ^ m = (p / (1 - dualParam p q)) ^ m * q ^ o * edgeProductCount (dualParam p q) m (m - o) := by
-- proof
  apply StatMech.BeffaraDC.dlt_edgeProduct_duality G hp hp1 hq m o hom

/--
[dlt_edgeProduct_duality_selfdual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Duality.lean)
-/
@[path]
private lemma dlt_edgeProduct_duality_selfdual_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {m o : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hsd : dualParam p q = p)
  (hom : o ≤ m) :
-- imply
  edgeProductCount p m o * q ^ m = (p / (1 - p)) ^ m * q ^ o * edgeProductCount p m (m - o) := by
-- proof
  apply StatMech.BeffaraDC.dlt_edgeProduct_duality_selfdual G hp hp1 hq hsd m o hom

/--
[dlt_rn_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Duality.lean)
-/
@[path]
private lemma dlt_rn_sandwich_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype Ω]
  [Nonempty Ω]
  {w w' : Ω → ℝ}
  {q : ℝ}
  {c : ℕ}
  {A : Finset Ω}
-- given
  (hq : 1 ≤ q)
  (hw'pos : ∀ ω, 0 < w' ω)
  (hwpos : ∀ ω, 0 < w ω)
  (hlb : ∀ ω, q ^ (-(c : ℤ)) * w' ω ≤ w ω)
  (hub : ∀ ω, w ω ≤ q ^ (c : ℤ) * w' ω) :
-- imply
  (∑ ω ∈ A, w ω) / (∑ ω, w ω) ≤ q ^ (2 * c) * ((∑ ω ∈ A, w' ω) / (∑ ω, w' ω)) := by
-- proof
  apply StatMech.BeffaraDC.dlt_rn_sandwich G w w' q hq c hw'pos hwpos hlb hub A

/--
[dlt_dichotomy_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Duality.lean)
-/
@[path]
private lemma dlt_dichotomy_lower_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype Ω]
  [Nonempty Ω]
  {x y Q : ℝ}
-- given
  (hsum : x + y = 1)
  (hQ : 0 ≤ Q)
  (hyx : y ≤ Q * x) :
-- imply
  1 / (1 + Q) ≤ x := by
-- proof
  apply StatMech.BeffaraDC.dlt_dichotomy_lower_bound G hsum hQ hyx

/--
[dlt_self_duality_estimate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Duality.lean)
-/
@[path]
private lemma dlt_self_duality_estimate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype Ω]
  [Nonempty Ω]
  {connectProb dualConnectProb q : ℝ}
-- given
  (hdichotomy : connectProb + dualConnectProb = 1)
  (hRN : dualConnectProb ≤ q ^ 2 * connectProb) :
-- imply
  1 / (1 + q ^ 2) ≤ connectProb := by
-- proof
  apply StatMech.BeffaraDC.dlt_self_duality_estimate G hdichotomy hRN

/--
[dlt_square_crossing_estimate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Duality.lean)
-/
@[path]
private lemma dlt_square_crossing_estimate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype Ω]
  [Nonempty Ω]
  {horizCross vertDualCross c : ℝ}
-- given
  (hc : 0 ≤ c)
  (hdichotomy : horizCross + vertDualCross = 1)
  (hsym : vertDualCross ≤ c * horizCross) :
-- imply
  1 / (1 + c) ≤ horizCross := by
-- proof
  apply StatMech.BeffaraDC.dlt_square_crossing_estimate G hc hdichotomy hsym

/--
[dlt_square_crossing_const_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Duality.lean)
-/
@[path]
private lemma dlt_square_crossing_const_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype Ω]
  [Nonempty Ω]
  {c : ℝ}
-- given
  (hc : 0 ≤ c) :
-- imply
  0 < 1 / (1 + c) := by
-- proof
  apply StatMech.BeffaraDC.dlt_square_crossing_const_pos G hc

/--
[dlt_self_duality_const_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Duality.lean)
-/
@[path]
private lemma dlt_self_duality_const_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype Ω]
  [Nonempty Ω]
  {q : ℝ} :
-- imply
  0 < 1 / (1 + q ^ 2) := by
-- proof
  apply StatMech.BeffaraDC.dlt_self_duality_const_pos G q


-- created on 2026-10-23
