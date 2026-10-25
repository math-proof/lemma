import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.OrderContour.Part2
open Finset Set SimpleGraph Filter Topology StatMech StatMech.FK


/--
[peierlsContourWeight_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma peierlsContourWeight_zero_eq
  {q : ℝ} :
-- imply
  peierlsContourWeight q 0 = 1 := by
-- proof
  apply StatMech.FK.peierlsContourWeight_zero q

/--
[peierlsContourWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma peierlsContourWeight_nonneg_eq
  {q : ℝ}
  {n : ℕ}
-- given
  (hq : 0 < q) :
-- imply
  0 ≤ peierlsContourWeight q n := by
-- proof
  apply StatMech.FK.peierlsContourWeight_nonneg hq n

/--
[card_dualCircuits_qSuppressed_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma card_dualCircuits_qSuppressed_le_eq
  {q : ℝ}
  {n : ℕ}
  {v : Site 2}
-- given
  (hq : 0 < q) :
-- imply
  ((dualLattice.finsetWalkLength n v v).card : ℝ) / q ^ n ≤ peierlsContourWeight q n := by
-- proof
  apply StatMech.FK.card_dualCircuits_qSuppressed_le hq n v

/--
[peierlsContourRatio_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma peierlsContourRatio_lt_one_eq
  {q : ℝ}
-- given
  (hq : 4 < q) :
-- imply
  (4 : ℝ) / q < 1 := by
-- proof
  apply StatMech.FK.peierlsContourRatio_lt_one hq

/--
[peierlsContourRatio_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma peierlsContourRatio_nonneg_eq
  {q : ℝ}
-- given
  (hq : 4 < q) :
-- imply
  (0 : ℝ) ≤ 4 / q := by
-- proof
  apply StatMech.FK.peierlsContourRatio_nonneg hq

/--
[peierls_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma peierls_summable_eq
  {q : ℝ}
-- given
  (hq : 4 < q) :
-- imply
  Summable (peierlsContourWeight q) := by
-- proof
  apply StatMech.FK.peierls_summable hq

/--
[peierls_tsum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma peierls_tsum_eq_eq
  {q : ℝ}
-- given
  (hq : 4 < q) :
-- imply
  ∑' n, peierlsContourWeight q n = q / (q - 4) := by
-- proof
  apply StatMech.FK.peierls_tsum_eq hq

/--
[peierlsTail_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma peierlsTail_eq_eq
  {q : ℝ}
  {N : ℕ}
-- given
  (hq : 4 < q) :
-- imply
  peierlsTail q N = (4 / q) ^ N * (q / (q - 4)) := by
-- proof
  apply StatMech.FK.peierlsTail_eq hq N

/--
[peierlsTail_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma peierlsTail_nonneg_eq
  {q : ℝ}
  {N : ℕ}
-- given
  (hq : 4 < q) :
-- imply
  0 ≤ peierlsTail q N := by
-- proof
  apply StatMech.FK.peierlsTail_nonneg hq N

/--
[peierlsTail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma peierlsTail_le_eq
  {q : ℝ}
  {N : ℕ}
-- given
  (hq : 8 ≤ q) :
-- imply
  peierlsTail q N ≤ 2 * (4 / q) ^ N := by
-- proof
  apply StatMech.FK.peierlsTail_le hq N

/--
[peierlsTail_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma peierlsTail_tendsto_zero_eq
  {N : ℕ}
-- given
  (hN : 1 ≤ N) :
-- imply
  Tendsto (fun q => peierlsTail q N) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.peierlsTail_tendsto_zero hN

/--
[dualCircuit_support_near](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma dualCircuit_support_near_eq
  {n : ℕ}
  {v : Site 2}
  {w : dualLattice.Walk v v}
-- given
  (hw : w.length = n) :
-- imply
  ∀ z ∈ w.support, l1dist 2 v z ≤ n := by
-- proof
  apply StatMech.FK.dualCircuit_support_near n v w hw

/--
[card_dualCircuits_based_in_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma card_dualCircuits_based_in_le_eq
  {B : Finset (Site 2)}
  {n : ℕ} :
-- imply
  (B.sigma (fun v => dualLattice.finsetWalkLength n v v)).card ≤ B.card * 4 ^ n := by
-- proof
  apply StatMech.FK.card_dualCircuits_based_in_le B n

/--
[card_dualCircuits_based_qSuppressed_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma card_dualCircuits_based_qSuppressed_le_eq
  {q : ℝ}
  {B : Finset (Site 2)}
  {n : ℕ}
-- given
  (hq : 0 < q) :
-- imply
  ((B.sigma (fun v => dualLattice.finsetWalkLength n v v)).card : ℝ) / q ^ n ≤ (B.card : ℝ) * peierlsContourWeight q n := by
-- proof
  apply StatMech.FK.card_dualCircuits_based_qSuppressed_le hq B n

/--
[finite_cluster_yields_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma finite_cluster_yields_dualCircuit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {z : Site 2}
  {w : (hypercubicLattice 2).Walk o z}
-- given
  (hfin : (cluster 2 ω o).Finite)
  (hz : z ∉ cluster 2 ω o) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.FK.finite_cluster_yields_dualCircuit o hfin w hz

/--
[escape_crosses_dualContour_oddly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma escape_crosses_dualContour_oddly_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {z : Site 2}
  {γ : (hypercubicLattice 2).Walk o z}
-- given
  (hz : z ∉ cluster 2 ω o) :
-- imply
  ¬ Even (crossCount (cluster 2 ω o) γ) := by
-- proof
  apply StatMech.FK.escape_crosses_dualContour_oddly o hz γ

/--
[qLarge_contour_estimate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean)
-/
@[path]
private lemma qLarge_contour_estimate_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {q : ℝ}
-- given
  (hq : 4 < q) :
-- imply
  Summable (peierlsContourWeight q) ∧ ∑' n, peierlsContourWeight q n = q / (q - 4) ∧ (∀ {q' : ℝ}, 8 ≤ q' → ∀ N : ℕ, peierlsTail q' N ≤ 2 * (4 / q') ^ N) := by
-- proof
  apply StatMech.FK.qLarge_contour_estimate hq


-- created on 2026-10-23
