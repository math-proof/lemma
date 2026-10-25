import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABCouplingReindex.Part2
open Finset SimpleGraph StatMech StatMech.Sharpness


/--
[abcrEndpointSum_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABCouplingReindex.lean)
-/
@[path]
private lemma abcrEndpointSum_mk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F : V → ℝ}
  {x y : V} :
-- imply
  abcrEndpointSum F s(x, y) = F x + F y := by
-- proof
  apply StatMech.Sharpness.abcrEndpointSum_mk G F x y

/--
[abcr_edgeSum_eq_dartSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABCouplingReindex.lean)
-/
@[path]
private lemma abcr_edgeSum_eq_dartSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {F : V → ℝ} :
-- imply
  ∑ e ∈ G.edgeFinset, J e * abcrEndpointSum F e = ∑ d : G.Dart, J d.edge * F d.fst := by
-- proof
  apply StatMech.Sharpness.abcr_edgeSum_eq_dartSum G J F

/--
[abcr_dartSum_eq_vertexSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABCouplingReindex.lean)
-/
@[path]
private lemma abcr_dartSum_eq_vertexSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {F : V → ℝ} :
-- imply
  ∑ d : G.Dart, J d.edge * F d.fst = ∑ x : V, F x * abcrIncidentCoupling G J x := by
-- proof
  apply StatMech.Sharpness.abcr_dartSum_eq_vertexSum G J F

/--
[abcr_edgeSum_eq_rowSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABCouplingReindex.lean)
-/
@[path]
private lemma abcr_edgeSum_eq_rowSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {F : V → ℝ}
  {J0 : ℝ}
-- given
  (hrow : ∀ x, abcrIncidentCoupling G J x = J0) :
-- imply
  ∑ e ∈ G.edgeFinset, J e * abcrEndpointSum F e = J0 * ∑ x : V, F x := by
-- proof
  apply StatMech.Sharpness.abcr_edgeSum_eq_rowSum G J F J0 hrow

/--
[abcr_edgeSum_le_rowSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABCouplingReindex.lean)
-/
@[path]
private lemma abcr_edgeSum_le_rowSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {F : V → ℝ}
  {J0 : ℝ}
-- given
  (hF : ∀ x, 0 ≤ F x)
  (hrow : ∀ x, abcrIncidentCoupling G J x ≤ J0) :
-- imply
  ∑ e ∈ G.edgeFinset, J e * abcrEndpointSum F e ≤ J0 * ∑ x : V, F x := by
-- proof
  apply StatMech.Sharpness.abcr_edgeSum_le_rowSum G J F J0 hF hrow


-- created on 2026-10-23
