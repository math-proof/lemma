import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMarkedSiteCorollary
open Finset Filter Set StatMech StatMech.FrontierA


/--
[expJ_zero_three_spin_eq_zero_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMarkedSiteCorollary.lean)
-/
@[path]
private lemma expJ_zero_three_spin_eq_zero_all_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x y z : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  expJ E J (fun _ => 0) (fun s => spin s x * (spin s y * spin s z)) = 0 := by
-- proof
  apply StatMech.FrontierA.expJ_zero_three_spin_eq_zero_all E J x y z

/--
[expJ_pointField_two_eq_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMarkedSiteCorollary.lean)
-/
@[path]
private lemma expJ_pointField_two_eq_all_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x y l : V}
  {t : Real}
-- given
  (J : Sym2 V -> Real) :
-- imply
  expJ E J (lebowitzPointField l t) (fun s => spin s x * spin s y) = expJ E J (fun _ => 0) (fun s => spin s x * spin s y) := by
-- proof
  apply StatMech.FrontierA.expJ_pointField_two_eq_all E J x y l t

/--
[expJ_pointField_three_eq_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMarkedSiteCorollary.lean)
-/
@[path]
private lemma expJ_pointField_three_eq_all_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i j k l : V}
  {t : Real}
-- given
  (J : Sym2 V -> Real) :
-- imply
  expJ E J (lebowitzPointField l t) (fun s => spin s i * (spin s j * spin s k)) = Real.tanh t * expJ E J (fun _ => 0) (fun s => (spin s i * spin s j) * (spin s k * spin s l)) := by
-- proof
  apply StatMech.FrontierA.expJ_pointField_three_eq_all E J i j k l t

/--
[grahamMarkedSite_with_parameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMarkedSiteCorollary.lean)
-/
@[path]
private lemma grahamMarkedSite_with_parameter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
  {q : Real}
-- given
  (K : Sym2 V -> Real)
  (hK : forall e, 0 <= K e)
  (hq0 : 0 < q)
  (hq1 : q < 1) :
-- imply
  grahamUrsell4 G.edgeFinset K i j k l + 2 * q ^ 2 * (grahamTwoPoint G.edgeFinset K i l * grahamTwoPoint G.edgeFinset K j l * grahamTwoPoint G.edgeFinset K k l) <= -2 * (grahamTwoPoint G.edgeFinset K i k - q ^ 2 * grahamTwoPoint G.edgeFinset K i l * grahamTwoPoint G.edgeFinset K k l) * (grahamTwoPoint G.edgeFinset K j k - q ^ 2 * grahamTwoPoint G.edgeFinset K j l * grahamTwoPoint G.edgeFinset K k l) * grahamTwoPoint G.edgeFinset K k l := by
-- proof
  apply StatMech.FrontierA.grahamMarkedSite_with_parameter G K hK i j k l q hq0 hq1

/--
[grahamMarkedSite_four_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMarkedSiteCorollary.lean)
-/
@[path]
private lemma grahamMarkedSite_four_point_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
-- given
  (K : Sym2 V -> Real)
  (hK : forall e, 0 <= K e) :
-- imply
  grahamUrsell4 G.edgeFinset K i j k l <= grahamCorrectedRHS G.edgeFinset K i j k l l := by
-- proof
  apply StatMech.FrontierA.grahamMarkedSite_four_point G K hK i j k l

/--
[grahamMarkedSite_four_point_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMarkedSiteCorollary.lean)
-/
@[path]
private lemma grahamMarkedSite_four_point_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag)
  (hJ : forall e, 0 <= J e) :
-- imply
  grahamUrsell4 E J i j k l <= grahamCorrectedRHS E J i j k l l := by
-- proof
  apply StatMech.FrontierA.grahamMarkedSite_four_point_edgeFinset E J hdiag hJ i j k l


-- created on 2026-10-23
