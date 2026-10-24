import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.HexagonalSharpnessOffCentre
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[hexagonalBox_reachOpen_hits_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalBox_reachOpen_hits_centered_eq
  {n m : Nat}
  {omega : ConfigSpace (hexagonalBoxGraph n).edgeSet}
  {x b : HexagonalBoxVertex n}
-- given
  (hreach : ReachOpen (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega x b)
  (hm : m ≤ centeredRadius x.1.1 b.1.1) :
-- imply
  ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega x (hexagonalBoxCenteredShell n x m) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBox_reachOpen_hits_centered hreach hm

/--
[hexagonalBox_rootShell_imp_centered_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalBox_rootShell_imp_centered_of_le_eq
  {n k m : Nat}
  {omega : ConfigSpace (hexagonalBoxGraph n).edgeSet}
  {x : HexagonalBoxVertex n}
-- given
  (hm : m ≤ ((k : Int) - (siteRadius x.1.1 : Int)).natAbs) :
-- imply
  ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega x (hexagonalBoxShell n k) → ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega x (hexagonalBoxCenteredShell n x m) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBox_rootShell_imp_centered_of_le hm

/--
[hexagonal_rootShell_sum_le_centered_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonal_rootShell_sum_le_centered_sup_eq
  {n : Nat}
  {mu : ConfigSpace (hexagonalBoxGraph (2 * n)).edgeSet → Real}
  {u : HexagonalBoxVertex n}
-- given
  (hmu0 : ∀ omega, 0 ≤ mu omega) :
-- imply
  (∑ k : ↑(Finset.Icc 1 n), Lindeberg.mean mu (fun omega => if ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega) u (hexagonalBoxShell n k) then (1 : Real) else 0)) ≤ 2 * (Finset.univ : Finset (HexagonalBoxVertex n)).sup' ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩ (fun x => ∑ j ∈ Finset.range n, Lindeberg.mean mu (fun omega => if ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega) x (hexagonalBoxCenteredShell n x j) then (1 : Real) else 0)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_rootShell_sum_le_centered_sup n mu hmu0 u

/--
[hexagonalOuterCenteredConn_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalOuterCenteredConn_nonneg_eq
  {n : Nat}
  {q beta : Real}
  {x : HexagonalBoxVertex n}
  {j : Nat}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  0 ≤ hexagonalOuterCenteredConn n q beta x j := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterCenteredConn_nonneg n q beta hq hbeta x j

/--
[hexagonalOuterCenteredConn_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalOuterCenteredConn_zero_eq
  {n : Nat}
  {q beta : Real}
  {x : HexagonalBoxVertex n}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  hexagonalOuterCenteredConn n q beta x 0 = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterCenteredConn_zero n q beta hq hbeta x

/--
[hexagonalOuterCenteredConn_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalOuterCenteredConn_le_one_eq
  {n : Nat}
  {q beta : Real}
  {x : HexagonalBoxVertex n}
  {j : Nat}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  hexagonalOuterCenteredConn n q beta x j ≤ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterCenteredConn_le_one n q beta hq hbeta x j

/--
[hexagonalOuterCenteredConn_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalOuterCenteredConn_antitone_eq
  {n : Nat}
  {q beta : Real}
  {x : HexagonalBoxVertex n}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  Antitone (hexagonalOuterCenteredConn n q beta x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterCenteredConn_antitone n q beta hq hbeta x

/--
[hexagonalOuterInnerTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalOuterInnerTheta_nonneg_eq
  {q beta : Real}
  {k : Nat}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  0 ≤ hexagonalOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterInnerTheta_nonneg q beta hq hbeta k

/--
[hexagonalOuterInnerTheta_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalOuterInnerTheta_zero_eq
  {q beta : Real} :
-- imply
  hexagonalOuterInnerTheta q beta 0 = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterInnerTheta_zero q beta

/--
[hexagonalCenteredShellEvent_iff_innerCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalCenteredShellEvent_iff_innerCross_eq
  {k : Nat}
  {omega : ConfigSpace (hexagonalBoxGraph (2 * k)).edgeSet}
-- given
  (hk : 1 ≤ k) :
-- imply
  omega ∈ hexagonalCenteredShellEvent (2 * k) k ↔ restrictConfig (hexagonalBoxEdgeLE (by omega : k ≤ 2 * k)) omega ∈ openCrossEvent (hexagonalBoxEndU k) (hexagonalBoxEndV k) (hexagonalBoxRoot k) (hexagonalBoxShell k k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalCenteredShellEvent_iff_innerCross k hk omega

/--
[hexagonalCenteredFullMass_eq_outerInnerTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalCenteredFullMass_eq_outerInnerTheta_eq
  {k : Nat}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  (∑ omega : ConfigSpace (Sym2 (HexagonalBoxVertex (2 * k))), (hexagonalCenteredShellFullEvent (2 * k) k).indicator (fun _ => (1 : Real)) omega * FK.wiredFkProb (hexagonalBoxGraph (2 * k)) (fun y => y ∈ hexagonalBoxShell (2 * k) (2 * k)) (1 - Real.exp (-beta)) q omega) = hexagonalOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalCenteredFullMass_eq_outerInnerTheta k hk q beta hq hbeta

/--
[hexagonal_centeredConn_imp_transShell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonal_centeredConn_imp_transShell_eq
  {n k : Nat}
  {x : HexagonalBoxVertex n}
  {rho : ConfigSpace (hexagonalBoxGraph (2 * n)).edgeSet}
-- given
  (hk : 1 ≤ k)
  (hkn : 2 * k < n)
  (hconn : ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) rho) x (hexagonalBoxCenteredShell n x k)) :
-- imply
  let hsub := hexagonalTransBox_subset_double x.2.1 hkn let transIncl := hexagonalTransBoxIncl hsub let hadjm := ocd_comapAdjMatch hexagonalGraph transIncl (fun _ => rfl) ocd_innerRestrictActive (hexagonalTransBoxGraph (2 * k) x.1.1) (hexagonalBoxGraph (2 * n)) transIncl hadjm rho ∈ hexagonalTransShellEvent (2 * k) k x.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_centeredConn_imp_transShell x hk hkn rho hconn

/--
[hexagonalOuterCenteredConn_le_theta_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalOuterCenteredConn_le_theta_strict_eq
  {n k : Nat}
  {x : HexagonalBoxVertex n}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hkn : 2 * k < n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  hexagonalOuterCenteredConn n q beta x k ≤ hexagonalOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterCenteredConn_le_theta_strict n k x hk hkn q beta hq hbeta

/--
[hexagonalCenteredDenom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalCenteredDenom_pos_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  0 < hexagonalCenteredDenom n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalCenteredDenom_pos n hn q beta hq hbeta

/--
[hexagonal_outer_inner_hcov_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonal_outer_inner_hcov_centered_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n)) (hexagonalBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q Lindeberg.mean mu (hexagonalInnerCrossInd n) * (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) / hexagonalCenteredDenom n q beta ≤ ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_outer_inner_hcov_centered n hn q beta hq hbeta

/--
[hexagonal_centered_sup_le_two_sig_of_strict_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonal_centered_sup_le_two_sig_of_strict_comparison_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hcomp : ∀ x : HexagonalBoxVertex n, ∀ k, k ∈ Finset.Icc 1 (n / 2) → 2 * k < n → hexagonalOuterCenteredConn n q beta x k ≤ hexagonalOuterInnerTheta q beta k) :
-- imply
  (Finset.univ : Finset (HexagonalBoxVertex n)).sup' ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩ (fun x => ∑ j ∈ Finset.range n, hexagonalOuterCenteredConn n q beta x j) ≤ 2 * hexagonalOuterInnerSig n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_centered_sup_le_two_sig_of_strict_comparison n q beta hq hbeta hcomp

/--
[hexagonalCenteredDenom_le_eight_sig_of_strict_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalCenteredDenom_le_eight_sig_of_strict_comparison_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hcomp : ∀ x : HexagonalBoxVertex n, ∀ k, k ∈ Finset.Icc 1 (n / 2) → 2 * k < n → hexagonalOuterCenteredConn n q beta x k ≤ hexagonalOuterInnerTheta q beta k) :
-- imply
  hexagonalCenteredDenom n q beta ≤ 8 * hexagonalOuterInnerSig n q beta / (n : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalCenteredDenom_le_eight_sig_of_strict_comparison n q beta hq hbeta hcomp

/--
[hexagonal_outer_inner_hcov_sharp_of_strict_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonal_outer_inner_hcov_sharp_of_strict_comparison_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hcomp : ∀ x : HexagonalBoxVertex n, ∀ k, k ∈ Finset.Icc 1 (n / 2) → 2 * k < n → hexagonalOuterCenteredConn n q beta x k ≤ hexagonalOuterInnerTheta q beta k) :
-- imply
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n)) (hexagonalBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q Lindeberg.mean mu (hexagonalInnerCrossInd n) * (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) / (8 * hexagonalOuterInnerSig n q beta / (n : Real)) ≤ ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_outer_inner_hcov_sharp_of_strict_comparison n hn q beta hq hbeta hcomp

/--
[hexagonal_outer_inner_differential_sharp_of_strict_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonal_outer_inner_differential_sharp_of_strict_comparison_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hcomp : ∀ x : HexagonalBoxVertex n, ∀ k, k ∈ Finset.Icc 1 (n / 2) → 2 * k < n → hexagonalOuterCenteredConn n q beta x k ≤ hexagonalOuterInnerTheta q beta k) :
-- imply
  hexagonalOuterInnerTheta q beta n * (1 - hexagonalOuterInnerTheta q beta n) / (8 * hexagonalOuterInnerSig n q beta / (n : Real)) ≤ hexagonalOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_outer_inner_differential_sharp_of_strict_comparison n hn q beta hq hbeta hcomp

/--
[hexagonalBox_root_neighbor_card_le_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalBox_root_neighbor_card_le_six_eq
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  ((hexagonalBoxGraph n).neighborFinset (hexagonalBoxRoot n)).card ≤ 6 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBox_root_neighbor_card_le_six n hn

/--
[hexagonalBox_root_degree_le_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalBox_root_degree_le_six_eq
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  (hexagonalBoxGraph n).degree (hexagonalBoxRoot n) ≤ 6 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalBox_root_degree_le_six n hn

/--
[hexagonalInnerIncident_card_le_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalInnerIncident_card_le_six_eq
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  (reindexedOpenIncidentEdges (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) (hexagonalBoxEndU n) (hexagonalBoxEndV n) (hexagonalBoxRoot n)).card ≤ 6 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalInnerIncident_card_le_six n hn

/--
[hexagonalInnerKappa_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalInnerKappa_pos_eq
  {n : Nat}
  {beta0 : Real} :
-- imply
  0 < hexagonalInnerKappa n beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalInnerKappa_pos n beta0

/--
[exp_neg_pow_six_le_hexagonalInnerKappa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma exp_neg_pow_six_le_hexagonalInnerKappa_eq
  {n : Nat}
  {beta0 : Real}
-- given
  (hn : 1 ≤ n)
  (hbeta0 : 0 ≤ beta0) :
-- imply
  Real.exp (-beta0) ^ 6 ≤ hexagonalInnerKappa n beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exp_neg_pow_six_le_hexagonalInnerKappa n hn beta0 hbeta0

/--
[hexagonal_outer_inner_one_sub_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonal_outer_inner_one_sub_lower_eq
  {n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0) :
-- imply
  hexagonalInnerKappa n beta0 ≤ 1 - hexagonalOuterInnerTheta q beta n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_outer_inner_one_sub_lower n hn q beta beta0 hq hbeta hbeta0

/--
[hexagonal_outer_inner_differential_linear_of_strict_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonal_outer_inner_differential_linear_of_strict_comparison_eq
  {n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0)
  (hcomp : ∀ x : HexagonalBoxVertex n, ∀ k, k ∈ Finset.Icc 1 (n / 2) → 2 * k < n → hexagonalOuterCenteredConn n q beta x k ≤ hexagonalOuterInnerTheta q beta k) :
-- imply
  hexagonalInnerKappa n beta0 * (hexagonalOuterInnerTheta q beta n / (8 * hexagonalOuterInnerSig n q beta / (n : Real))) ≤ hexagonalOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_outer_inner_differential_linear_of_strict_comparison n hn q beta beta0 hq hbeta hbeta0 hcomp

/--
[hexagonal_outer_inner_hcov_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonal_outer_inner_hcov_sharp_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  let mu := FK.activeBCProb (hexagonalBoxGraph (2 * n)) (hexagonalBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q Lindeberg.mean mu (hexagonalInnerCrossInd n) * (1 - Lindeberg.mean mu (hexagonalInnerCrossInd n)) / (8 * hexagonalOuterInnerSig n q beta / (n : Real)) ≤ ∑ e, Lindeberg.cov mu (hexagonalInnerCrossInd n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_outer_inner_hcov_sharp n hn q beta hq hbeta

/--
[hexagonal_outer_inner_differential_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonal_outer_inner_differential_sharp_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  hexagonalOuterInnerTheta q beta n * (1 - hexagonalOuterInnerTheta q beta n) / (8 * hexagonalOuterInnerSig n q beta / (n : Real)) ≤ hexagonalOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_outer_inner_differential_sharp n hn q beta hq hbeta

/--
[hexagonal_outer_inner_differential_linear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonal_outer_inner_differential_linear_eq
  {n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0) :
-- imply
  hexagonalInnerKappa n beta0 * (hexagonalOuterInnerTheta q beta n / (8 * hexagonalOuterInnerSig n q beta / (n : Real))) ≤ hexagonalOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_outer_inner_differential_linear n hn q beta beta0 hq hbeta hbeta0

/--
[hexagonalOuterInnerSig_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalOuterInnerSig_pos_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  0 < hexagonalOuterInnerSig n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterInnerSig_pos n hn q beta hq hbeta

/--
[hexagonalSharpConstant_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonalSharpConstant_pos_eq
  {beta0 : Real} :
-- imply
  0 < hexagonalSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalSharpConstant_pos beta0

/--
[hexagonal_outer_inner_differential_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean)
-/
@[path]
private lemma hexagonal_outer_inner_differential_uniform_eq
  {n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0) :
-- imply
  hexagonalSharpConstant beta0 * (((n : Real) / hexagonalOuterInnerSig n q beta) * hexagonalOuterInnerTheta q beta n) ≤ hexagonalOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_outer_inner_differential_uniform n hn q beta beta0 hq hbeta hbeta0


-- created on 2026-10-23
