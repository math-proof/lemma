import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessOffCentre.Part4
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangularBox_reachOpen_hits_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularBox_reachOpen_hits_centered_eq
  {n m : Nat}
  {omega : ConfigSpace (triangularBoxGraph n).edgeSet}
  {x b : TriangularBoxVertex n}
-- given
  (hreach : ReachOpen (triangularBoxEndU n) (triangularBoxEndV n) omega x b)
  (hm : m ≤ centeredRadius x.1 b.1) :
-- imply
  ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega x (triangularBoxCenteredShell n x m) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBox_reachOpen_hits_centered hreach hm

/--
[triangularBox_rootShell_imp_centered_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularBox_rootShell_imp_centered_of_le_eq
  {n k m : Nat}
  {omega : ConfigSpace (triangularBoxGraph n).edgeSet}
  {x : TriangularBoxVertex n}
-- given
  (hm : m ≤ ((k : Int) - (siteRadius x.1 : Int)).natAbs) :
-- imply
  ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega x (triangularBoxShell n k) → ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega x (triangularBoxCenteredShell n x m) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBox_rootShell_imp_centered_of_le hm

/--
[triangular_rootShell_sum_le_centered_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangular_rootShell_sum_le_centered_sup_eq
  {n : Nat}
  {mu : ConfigSpace (triangularBoxGraph (2 * n)).edgeSet → Real}
  {u : TriangularBoxVertex n}
-- given
  (hmu0 : ∀ omega, 0 ≤ mu omega) :
-- imply
  (∑ k : ↑(Finset.Icc 1 n), Lindeberg.mean mu (fun omega => if ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega) u (triangularBoxShell n k) then (1 : Real) else 0)) ≤ 2 * (Finset.univ : Finset (TriangularBoxVertex n)).sup' ⟨triangularBoxRoot n, Finset.mem_univ _⟩ (fun x => ∑ j ∈ Finset.range n, Lindeberg.mean mu (fun omega => if ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega) x (triangularBoxCenteredShell n x j) then (1 : Real) else 0)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_rootShell_sum_le_centered_sup n mu hmu0 u

/--
[triangularOuterCenteredConn_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularOuterCenteredConn_nonneg_eq
  {n : Nat}
  {q beta : Real}
  {x : TriangularBoxVertex n}
  {j : Nat}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  0 ≤ triangularOuterCenteredConn n q beta x j := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterCenteredConn_nonneg n q beta hq hbeta x j

/--
[triangularOuterCenteredConn_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularOuterCenteredConn_zero_eq
  {n : Nat}
  {q beta : Real}
  {x : TriangularBoxVertex n}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  triangularOuterCenteredConn n q beta x 0 = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterCenteredConn_zero n q beta hq hbeta x

/--
[triangularOuterCenteredConn_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularOuterCenteredConn_le_one_eq
  {n : Nat}
  {q beta : Real}
  {x : TriangularBoxVertex n}
  {j : Nat}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  triangularOuterCenteredConn n q beta x j ≤ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterCenteredConn_le_one n q beta hq hbeta x j

/--
[triangularOuterCenteredConn_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularOuterCenteredConn_antitone_eq
  {n : Nat}
  {q beta : Real}
  {x : TriangularBoxVertex n}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  Antitone (triangularOuterCenteredConn n q beta x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterCenteredConn_antitone n q beta hq hbeta x

/--
[triangularOuterInnerTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularOuterInnerTheta_nonneg_eq
  {q beta : Real}
  {k : Nat}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  0 ≤ triangularOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterInnerTheta_nonneg q beta hq hbeta k

/--
[triangularOuterInnerTheta_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularOuterInnerTheta_zero_eq
  {q beta : Real} :
-- imply
  triangularOuterInnerTheta q beta 0 = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterInnerTheta_zero q beta

/--
[triangularCenteredShellEvent_iff_innerCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularCenteredShellEvent_iff_innerCross_eq
  {k : Nat}
  {omega : ConfigSpace (triangularBoxGraph (2 * k)).edgeSet}
-- given
  (hk : 1 ≤ k) :
-- imply
  omega ∈ triangularCenteredShellEvent (2 * k) k ↔ restrictConfig (triangularBoxEdgeLE (by omega : k ≤ 2 * k)) omega ∈ openCrossEvent (triangularBoxEndU k) (triangularBoxEndV k) (triangularBoxRoot k) (triangularBoxShell k k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCenteredShellEvent_iff_innerCross k hk omega

/--
[triangularCenteredFullMass_eq_outerInnerTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularCenteredFullMass_eq_outerInnerTheta_eq
  {k : Nat}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  (∑ omega : ConfigSpace (Sym2 (TriangularBoxVertex (2 * k))), (triangularCenteredShellFullEvent (2 * k) k).indicator (fun _ => (1 : Real)) omega * FK.wiredFkProb (triangularBoxGraph (2 * k)) (fun y => y ∈ triangularBoxShell (2 * k) (2 * k)) (1 - Real.exp (-beta)) q omega) = triangularOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCenteredFullMass_eq_outerInnerTheta k hk q beta hq hbeta

/--
[triangular_centeredConn_imp_transShell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangular_centeredConn_imp_transShell_eq
  {n k : Nat}
  {x : TriangularBoxVertex n}
  {rho : ConfigSpace (triangularBoxGraph (2 * n)).edgeSet}
-- given
  (hk : 1 ≤ k)
  (hkn : 2 * k < n)
  (hconn : ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) rho) x (triangularBoxCenteredShell n x k)) :
-- imply
  let hsub := triangularTransBox_subset_double x.2 hkn let transIncl := triangularTransBoxIncl hsub let hadjm := ocd_comapAdjMatch triangularGraph transIncl (fun _ => rfl) ocd_innerRestrictActive (triangularTransBoxGraph (2 * k) x.1) (triangularBoxGraph (2 * n)) transIncl hadjm rho ∈ triangularTransShellEvent (2 * k) k x.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_centeredConn_imp_transShell x hk hkn rho hconn

/--
[triangularOuterCenteredConn_le_theta_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularOuterCenteredConn_le_theta_strict_eq
  {n k : Nat}
  {x : TriangularBoxVertex n}
  {q beta : Real}
-- given
  (hk : 1 ≤ k)
  (hkn : 2 * k < n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  triangularOuterCenteredConn n q beta x k ≤ triangularOuterInnerTheta q beta k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterCenteredConn_le_theta_strict n k x hk hkn q beta hq hbeta

/--
[triangularCenteredDenom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularCenteredDenom_pos_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  0 < triangularCenteredDenom n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCenteredDenom_pos n hn q beta hq hbeta

/--
[triangular_outer_inner_hcov_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangular_outer_inner_hcov_centered_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n)) (triangularBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q Lindeberg.mean mu (triangularInnerCrossInd n) * (1 - Lindeberg.mean mu (triangularInnerCrossInd n)) / triangularCenteredDenom n q beta ≤ ∑ e, Lindeberg.cov mu (triangularInnerCrossInd n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_outer_inner_hcov_centered n hn q beta hq hbeta

/--
[triangular_centered_sup_le_two_sig_of_strict_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangular_centered_sup_le_two_sig_of_strict_comparison_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hcomp : ∀ x : TriangularBoxVertex n, ∀ k, k ∈ Finset.Icc 1 (n / 2) → 2 * k < n → triangularOuterCenteredConn n q beta x k ≤ triangularOuterInnerTheta q beta k) :
-- imply
  (Finset.univ : Finset (TriangularBoxVertex n)).sup' ⟨triangularBoxRoot n, Finset.mem_univ _⟩ (fun x => ∑ j ∈ Finset.range n, triangularOuterCenteredConn n q beta x j) ≤ 2 * triangularOuterInnerSig n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_centered_sup_le_two_sig_of_strict_comparison n q beta hq hbeta hcomp

/--
[triangularCenteredDenom_le_eight_sig_of_strict_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularCenteredDenom_le_eight_sig_of_strict_comparison_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hcomp : ∀ x : TriangularBoxVertex n, ∀ k, k ∈ Finset.Icc 1 (n / 2) → 2 * k < n → triangularOuterCenteredConn n q beta x k ≤ triangularOuterInnerTheta q beta k) :
-- imply
  triangularCenteredDenom n q beta ≤ 8 * triangularOuterInnerSig n q beta / (n : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCenteredDenom_le_eight_sig_of_strict_comparison n q beta hq hbeta hcomp

/--
[triangular_outer_inner_hcov_sharp_of_strict_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangular_outer_inner_hcov_sharp_of_strict_comparison_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hcomp : ∀ x : TriangularBoxVertex n, ∀ k, k ∈ Finset.Icc 1 (n / 2) → 2 * k < n → triangularOuterCenteredConn n q beta x k ≤ triangularOuterInnerTheta q beta k) :
-- imply
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n)) (triangularBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q Lindeberg.mean mu (triangularInnerCrossInd n) * (1 - Lindeberg.mean mu (triangularInnerCrossInd n)) / (8 * triangularOuterInnerSig n q beta / (n : Real)) ≤ ∑ e, Lindeberg.cov mu (triangularInnerCrossInd n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_outer_inner_hcov_sharp_of_strict_comparison n hn q beta hq hbeta hcomp

/--
[triangular_outer_inner_differential_sharp_of_strict_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangular_outer_inner_differential_sharp_of_strict_comparison_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hcomp : ∀ x : TriangularBoxVertex n, ∀ k, k ∈ Finset.Icc 1 (n / 2) → 2 * k < n → triangularOuterCenteredConn n q beta x k ≤ triangularOuterInnerTheta q beta k) :
-- imply
  triangularOuterInnerTheta q beta n * (1 - triangularOuterInnerTheta q beta n) / (8 * triangularOuterInnerSig n q beta / (n : Real)) ≤ triangularOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_outer_inner_differential_sharp_of_strict_comparison n hn q beta hq hbeta hcomp

/--
[triangularBox_root_neighbor_card_le_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularBox_root_neighbor_card_le_six_eq
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  ((triangularBoxGraph n).neighborFinset (triangularBoxRoot n)).card ≤ 6 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBox_root_neighbor_card_le_six n hn

/--
[triangularBox_root_degree_le_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularBox_root_degree_le_six_eq
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  (triangularBoxGraph n).degree (triangularBoxRoot n) ≤ 6 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularBox_root_degree_le_six n hn

/--
[triangularInnerIncident_card_le_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularInnerIncident_card_le_six_eq
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  (reindexedOpenIncidentEdges (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) (triangularBoxEndU n) (triangularBoxEndV n) (triangularBoxRoot n)).card ≤ 6 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularInnerIncident_card_le_six n hn

/--
[triangularInnerKappa_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularInnerKappa_pos_eq
  {n : Nat}
  {beta0 : Real} :
-- imply
  0 < triangularInnerKappa n beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularInnerKappa_pos n beta0

/--
[exp_neg_pow_six_le_triangularInnerKappa](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma exp_neg_pow_six_le_triangularInnerKappa_eq
  {n : Nat}
  {beta0 : Real}
-- given
  (hn : 1 ≤ n)
  (hbeta0 : 0 ≤ beta0) :
-- imply
  Real.exp (-beta0) ^ 6 ≤ triangularInnerKappa n beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exp_neg_pow_six_le_triangularInnerKappa n hn beta0 hbeta0

/--
[triangular_outer_inner_one_sub_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangular_outer_inner_one_sub_lower_eq
  {n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0) :
-- imply
  triangularInnerKappa n beta0 ≤ 1 - triangularOuterInnerTheta q beta n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_outer_inner_one_sub_lower n hn q beta beta0 hq hbeta hbeta0

/--
[triangular_outer_inner_differential_linear_of_strict_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangular_outer_inner_differential_linear_of_strict_comparison_eq
  {n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0)
  (hcomp : ∀ x : TriangularBoxVertex n, ∀ k, k ∈ Finset.Icc 1 (n / 2) → 2 * k < n → triangularOuterCenteredConn n q beta x k ≤ triangularOuterInnerTheta q beta k) :
-- imply
  triangularInnerKappa n beta0 * (triangularOuterInnerTheta q beta n / (8 * triangularOuterInnerSig n q beta / (n : Real))) ≤ triangularOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_outer_inner_differential_linear_of_strict_comparison n hn q beta beta0 hq hbeta hbeta0 hcomp

/--
[triangular_outer_inner_hcov_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangular_outer_inner_hcov_sharp_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  let mu := FK.activeBCProb (triangularBoxGraph (2 * n)) (triangularBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q Lindeberg.mean mu (triangularInnerCrossInd n) * (1 - Lindeberg.mean mu (triangularInnerCrossInd n)) / (8 * triangularOuterInnerSig n q beta / (n : Real)) ≤ ∑ e, Lindeberg.cov mu (triangularInnerCrossInd n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_outer_inner_hcov_sharp n hn q beta hq hbeta

/--
[triangular_outer_inner_differential_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangular_outer_inner_differential_sharp_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  triangularOuterInnerTheta q beta n * (1 - triangularOuterInnerTheta q beta n) / (8 * triangularOuterInnerSig n q beta / (n : Real)) ≤ triangularOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_outer_inner_differential_sharp n hn q beta hq hbeta

/--
[triangular_outer_inner_differential_linear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangular_outer_inner_differential_linear_eq
  {n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0) :
-- imply
  triangularInnerKappa n beta0 * (triangularOuterInnerTheta q beta n / (8 * triangularOuterInnerSig n q beta / (n : Real))) ≤ triangularOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_outer_inner_differential_linear n hn q beta beta0 hq hbeta hbeta0

/--
[triangularOuterInnerSig_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularOuterInnerSig_pos_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta) :
-- imply
  0 < triangularOuterInnerSig n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterInnerSig_pos n hn q beta hq hbeta

/--
[triangularSharpConstant_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangularSharpConstant_pos_eq
  {beta0 : Real} :
-- imply
  0 < triangularSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularSharpConstant_pos beta0

/--
[triangular_outer_inner_differential_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean)
-/
@[path]
private lemma triangular_outer_inner_differential_uniform_eq
  {n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 ≤ n)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0) :
-- imply
  triangularSharpConstant beta0 * (((n : Real) / triangularOuterInnerSig n q beta) * triangularOuterInnerTheta q beta n) ≤ triangularOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_outer_inner_differential_uniform n hn q beta beta0 hq hbeta hbeta0


-- created on 2026-10-23
