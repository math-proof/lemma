import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part5
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[hexagonalTransBoxIncl_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransBoxIncl_val_eq
  {R N : Nat}
  {x : Site 2}
  {y : HexagonalTransBoxVertex R x}
-- given
  (hsub : hexagonalTransBox R x ⊆ box 2 N) :
-- imply
  (hexagonalTransBoxIncl hsub y).1.1 = y.1.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransBoxIncl_val hsub y

/--
[hexagonalTransBoxIncl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransBoxIncl_injective_eq
  {R N : Nat}
  {x : Site 2}
-- given
  (hsub : hexagonalTransBox R x ⊆ box 2 N) :
-- imply
  Function.Injective (hexagonalTransBoxIncl hsub) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransBoxIncl_injective hsub

/--
[hexagonalReflect_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalReflect_adj_eq
  {u v : HexVertex} :
-- imply
  hexagonalGraph.Adj u v ↔ hexagonalGraph.Adj (hexagonalReflect u) (hexagonalReflect v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalReflect_adj u v

/--
[hexagonalTransEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransEquiv_adj_eq
  {R : Nat}
  {x : HexVertex}
  {u v : HexagonalBoxVertex R} :
-- imply
  (hexagonalBoxGraph R).Adj u v ↔ (hexagonalTransBoxGraph R x.1).Adj (hexagonalTransEquiv R x u) (hexagonalTransEquiv R x v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransEquiv_adj R x u v

/--
[hexagonalTransEquiv_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransEquiv_center_eq
  {R : Nat}
  {x : HexVertex} :
-- imply
  hexagonalTransEquiv R x (hexagonalBoxRoot R) = hexagonalTransBoxCenter R x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransEquiv_center R x

/--
[hexagonalTransEquiv_mem_shell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransEquiv_mem_shell_eq
  {R k : Nat}
  {x : HexVertex}
  {y : HexagonalBoxVertex R} :
-- imply
  hexagonalTransEquiv R x y ∈ hexagonalTransBoxShell R k x.1 ↔ y ∈ hexagonalBoxShell R k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransEquiv_mem_shell R k x y

/--
[hexagonalTransShellEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransShellEvent_increasing_eq
  {R k : Nat}
  {x : HexVertex} :
-- imply
  IsIncreasing (hexagonalTransShellEvent R k x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransShellEvent_increasing R k x

/--
[hexagonalCenteredShellEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalCenteredShellEvent_increasing_eq
  {R k : Nat} :
-- imply
  IsIncreasing (hexagonalCenteredShellEvent R k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalCenteredShellEvent_increasing R k

/--
[hexagonal_reachOpen_edgeSet_iff_openSub_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonal_reachOpen_edgeSet_iff_openSub_reachable_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {omega : ConfigSpace H.edgeSet}
  {u v : W} :
-- imply
  ReachOpen (fun e : H.edgeSet => e.1.out.1) (fun e : H.edgeSet => e.1.out.2) omega u v ↔ (openSub H (extendActive H omega)).Reachable u v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_reachOpen_edgeSet_iff_openSub_reachable H omega u v

/--
[hexagonal_connOpenSet_edgeSet_iff_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonal_connOpenSet_edgeSet_iff_openSub_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {omega : ConfigSpace H.edgeSet}
  {u : W}
  {B : Set W} :
-- imply
  ConnOpenSet (fun e : H.edgeSet => e.1.out.1) (fun e : H.edgeSet => e.1.out.2) omega u B ↔ ∃ v ∈ B, (openSub H (extendActive H omega)).Reachable u v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_connOpenSet_edgeSet_iff_openSub H omega u B

/--
[restrictActive_preimage_hexagonalCenteredShellEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma restrictActive_preimage_hexagonalCenteredShellEvent_eq
  {R k : Nat} :
-- imply
  restrictActive (hexagonalBoxGraph R) ⁻¹' hexagonalCenteredShellEvent R k = hexagonalCenteredShellFullEvent R k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.restrictActive_preimage_hexagonalCenteredShellEvent R k

/--
[restrictActive_preimage_hexagonalTransShellEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma restrictActive_preimage_hexagonalTransShellEvent_eq
  {R k : Nat}
  {x : HexVertex} :
-- imply
  restrictActive (hexagonalTransBoxGraph R x.1) ⁻¹' hexagonalTransShellEvent R k x = hexagonalTransShellFullEvent R k x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.restrictActive_preimage_hexagonalTransShellEvent R k x

/--
[reCfgIso_preimage_hexagonalCenteredShellFullEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma reCfgIso_preimage_hexagonalCenteredShellFullEvent_eq
  {R k : Nat}
  {x : HexVertex} :
-- imply
  reCfgIso (hexagonalTransEquiv R x) ⁻¹' hexagonalCenteredShellFullEvent R k = hexagonalTransShellFullEvent R k x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.reCfgIso_preimage_hexagonalCenteredShellFullEvent R k x

/--
[hexagonalTransEquiv_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransEquiv_boundary_eq
  {R : Nat}
  {x : HexVertex}
  {y : HexagonalBoxVertex R} :
-- imply
  y ∈ hexagonalBoxShell R R ↔ hexagonalTransBoxBoundary R x.1 (hexagonalTransEquiv R x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransEquiv_boundary R x y

/--
[hexagonalTransShellEvent_activeBCMean_eq_centeredFullMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransShellEvent_activeBCMean_eq_centeredFullMass_eq
  {R k : Nat}
  {x : HexVertex}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  activeBCMean (hexagonalTransBoxGraph R x.1) (boundaryCliqueGraph (hexagonalTransBoxBoundary R x.1)) (fun _ => p) q ((hexagonalTransShellEvent R k x).indicator fun _ => (1 : Real)) = ∑ omega : ConfigSpace (Sym2 (HexagonalBoxVertex R)), (hexagonalCenteredShellFullEvent R k).indicator (fun _ => (1 : Real)) omega * wiredFkProb (hexagonalBoxGraph R) (fun y => y ∈ hexagonalBoxShell R R) p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransShellEvent_activeBCMean_eq_centeredFullMass R k x hp hp1 hq

/--
[hexagonalTransShellEvent_betaMean_eq_centeredFullMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransShellEvent_betaMean_eq_centeredFullMass_eq
  {R k : Nat}
  {x : HexVertex}
  {q beta : Real}
-- given
  (hq : 0 < q)
  (hbeta : 0 < beta) :
-- imply
  activeBCMean (hexagonalTransBoxGraph R x.1) (boundaryCliqueGraph (hexagonalTransBoxBoundary R x.1)) (betaParams (fun _ => 1) beta) q ((hexagonalTransShellEvent R k x).indicator fun _ => (1 : Real)) = ∑ omega : ConfigSpace (Sym2 (HexagonalBoxVertex R)), (hexagonalCenteredShellFullEvent R k).indicator (fun _ => (1 : Real)) omega * wiredFkProb (hexagonalBoxGraph R) (fun y => y ∈ hexagonalBoxShell R R) (1 - Real.exp (-beta)) q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransShellEvent_betaMean_eq_centeredFullMass R k x q beta hq hbeta

/--
[hexagonalTransBox_subset_double](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransBox_subset_double_eq
  {n k : Nat}
  {x : Site 2}
-- given
  (hx : x ∈ box 2 n)
  (hkn : 2 * k < n) :
-- imply
  hexagonalTransBox (2 * k) x ⊆ box 2 (2 * n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransBox_subset_double hx hkn

/--
[hexagonalTransBox_outer_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransBox_outer_margin_eq
  {n k : Nat}
  {x : Site 2}
  {y : HexagonalTransBoxVertex (2 * k) x}
-- given
  (hx : x ∈ box 2 n)
  (hkn : 2 * k < n) :
-- imply
  hexagonalTransBoxIncl (hexagonalTransBox_subset_double hx hkn) y ∉ hexagonalBoxShell (2 * n) (2 * n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransBox_outer_margin hx hkn y

/--
[hexagonal_adj_sub_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonal_adj_sub_right_eq
  {x : Site 2}
  {y z : HexVertex}
-- given
  (hyz : hexagonalGraph.Adj y z) :
-- imply
  hexagonalGraph.Adj (y.1 - x, y.2) (z.1 - x, z.2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_adj_sub_right x hyz

/--
[hexagonalTransBox_boundary_of_adj_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransBox_boundary_of_adj_outside_eq
  {R : Nat}
  {x : Site 2}
  {y : HexagonalTransBoxVertex R x}
  {z : HexVertex}
-- given
  (hR : 1 <= R)
  (hyz : hexagonalGraph.Adj y.1 z)
  (hz : z.1 ∉ hexagonalTransBox R x) :
-- imply
  hexagonalTransBoxBoundary R x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransBox_boundary_of_adj_outside hR y z hyz hz

/--
[hexagonalTransBox_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransBox_inducedWiring_le_eq
  {n k : Nat}
  {x : Site 2}
  {psi : ConfigSpace (Sym2 (HexagonalBoxVertex (2 * n)))}
-- given
  (hx : x ∈ box 2 n)
  (hk : 1 <= k)
  (hkn : 2 * k < n) :
-- imply
  ocd_inducedWiring (hexagonalBoxGraph (2 * n)) (hexagonalTransBoxIncl (hexagonalTransBox_subset_double hx hkn)) (fun y => y ∈ hexagonalBoxShell (2 * n) (2 * n)) psi <= boundaryCliqueGraph (hexagonalTransBoxBoundary (2 * k) x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransBox_inducedWiring_le hx hk hkn psi

/--
[hexagonalTransBox_activeBCMean_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean)
-/
@[path]
private lemma hexagonalTransBox_activeBCMean_le_eq
  {n k : Nat}
  {x : Site 2}
  {q beta : Real}
  {A : Set (ConfigSpace (hexagonalTransBoxGraph (2 * k) x).edgeSet)}
-- given
  (hx : x ∈ box 2 n)
  (hk : 1 <= k)
  (hkn : 2 * k < n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hA : IsIncreasing A) :
-- imply
  activeBCMean (hexagonalBoxGraph (2 * n)) (boundaryCliqueGraph (fun y => y ∈ hexagonalBoxShell (2 * n) (2 * n))) (betaParams (fun _ => 1) beta) q (fun rho => A.indicator (fun _ => (1 : Real)) (ocd_innerRestrictActive (hexagonalTransBoxGraph (2 * k) x) (hexagonalBoxGraph (2 * n)) (hexagonalTransBoxIncl (hexagonalTransBox_subset_double hx hkn)) (ocd_comapAdjMatch hexagonalGraph (hexagonalTransBoxIncl (hexagonalTransBox_subset_double hx hkn)) (fun _ => rfl)) rho)) <= activeBCMean (hexagonalTransBoxGraph (2 * k) x) (boundaryCliqueGraph (hexagonalTransBoxBoundary (2 * k) x)) (betaParams (fun _ => 1) beta) q (A.indicator fun _ => (1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTransBox_activeBCMean_le hx hk hkn q beta hq hbeta hA


-- created on 2026-10-23
