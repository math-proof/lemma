import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriangularOffCentre
open Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[ocd_comapAdjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma ocd_comapAdjMatch_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {Sin Sout : Set V}
  [Fintype Sin]
  [Fintype Sout]
-- given
  (iota : Sin -> Sout)
  (hiotaVal : forall x, (iota x : V) = (x : V)) :
-- imply
  ocd_AdjMatch (SimpleGraph.comap Subtype.val G) (SimpleGraph.comap Subtype.val G) iota := by
-- proof
  apply StatMech.FK.ocd_comapAdjMatch G iota hiotaVal

/--
[ocd_comap_bdryIn_of_outsideGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma ocd_comap_bdryIn_of_outsideGraph_adj_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {Sin Sout : Set V}
  [Fintype Sin]
  [Fintype Sout]
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
  {psi : ConfigSpace (Sym2 Sout)}
  {x : Sin}
  {z : Sout}
-- given
  (iota : Sin -> Sout)
  (hiotaVal : forall x, (iota x : V) = (x : V))
  (bdryOut : Sout -> Prop)
  (bdryIn : Sin -> Prop)
  (hmargin : forall x : Sin, ¬ bdryOut (iota x))
  (hbdryIn : forall (x : Sin) (z : V), G.Adj x.1 z -> z ∉ Sin -> bdryIn x)
  (h : (ocd_outsideGraph (SimpleGraph.comap Subtype.val G) iota bdryOut psi).Adj (iota x) z) :
-- imply
  bdryIn x := by
-- proof
  apply StatMech.FK.ocd_comap_bdryIn_of_outsideGraph_adj G iota hiotaVal bdryOut bdryIn hmargin hbdryIn psi h

/--
[ocd_comapInducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma ocd_comapInducedWiring_le_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {Sin Sout : Set V}
  [Fintype Sin]
  [Fintype Sout]
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
  {psi : ConfigSpace (Sym2 Sout)}
-- given
  (iota : Sin -> Sout)
  (hiotaVal : forall x, (iota x : V) = (x : V))
  (hiota : Function.Injective iota)
  (bdryOut : Sout -> Prop)
  (bdryIn : Sin -> Prop)
  (hmargin : forall x : Sin, ¬ bdryOut (iota x))
  (hbdryIn : forall (x : Sin) (z : V), G.Adj x.1 z -> z ∉ Sin -> bdryIn x) :
-- imply
  ocd_inducedWiring (SimpleGraph.comap Subtype.val G) iota bdryOut psi <= boundaryCliqueGraph bdryIn := by
-- proof
  apply StatMech.FK.ocd_comapInducedWiring_le G iota hiotaVal hiota bdryOut bdryIn hmargin hbdryIn psi

/--
[ocd_comapInducedWiring_le_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma ocd_comapInducedWiring_le_equiv_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {Sin Sout : Set V}
  [Fintype Sin]
  [Fintype Sout]
  {e : V ≃ V}
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
  {psi : ConfigSpace (Sym2 Sout)}
-- given
  (he : ∀ x y, G.Adj (e x) (e y) ↔ G.Adj x y)
  (iota : Sin -> Sout)
  (hiotaVal : ∀ x, (iota x : V) = e (x : V))
  (hiota : Function.Injective iota)
  (bdryOut : Sout -> Prop)
  (bdryIn : Sin -> Prop)
  (hmargin : ∀ x : Sin, ¬ bdryOut (iota x))
  (hbdryIn : ∀ (x : Sin) (z : V), G.Adj x.1 z -> z ∉ Sin -> bdryIn x) :
-- imply
  ocd_inducedWiring (SimpleGraph.comap Subtype.val G) iota bdryOut psi <= boundaryCliqueGraph bdryIn := by
-- proof
  apply StatMech.FK.ocd_comapInducedWiring_le_equiv G e he iota hiotaVal hiota bdryOut bdryIn hmargin hbdryIn psi

/--
[triangularTransBoxIncl_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransBoxIncl_val_eq
  {R N : Nat}
  {x : Site 2}
  {y : TriangularTransBoxVertex R x}
-- given
  (hsub : triangularTransBox R x ⊆ box 2 N) :
-- imply
  (triangularTransBoxIncl hsub y : Site 2) = y.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransBoxIncl_val hsub y

/--
[triangularTransBoxIncl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransBoxIncl_injective_eq
  {R N : Nat}
  {x : Site 2}
-- given
  (hsub : triangularTransBox R x ⊆ box 2 N) :
-- imply
  Function.Injective (triangularTransBoxIncl hsub) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransBoxIncl_injective hsub

/--
[triangularTransEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransEquiv_adj_eq
  {R : Nat}
  {x : Site 2}
  {u v : TriangularBoxVertex R} :
-- imply
  (triangularBoxGraph R).Adj u v ↔ (triangularTransBoxGraph R x).Adj (StatMech.FK.fvs_transEquiv 2 R x u) (StatMech.FK.fvs_transEquiv 2 R x v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransEquiv_adj R x u v

/--
[triangularTransEquiv_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransEquiv_center_eq
  {R : Nat}
  {x : Site 2} :
-- imply
  StatMech.FK.fvs_transEquiv 2 R x (triangularBoxRoot R) = triangularTransBoxCenter R x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransEquiv_center R x

/--
[triangularTransEquiv_mem_shell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransEquiv_mem_shell_eq
  {R k : Nat}
  {x : Site 2}
  {y : TriangularBoxVertex R} :
-- imply
  StatMech.FK.fvs_transEquiv 2 R x y ∈ triangularTransBoxShell R k x ↔ y ∈ triangularBoxShell R k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransEquiv_mem_shell R k x y

/--
[triangularTransShellEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransShellEvent_increasing_eq
  {R k : Nat}
  {x : Site 2} :
-- imply
  IsIncreasing (triangularTransShellEvent R k x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransShellEvent_increasing R k x

/--
[triangularCenteredShellEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularCenteredShellEvent_increasing_eq
  {R k : Nat} :
-- imply
  IsIncreasing (triangularCenteredShellEvent R k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCenteredShellEvent_increasing R k

/--
[reachOpen_edgeSet_iff_openSub_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma reachOpen_edgeSet_iff_openSub_reachable_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {omega : ConfigSpace H.edgeSet}
  {u v : W} :
-- imply
  ReachOpen (fun e : H.edgeSet => e.1.out.1) (fun e : H.edgeSet => e.1.out.2) omega u v ↔ (openSub H (extendActive H omega)).Reachable u v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.reachOpen_edgeSet_iff_openSub_reachable H omega u v

/--
[connOpenSet_edgeSet_iff_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma connOpenSet_edgeSet_iff_openSub_eq
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
  apply StatMech.FK.PeriodicPlanar.connOpenSet_edgeSet_iff_openSub H omega u B

/--
[restrictActive_preimage_triangularCenteredShellEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma restrictActive_preimage_triangularCenteredShellEvent_eq
  {R k : Nat} :
-- imply
  restrictActive (triangularBoxGraph R) ⁻¹' triangularCenteredShellEvent R k = triangularCenteredShellFullEvent R k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.restrictActive_preimage_triangularCenteredShellEvent R k

/--
[restrictActive_preimage_triangularTransShellEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma restrictActive_preimage_triangularTransShellEvent_eq
  {R k : Nat}
  {x : Site 2} :
-- imply
  restrictActive (triangularTransBoxGraph R x) ⁻¹' triangularTransShellEvent R k x = triangularTransShellFullEvent R k x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.restrictActive_preimage_triangularTransShellEvent R k x

/--
[reCfgIso_preimage_triangularCenteredShellFullEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma reCfgIso_preimage_triangularCenteredShellFullEvent_eq
  {R k : Nat}
  {x : Site 2} :
-- imply
  reCfgIso (StatMech.FK.fvs_transEquiv 2 R x) ⁻¹' triangularCenteredShellFullEvent R k = triangularTransShellFullEvent R k x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.reCfgIso_preimage_triangularCenteredShellFullEvent R k x

/--
[triangularTransEquiv_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransEquiv_boundary_eq
  {R : Nat}
  {x : Site 2}
  {y : TriangularBoxVertex R} :
-- imply
  y ∈ triangularBoxShell R R ↔ triangularTransBoxBoundary R x (StatMech.FK.fvs_transEquiv 2 R x y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransEquiv_boundary R x y

/--
[triangularTransShellEvent_activeBCMean_eq_centeredFullMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransShellEvent_activeBCMean_eq_centeredFullMass_eq
  {R k : Nat}
  {x : Site 2}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  activeBCMean (triangularTransBoxGraph R x) (boundaryCliqueGraph (triangularTransBoxBoundary R x)) (fun _ => p) q ((triangularTransShellEvent R k x).indicator fun _ => (1 : Real)) = ∑ omega : ConfigSpace (Sym2 (TriangularBoxVertex R)), (triangularCenteredShellFullEvent R k).indicator (fun _ => (1 : Real)) omega * wiredFkProb (triangularBoxGraph R) (fun y => y ∈ triangularBoxShell R R) p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransShellEvent_activeBCMean_eq_centeredFullMass R k x hp hp1 hq

/--
[triangularTransShellEvent_betaMean_eq_centeredFullMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransShellEvent_betaMean_eq_centeredFullMass_eq
  {R k : Nat}
  {x : Site 2}
  {q beta : Real}
-- given
  (hq : 0 < q)
  (hbeta : 0 < beta) :
-- imply
  activeBCMean (triangularTransBoxGraph R x) (boundaryCliqueGraph (triangularTransBoxBoundary R x)) (betaParams (fun _ => 1) beta) q ((triangularTransShellEvent R k x).indicator fun _ => (1 : Real)) = ∑ omega : ConfigSpace (Sym2 (TriangularBoxVertex R)), (triangularCenteredShellFullEvent R k).indicator (fun _ => (1 : Real)) omega * wiredFkProb (triangularBoxGraph R) (fun y => y ∈ triangularBoxShell R R) (1 - Real.exp (-beta)) q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransShellEvent_betaMean_eq_centeredFullMass R k x q beta hq hbeta

/--
[triangularTransBox_subset_double](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransBox_subset_double_eq
  {n k : Nat}
  {x : Site 2}
-- given
  (hx : x ∈ box 2 n)
  (hkn : 2 * k < n) :
-- imply
  triangularTransBox (2 * k) x ⊆ box 2 (2 * n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransBox_subset_double hx hkn

/--
[triangularTransBox_outer_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransBox_outer_margin_eq
  {n k : Nat}
  {x : Site 2}
  {y : TriangularTransBoxVertex (2 * k) x}
-- given
  (hx : x ∈ box 2 n)
  (hkn : 2 * k < n) :
-- imply
  triangularTransBoxIncl (triangularTransBox_subset_double hx hkn) y ∉ triangularBoxShell (2 * n) (2 * n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransBox_outer_margin hx hkn y

/--
[triangular_adj_sub_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangular_adj_sub_right_eq
  {x : Site 2}
  {y z : Site 2}
-- given
  (hyz : triangularGraph.Adj y z) :
-- imply
  triangularGraph.Adj (y - x) (z - x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_adj_sub_right x hyz

/--
[triangularTransBox_boundary_of_adj_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransBox_boundary_of_adj_outside_eq
  {R : Nat}
  {x : Site 2}
  {y : TriangularTransBoxVertex R x}
  {z : Site 2}
-- given
  (hR : 1 <= R)
  (hyz : triangularGraph.Adj y.1 z)
  (hz : z ∉ triangularTransBox R x) :
-- imply
  triangularTransBoxBoundary R x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransBox_boundary_of_adj_outside hR y z hyz hz

/--
[triangularTransBox_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransBox_inducedWiring_le_eq
  {n k : Nat}
  {x : Site 2}
  {psi : ConfigSpace (Sym2 (TriangularBoxVertex (2 * n)))}
-- given
  (hx : x ∈ box 2 n)
  (hk : 1 <= k)
  (hkn : 2 * k < n) :
-- imply
  ocd_inducedWiring (triangularBoxGraph (2 * n)) (triangularTransBoxIncl (triangularTransBox_subset_double hx hkn)) (fun y => y ∈ triangularBoxShell (2 * n) (2 * n)) psi <= boundaryCliqueGraph (triangularTransBoxBoundary (2 * k) x) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransBox_inducedWiring_le hx hk hkn psi

/--
[triangularTransBox_activeBCMean_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean)
-/
@[path]
private lemma triangularTransBox_activeBCMean_le_eq
  {n k : Nat}
  {x : Site 2}
  {q beta : Real}
  {A : Set (ConfigSpace (triangularTransBoxGraph (2 * k) x).edgeSet)}
-- given
  (hx : x ∈ box 2 n)
  (hk : 1 <= k)
  (hkn : 2 * k < n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hA : IsIncreasing A) :
-- imply
  activeBCMean (triangularBoxGraph (2 * n)) (boundaryCliqueGraph (fun y => y ∈ triangularBoxShell (2 * n) (2 * n))) (betaParams (fun _ => 1) beta) q (fun rho => A.indicator (fun _ => (1 : Real)) (ocd_innerRestrictActive (triangularTransBoxGraph (2 * k) x) (triangularBoxGraph (2 * n)) (triangularTransBoxIncl (triangularTransBox_subset_double hx hkn)) (ocd_comapAdjMatch triangularGraph (triangularTransBoxIncl (triangularTransBox_subset_double hx hkn)) (fun _ => rfl)) rho)) <= activeBCMean (triangularTransBoxGraph (2 * k) x) (boundaryCliqueGraph (triangularTransBoxBoundary (2 * k) x)) (betaParams (fun _ => 1) beta) q (A.indicator fun _ => (1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTransBox_activeBCMean_le hx hk hkn q beta hq hbeta hA


-- created on 2026-10-23
