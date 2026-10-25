import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.wifinterfaceconn
open SimpleGraph Function StatMech StatMech.Wif


/--
[wif_orbitCovers_of_interfaceConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wifinterfaceconn.lean)
-/
@[path]
private lemma wif_orbitCovers_of_interfaceConnected_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hIC : InterfaceConnected K)
  (hheads : ∀ d : Dart, (hd : IsBoundaryDart K d) → ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨a.1.head, a.2.2⟩ ⟨d.head, hd.2⟩) :
-- imply
  WpbOrbitCovers K a := by
-- proof
  apply StatMech.Wif.wif_orbitCovers_of_interfaceConnected K a hIC hheads

/--
[wif_interfaceConnected_of_orbitCovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wifinterfaceconn.lean)
-/
@[path]
private lemma wif_interfaceConnected_of_orbitCovers_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hcov : WpbOrbitCovers K a) :
-- imply
  InterfaceConnected K := by
-- proof
  apply StatMech.Wif.wif_interfaceConnected_of_orbitCovers K hK a hcov

/--
[wif_revCount_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wifinterfaceconn.lean)
-/
@[path]
private lemma wif_revCount_pm_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hpf : WpbPinchFree K a)
  (hIC : InterfaceConnected K)
  (hheads : ∀ d : Dart, (hd : IsBoundaryDart K d) → ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨a.1.head, a.2.2⟩ ⟨d.head, hd.2⟩)
  (hbuild : Euc.EucBuildable (wcd_toVtxFinset K hK)) :
-- imply
  revCount K a = 1 ∨ revCount K a = -1 := by
-- proof
  apply StatMech.Wif.wif_revCount_pm_one K hK a hpf hIC hheads hbuild

/--
[wif_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wifinterfaceconn.lean)
-/
@[path]
private lemma wif_balanceIsFour_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hpf : WpbPinchFree K a)
  (hIC : InterfaceConnected K)
  (hheads : ∀ d : Dart, (hd : IsBoundaryDart K d) → ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨a.1.head, a.2.2⟩ ⟨d.head, hd.2⟩)
  (hbuild : Euc.EucBuildable (wcd_toVtxFinset K hK)) :
-- imply
  BalanceIsFour K a := by
-- proof
  apply StatMech.Wif.wif_balanceIsFour K hK a hpf hIC hheads hbuild

/--
[wif_boundaryKingConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wifinterfaceconn.lean)
-/
@[path]
private lemma wif_boundaryKingConnected_eq
  {K : Set (Site 2)} :
-- imply
  BoundaryKingConnected K := by
-- proof
  apply StatMech.Wif.wif_boundaryKingConnected K

/--
[wif_kingTransport_route_dead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wifinterfaceconn.lean)
-/
@[path]
private lemma wif_kingTransport_route_dead_eq :
-- imply
  ¬ OrbitKingTransport ({(0 : Site 2)} : Set (Site 2)) := by
-- proof
  apply StatMech.Wif.wif_kingTransport_route_dead

/--
[wif_interfaceConnected_iff_orbitTraceSurjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wifinterfaceconn.lean)
-/
@[path]
private lemma wif_interfaceConnected_iff_orbitTraceSurjective_eq
  {K : Set (Site 2)} :
-- imply
  InterfaceConnected K ↔ OrbitTraceSurjective K := by
-- proof
  apply StatMech.Wif.wif_interfaceConnected_iff_orbitTraceSurjective K

/--
[wif_interfaceConnected_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wifinterfaceconn.lean)
-/
@[path]
private lemma wif_interfaceConnected_unitCell_eq :
-- imply
  InterfaceConnected unitCell := by
-- proof
  apply StatMech.Wif.wif_interfaceConnected_unitCell

/--
[wif_interfaceConnected_unitCell_of_orbitCovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wifinterfaceconn.lean)
-/
@[path]
private lemma wif_interfaceConnected_unitCell_of_orbitCovers_eq :
-- imply
  InterfaceConnected unitCell := by
-- proof
  apply StatMech.Wif.wif_interfaceConnected_unitCell_of_orbitCovers


-- created on 2026-10-23
