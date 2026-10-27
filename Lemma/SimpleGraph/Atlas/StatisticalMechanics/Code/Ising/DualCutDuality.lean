import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.DualCutDuality
open Finset SimpleGraph StatMech StatMech.Ising


/--
[primalMinus_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma primalMinus_adj_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {x y : V} :
-- imply
  (primalMinus Gp δ).Adj x y ↔ Gp.Adj x y ∧ s(x, y) ∉ δ := by
-- proof
  apply StatMech.Ising.primalMinus_adj δ x y

/--
[primalMinus_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma primalMinus_le_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ : Finset (Sym2 V)} :
-- imply
  primalMinus Gp δ ≤ Gp := by
-- proof
  apply StatMech.Ising.primalMinus_le δ

/--
[walkParity_mapLe_primalMinus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma walkParity_mapLe_primalMinus_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {x y : V}
  {p : (primalMinus Gp δ).Walk x y} :
-- imply
  walkParity Gp δ (p.mapLe (primalMinus_le δ)) = false := by
-- proof
  apply StatMech.Ising.walkParity_mapLe_primalMinus p

/--
[primalMinus_sameSide_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma primalMinus_sameSide_of_reachable_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {v₀ : V}
  {x y : V}
-- given
  (hev : EvenOnCycles Gp δ)
  (hG : Gp.Preconnected)
  (hr : (primalMinus Gp δ).Reachable x y) :
-- imply
  parityConfig Gp δ hG v₀ x = parityConfig Gp δ hG v₀ y := by
-- proof
  apply StatMech.Ising.primalMinus_sameSide_of_reachable hev hG v₀ hr

/--
[primalMinus_separates_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma primalMinus_separates_of_mem_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {u v : V}
-- given
  (hev : EvenOnCycles Gp δ)
  (hadj : Gp.Adj u v)
  (hmem : s(u, v) ∈ δ) :
-- imply
  ¬ (primalMinus Gp δ).Reachable u v := by
-- proof
  apply StatMech.Ising.primalMinus_separates_of_mem hev hadj hmem

/--
[parityConfig_isRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma parityConfig_isRegion_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {v₀ : V}
  {u v : V}
-- given
  (hev : EvenOnCycles Gp δ)
  (hG : Gp.Preconnected)
  (hadj : Gp.Adj u v) :
-- imply
  s(u, v) ∈ δ ↔ parityConfig Gp δ hG v₀ u ≠ parityConfig Gp δ hG v₀ v := by
-- proof
  apply StatMech.Ising.parityConfig_isRegion hev hG v₀ hadj

/--
[dcd_latticeMinusBarrier_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma dcd_latticeMinusBarrier_sameSide_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (latticeMinusBarrier S).Walk x y} :
-- imply
  (x ∈ S ↔ y ∈ S) := by
-- proof
  apply StatMech.Ising.dcd_latticeMinusBarrier_sameSide S w

/--
[dcd_not_reachable_latticeMinusBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma dcd_not_reachable_latticeMinusBarrier_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ¬ (latticeMinusBarrier S).Reachable x y := by
-- proof
  apply StatMech.Ising.dcd_not_reachable_latticeMinusBarrier S hx hy

/--
[dcd_windingRegion_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma dcd_windingRegion_separates_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : x ∈ jec_leftRegion Vc)
  (hy : y ∉ jec_leftRegion Vc) :
-- imply
  ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
-- proof
  apply StatMech.Ising.dcd_windingRegion_separates Vc hx hy

/--
[dcd_windingRegion_bdEdge_on_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma dcd_windingRegion_bdEdge_on_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Ising.dcd_windingRegion_bdEdge_on_support Vc hadj hbd

/--
[dcd_windingRegion_no_bdEdge_off_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma dcd_windingRegion_no_bdEdge_off_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ Vc.support)
  (hv : v ∉ Vc.support) :
-- imply
  ¬ bdEdge (jec_leftRegion Vc) s(u, v) := by
-- proof
  apply StatMech.Ising.dcd_windingRegion_no_bdEdge_off_support Vc hadj hu hv

/--
[dcd_boundsRegion_at_walk_of_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma dcd_boundsRegion_at_walk_of_bdEdge_eq
  {Gd : SimpleGraph (Site 2)}
  [DecidableRel Gd.Adj]
  {S : Set (Site 2)}
  {w : Site 2}
  {W : Gd.Walk w w}
-- given
  (hpull : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ bdEdge S s(u, v))) :
-- imply
  ∃ S' : Site 2 → Bool, ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ S' u ≠ S' v) := by
-- proof
  apply StatMech.Ising.dcd_boundsRegion_at_walk_of_bdEdge S W hpull

/--
[dcd_boundsRegion_of_leftRegionMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma dcd_boundsRegion_of_leftRegionMatch_eq
  {Gd : SimpleGraph (Site 2)}
  [DecidableRel Gd.Adj]
-- given
  (hmatch : ∀ {w : Site 2} (W : Gd.Walk w w), DualWalkLeftRegionMatch W) :
-- imply
  DualWalkBoundsRegion (hypercubicLattice 2) Gd crossEdge := by
-- proof
  apply StatMech.Ising.dcd_boundsRegion_of_leftRegionMatch hmatch

/--
[dcd_two_components_of_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma dcd_two_components_of_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {p q : Site 2}
-- given
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
  (hOutOff : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Ising.dcd_two_components_of_offSupport Vc hp hq hInOff hOutOff

/--
[dcd_leftRegionMatch_of_edgeless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualCutDuality.lean)
-/
@[path]
private lemma dcd_leftRegionMatch_of_edgeless_eq
  {Gd : SimpleGraph (Site 2)}
  [DecidableRel Gd.Adj]
  {w : Site 2}
  {W : Gd.Walk w w}
-- given
  (hGd : Gd.edgeSet = ∅) :
-- imply
  DualWalkLeftRegionMatch W := by
-- proof
  apply StatMech.Ising.dcd_leftRegionMatch_of_edgeless hGd W


-- created on 2026-10-23
