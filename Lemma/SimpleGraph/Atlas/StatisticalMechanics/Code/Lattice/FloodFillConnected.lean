import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.FloodFillConnected
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[ffc_offSupportLattice_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_offSupportLattice_adj_eq
  {B : Set (Site 2)}
  {x y : Site 2} :
-- imply
  (ffc_offSupportLattice B).Adj x y ↔ (hypercubicLattice 2).Adj x y ∧ x ∉ B ∧ y ∉ B := by
-- proof
  apply StatMech.Lattice.ffc_offSupportLattice_adj B x y

/--
[ffc_offSupportLattice_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_offSupportLattice_le_eq
  {B : Set (Site 2)} :
-- imply
  ffc_offSupportLattice B ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.ffc_offSupportLattice_le B

/--
[ffc_offSupportWalk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_offSupportWalk_support_eq
  {B : Set (Site 2)}
  {x y : Site 2}
  {w : (ffc_offSupportLattice B).Walk x y}
-- given
  (hx : x ∉ B) :
-- imply
  ∀ z ∈ w.support, z ∉ B := by
-- proof
  apply StatMech.Lattice.ffc_offSupportWalk_support w hx

/--
[ffc_project_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_project_walk_eq
  {B : Set (Site 2)}
  {x y : Site 2}
  {w : (ffc_offSupportLattice B).Walk x y}
-- given
  (hx : x ∉ B) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk x y, (∀ z ∈ p.support, z ∉ B) ∧ p.support = w.support := by
-- proof
  apply StatMech.Lattice.ffc_project_walk w hx

/--
[ffc_reachable_iff_offSupportWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_reachable_iff_offSupportWalk_eq
  {B : Set (Site 2)}
  {x y : Site 2}
-- given
  (hx : x ∉ B) :
-- imply
  (ffc_offSupportLattice B).Reachable x y ↔ ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B := by
-- proof
  apply StatMech.Lattice.ffc_reachable_iff_offSupportWalk hx

/--
[ffc_mem_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_mem_floodFill_eq
  {B : Set (Site 2)}
  {seed z : Site 2} :
-- imply
  z ∈ ffc_floodFill B seed ↔ (ffc_offSupportLattice B).Reachable seed z := by
-- proof
  apply StatMech.Lattice.ffc_mem_floodFill

/--
[ffc_seed_mem_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_seed_mem_floodFill_eq
  {B : Set (Site 2)}
  {seed : Site 2} :
-- imply
  seed ∈ ffc_floodFill B seed := by
-- proof
  apply StatMech.Lattice.ffc_seed_mem_floodFill B seed

/--
[ffc_floodFill_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_floodFill_offSupport_eq
  {B : Set (Site 2)}
  {seed : Site 2}
  {z : Site 2}
-- given
  (hseed : seed ∉ B)
  (hz : z ∈ ffc_floodFill B seed) :
-- imply
  z ∉ B := by
-- proof
  apply StatMech.Lattice.ffc_floodFill_offSupport hseed hz

/--
[ffc_floodFill_reachable_offSupportLattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_floodFill_reachable_offSupportLattice_eq
  {B : Set (Site 2)}
  {seed : Site 2}
  {x y : Site 2}
-- given
  (hx : x ∈ ffc_floodFill B seed)
  (hy : y ∈ ffc_floodFill B seed) :
-- imply
  (ffc_offSupportLattice B).Reachable x y := by
-- proof
  apply StatMech.Lattice.ffc_floodFill_reachable_offSupportLattice hx hy

/--
[ffc_floodFill_path_connected_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_floodFill_path_connected_offSupport_eq
  {B : Set (Site 2)}
  {seed : Site 2}
  {x y : Site 2}
-- given
  (hseed : seed ∉ B)
  (hx : x ∈ ffc_floodFill B seed)
  (hy : y ∈ ffc_floodFill B seed) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B := by
-- proof
  apply StatMech.Lattice.ffc_floodFill_path_connected_offSupport hseed hx hy

/--
[ffc_floodFill_self_offSupport_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_floodFill_self_offSupport_walk_eq
  {B : Set (Site 2)}
  {seed : Site 2}
  {z : Site 2}
-- given
  (hseed : seed ∉ B)
  (hz : z ∈ ffc_floodFill B seed) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk seed z, ∀ w ∈ p.support, w ∉ B := by
-- proof
  apply StatMech.Lattice.ffc_floodFill_self_offSupport_walk hseed hz

/--
[ffc_floodFill_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_floodFill_step_eq
  {B : Set (Site 2)}
  {seed z w : Site 2}
-- given
  (hz : z ∈ ffc_floodFill B seed)
  (hadj : (hypercubicLattice 2).Adj z w)
  (hzB : z ∉ B)
  (hwB : w ∉ B) :
-- imply
  w ∈ ffc_floodFill B seed := by
-- proof
  apply StatMech.Lattice.ffc_floodFill_step hz hadj hzB hwB

/--
[ffc_engine_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_engine_nonvacuous_eq :
-- imply
  ∃ p : (hypercubicLattice 2).Walk (![0, 0] : Site 2) ![1, 0], ∀ z ∈ p.support, z ∉ ({z | z = (![5, 5] : Site 2)} : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.ffc_engine_nonvacuous

/--
[ffc_floodFill_reachable_in_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_floodFill_reachable_in_barrier_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {x y : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hx : x ∈ ffc_floodFill {z | z ∈ Vc.support} seed)
  (hy : y ∈ ffc_floodFill {z | z ∈ Vc.support} seed) :
-- imply
  (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
-- proof
  apply StatMech.Lattice.ffc_floodFill_reachable_in_barrier Vc hseed hx hy

/--
[ffc_side_reachable_of_eq_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_side_reachable_of_eq_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {T : Set (Site 2)}
  {x y : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hT : T = ffc_floodFill {z | z ∈ Vc.support} seed)
  (hx : x ∈ T)
  (hy : y ∈ T) :
-- imply
  (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
-- proof
  apply StatMech.Lattice.ffc_side_reachable_of_eq_floodFill Vc hseed hT hx hy

/--
[ffc_floodFill_inside_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_floodFill_inside_connected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {x y : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hInside : jec_leftRegion Vc = ffc_floodFill {z | z ∈ Vc.support} seed)
  (hx : x ∈ jec_leftRegion Vc)
  (hy : y ∈ jec_leftRegion Vc) :
-- imply
  (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
-- proof
  apply StatMech.Lattice.ffc_floodFill_inside_connected Vc hseed hInside hx hy

/--
[ffc_floodFill_outside_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_floodFill_outside_connected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {x y : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hOutside : (jec_leftRegion Vc)ᶜ = ffc_floodFill {z | z ∈ Vc.support} seed)
  (hx : x ∉ jec_leftRegion Vc)
  (hy : y ∉ jec_leftRegion Vc) :
-- imply
  (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
-- proof
  apply StatMech.Lattice.ffc_floodFill_outside_connected Vc hseed hOutside hx hy

/--
[ffc_hInOff_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_hInOff_of_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hInside : jec_leftRegion Vc = ffc_floodFill {z | z ∈ Vc.support} seed) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.ffc_hInOff_of_floodFill Vc hseed hInside

/--
[ffc_hOutOff_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_hOutOff_of_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hOutside : (jec_leftRegion Vc)ᶜ = ffc_floodFill {z | z ∈ Vc.support} seed) :
-- imply
  ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.ffc_hOutOff_of_floodFill Vc hseed hOutside

/--
[ffc_two_components_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_two_components_of_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {p q : Site 2}
  {sIn sOut : Site 2}
-- given
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hsIn : sIn ∉ Vc.support)
  (hsOut : sOut ∉ Vc.support)
  (hInside : jec_leftRegion Vc = ffc_floodFill {z | z ∈ Vc.support} sIn)
  (hOutside : (jec_leftRegion Vc)ᶜ = ffc_floodFill {z | z ∈ Vc.support} sOut) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.ffc_two_components_of_floodFill Vc hp hq hsIn hsOut hInside hOutside

/--
[ffc_egf_LoopFloodFill_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_egf_LoopFloodFill_of_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {xIn yOut : Site 2}
  {sIn sOut : Site 2}
-- given
  (hxIn : xIn ∈ jec_leftRegion Vc)
  (hyOut : yOut ∉ jec_leftRegion Vc)
  (hsIn : sIn ∉ Vc.support)
  (hsOut : sOut ∉ Vc.support)
  (hInside : jec_leftRegion Vc = ffc_floodFill {z | z ∈ Vc.support} sIn)
  (hOutside : (jec_leftRegion Vc)ᶜ = ffc_floodFill {z | z ∈ Vc.support} sOut) :
-- imply
  egf_LoopFloodFill Vc := by
-- proof
  apply StatMech.Lattice.ffc_egf_LoopFloodFill_of_floodFill Vc hxIn hyOut hsIn hsOut hInside hOutside

/--
[ffc_egf_loop_two_components_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean)
-/
@[path]
private lemma ffc_egf_loop_two_components_of_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {xIn yOut : Site 2}
  {sIn sOut : Site 2}
-- given
  (hxIn : xIn ∈ jec_leftRegion Vc)
  (hyOut : yOut ∉ jec_leftRegion Vc)
  (hsIn : sIn ∉ Vc.support)
  (hsOut : sOut ∉ Vc.support)
  (hInside : jec_leftRegion Vc = ffc_floodFill {z | z ∈ Vc.support} sIn)
  (hOutside : (jec_leftRegion Vc)ᶜ = ffc_floodFill {z | z ∈ Vc.support} sOut) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.ffc_egf_loop_two_components_of_floodFill Vc hxIn hyOut hsIn hsOut hInside hOutside


-- created on 2026-10-23
