import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
open SimpleGraph Function StatMech StatMech.Lattice


/--
[complAdj_of_unitDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceOrbit.lean)
-/
@[path]
private lemma complAdj_of_unitDiff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {u v : Site 2}
-- given
  (hu : u ∉ K)
  (hv : v ∉ K)
  (hd : unitWt (u - v) = 1) :
-- imply
  ((hypercubicLattice 2).induce Kᶜ).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Lattice.complAdj_of_unitDiff K hu hv hd

/--
[complReachable_of_unitDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceOrbit.lean)
-/
@[path]
private lemma complReachable_of_unitDiff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {u v : Site 2}
-- given
  (hu : u ∉ K)
  (hv : v ∉ K)
  (hd : unitWt (u - v) = 1) :
-- imply
  ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Lattice.complReachable_of_unitDiff K hu hv hd

/--
[complReachable_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceOrbit.lean)
-/
@[path]
private lemma complReachable_congr_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {G : SimpleGraph V}
  {S : Set V}
  {a b a' b' : ↥S}
-- given
  (ha : (a : V) = (a' : V))
  (hb : (b : V) = (b' : V))
  (h : (G.induce S).Reachable a b) :
-- imply
  (G.induce S).Reachable a' b' := by
-- proof
  apply StatMech.Lattice.complReachable_congr ha hb h

/--
[boundaryDart_head_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceOrbit.lean)
-/
@[path]
private lemma boundaryDart_head_not_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  e.head ∉ K := by
-- proof
  apply StatMech.Lattice.boundaryDart_head_not_mem K e he

/--
[dartNext_head_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceOrbit.lean)
-/
@[path]
private lemma dartNext_head_not_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  (dartNext K e).head ∉ K := by
-- proof
  apply StatMech.Lattice.dartNext_head_not_mem K e he

/--
[dartNext_head_sameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceOrbit.lean)
-/
@[path]
private lemma dartNext_head_sameComponent_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨(dartNext K e).head, dartNext_head_not_mem K e he⟩ := by
-- proof
  apply StatMech.Lattice.dartNext_head_sameComponent K e he

/--
[iterate_isBoundaryDart'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceOrbit.lean)
-/
@[path]
private lemma iterate_isBoundaryDart'_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  IsBoundaryDart K ((dartNext K)^[n] e) := by
-- proof
  apply StatMech.Lattice.iterate_isBoundaryDart' K e he n

/--
[dartNext_iterate_head_sameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceOrbit.lean)
-/
@[path]
private lemma dartNext_iterate_head_sameComponent_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨((dartNext K)^[n] e).head, (iterate_isBoundaryDart' K e he n).2⟩ := by
-- proof
  apply StatMech.Lattice.dartNext_iterate_head_sameComponent K e he n

/--
[dartNext_orbit_head_sameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceOrbit.lean)
-/
@[path]
private lemma dartNext_orbit_head_sameComponent_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e f : Dart}
  {n : ℕ}
-- given
  (he : IsBoundaryDart K e)
  (hf : IsBoundaryDart K f)
  (heq : (dartNext K)^[n] e = f) :
-- imply
  ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
-- proof
  apply StatMech.Lattice.dartNext_orbit_head_sameComponent K e f he hf heq

/--
[head_compl_of_exitDartsSameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceOrbit.lean)
-/
@[path]
private lemma head_compl_of_exitDartsSameOrbit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : ExitDartsSameOrbit ω hfin) :
-- imply
  ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable ⟨(exitDart (ω := ω) hfin).head, (exitDart_isBoundaryDart (ω := ω) hfin).2⟩ ⟨(leftExitDart (ω := ω) hfin).head, (leftExitDart_isBoundaryDart (ω := ω) hfin).2⟩ := by
-- proof
  apply StatMech.Lattice.head_compl_of_exitDartsSameOrbit hfin h

/--
[exitDartsSameOrbit_of_interfaceConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceOrbit.lean)
-/
@[path]
private lemma exitDartsSameOrbit_of_interfaceConnected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
  (hcomp : ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable ⟨(exitDart (ω := ω) hfin).head, (exitDart_isBoundaryDart (ω := ω) hfin).2⟩ ⟨(leftExitDart (ω := ω) hfin).head, (leftExitDart_isBoundaryDart (ω := ω) hfin).2⟩) :
-- imply
  ExitDartsSameOrbit ω hfin := by
-- proof
  apply StatMech.Lattice.exitDartsSameOrbit_of_interfaceConnected hfin hInt hcomp


-- created on 2026-10-23
