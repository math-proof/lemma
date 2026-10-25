import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEssentialClusterBoundary.Part2
open SimpleGraph StatMech StatMech.FrontierD


/--
[mem_fkRectClusterBoundaryDarts_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEssentialClusterBoundary.lean)
-/
@[path]
private lemma mem_fkRectClusterBoundaryDarts_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {d : FKMedialDart R.medialTorus} :
-- imply
  d ∈ fkRectClusterBoundaryDarts R omega x ↔ (fkRectOpenGraph R omega).Reachable x (fkRectMedialDartPrimalLabel R d) := by
-- proof
  apply StatMech.FrontierD.mem_fkRectClusterBoundaryDarts_iff R omega x d

/--
[fkRectClusterBoundaryDarts_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEssentialClusterBoundary.lean)
-/
@[path]
private lemma fkRectClusterBoundaryDarts_nonempty_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex} :
-- imply
  (fkRectClusterBoundaryDarts R omega x).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectClusterBoundaryDarts_nonempty R omega x

/--
[fkRectClusterBoundaryDarts_boundaryStep_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEssentialClusterBoundary.lean)
-/
@[path]
private lemma fkRectClusterBoundaryDarts_boundaryStep_mem_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {d : FKMedialDart R.medialTorus}
-- given
  (hd : d ∈ fkRectClusterBoundaryDarts R omega x) :
-- imply
  fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega) d ∈ fkRectClusterBoundaryDarts R omega x := by
-- proof
  apply StatMech.FrontierD.fkRectClusterBoundaryDarts_boundaryStep_mem R omega x hd

/--
[fkRectClusterBoundaryPerm_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEssentialClusterBoundary.lean)
-/
@[path]
private lemma fkRectClusterBoundaryPerm_val_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
-- given
  (d : {d : FKMedialDart R.medialTorus // d ∈ fkRectClusterBoundaryDarts R omega x}) :
-- imply
  (fkRectClusterBoundaryPerm R omega x d).1 = fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega) d.1 := by
-- proof
  apply StatMech.FrontierD.fkRectClusterBoundaryPerm_val R omega x d

/--
[fkRectClusterBoundaryDarts_iterate_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEssentialClusterBoundary.lean)
-/
@[path]
private lemma fkRectClusterBoundaryDarts_iterate_mem_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {d : FKMedialDart R.medialTorus}
-- given
  (hd : d ∈ fkRectClusterBoundaryDarts R omega x) :
-- imply
  ∀ n : Nat, (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega))^[n] d ∈ fkRectClusterBoundaryDarts R omega x := by
-- proof
  apply StatMech.FrontierD.fkRectClusterBoundaryDarts_iterate_mem R omega x hd

/--
[fkRectWindingIndependent_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEssentialClusterBoundary.lean)
-/
@[path]
private lemma fkRectWindingIndependent_comm_eq
  {u v : Int × Int} :
-- imply
  FKRectWindingIndependent u v ↔ FKRectWindingIndependent v u := by
-- proof
  apply StatMech.FrontierD.fkRectWindingIndependent_comm u v

/--
[fkRect_boundaryOrbit_winding_dependent_of_not_hasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEssentialClusterBoundary.lean)
-/
@[path]
private lemma fkRect_boundaryOrbit_winding_dependent_of_not_hasNet_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {q : (fkRectOpenGraph R omega).Walk x x}
  {d : FKMedialDart R.medialTorus}
-- given
  (hold : ¬ FKRectHasNet R omega)
  (hxd : (fkRectOpenGraph R omega).Reachable x (fkRectMedialDartPrimalLabel R d)) :
-- imply
  ¬ FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d)) (fkRectWalkWinding R q) := by
-- proof
  apply StatMech.FrontierD.fkRect_boundaryOrbit_winding_dependent_of_not_hasNet R omega x q hold d hxd


-- created on 2026-10-23
