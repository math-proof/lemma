import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
open Finset SimpleGraph StatMech StatMech.Universality StatMech.Universality.FKIsingMedialDart StatMech.Universality.FKIsingDobrushinMedialComplex


/--
[localMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma localMate_involutive_eq
  {P : PlanarZ2Subgraph}
  {omega : ConfigSpace (Sym2 P.V)} :
-- imply
  Function.Involutive (localMate omega) := by
-- proof
  apply StatMech.Universality.FKIsingMedialDart.localMate_involutive omega

/--
[localMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma localMate_ne_eq
  {P : PlanarZ2Subgraph}
  {omega : ConfigSpace (Sym2 P.V)}
  {d : FKIsingMedialDart P} :
-- imply
  localMate omega d ≠ d := by
-- proof
  apply StatMech.Universality.FKIsingMedialDart.localMate_ne omega d

/--
[localMate_edgeFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma localMate_edgeFlip_eq
  {P : PlanarZ2Subgraph}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P}
  {side : FKIsingMedialSide} :
-- imply
  localMate (FKIsingDobrushinDomain.localEdgeFlipEquiv e.1 omega) (e, side) = match omega e.1, side with := by
-- proof
  apply StatMech.Universality.FKIsingMedialDart.localMate_edgeFlip omega e side

/--
[localMate_edgeFlip_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma localMate_edgeFlip_of_ne_eq
  {P : PlanarZ2Subgraph}
  {omega : ConfigSpace (Sym2 P.V)}
  {e f : FKIsingMedialVertex P}
  {side : FKIsingMedialSide}
-- given
  (hef : f ≠ e) :
-- imply
  localMate (FKIsingDobrushinDomain.localEdgeFlipEquiv e.1 omega) (f, side) = localMate omega (f, side) := by
-- proof
  apply StatMech.Universality.FKIsingMedialDart.localMate_edgeFlip_of_ne omega e f hef side

/--
[winding_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma winding_west_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P} :
-- imply
  C.winding omega (e, .west) = C.baseWinding omega e := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.winding_west C omega e

/--
[winding_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma winding_east_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P} :
-- imply
  C.winding omega (e, .east) = C.winding omega (e, .west) + Real.pi := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.winding_east C omega e

/--
[winding_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma winding_south_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P} :
-- imply
  C.winding omega (e, .south) = C.winding omega (e, .west) - Real.pi / 2 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.winding_south C omega e

/--
[winding_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma winding_north_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P} :
-- imply
  C.winding omega (e, .north) = C.winding omega (e, .west) + Real.pi / 2 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.winding_north C omega e

/--
[loopGraph_neighborFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma loopGraph_neighborFinset_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {d : FKIsingMedialDart P} :
-- imply
  (C.loopGraph omega).neighborFinset d = {FKIsingMedialDart.localMate omega d, C.bondMate d} := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.loopGraph_neighborFinset C omega d

/--
[loopGraph_degree_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma loopGraph_degree_eq_two_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {d : FKIsingMedialDart P} :
-- imply
  (C.loopGraph omega).degree d = 2 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.loopGraph_degree_eq_two C omega d

/--
[mem_exploration_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma mem_exploration_iff_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {d : FKIsingMedialDart P} :
-- imply
  d ∈ C.exploration omega ↔ (C.loopGraph omega).Reachable C.sourceDart d := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.mem_exploration_iff C omega d

/--
[source_mem_exploration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma source_mem_exploration_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)} :
-- imply
  C.sourceDart ∈ C.exploration omega := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.source_mem_exploration C omega

/--
[localMate_mem_exploration_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma localMate_mem_exploration_iff_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {d : FKIsingMedialDart P} :
-- imply
  FKIsingMedialDart.localMate omega d ∈ C.exploration omega ↔ d ∈ C.exploration omega := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.localMate_mem_exploration_iff C omega d

/--
[closed_west_mem_iff_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma closed_west_mem_iff_south_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P} :
-- imply
  (e, .west) ∈ C.exploration (setClosed e.1 omega) ↔ (e, .south) ∈ C.exploration (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.closed_west_mem_iff_south C omega e

/--
[closed_east_mem_iff_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma closed_east_mem_iff_north_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P} :
-- imply
  (e, .east) ∈ C.exploration (setClosed e.1 omega) ↔ (e, .north) ∈ C.exploration (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.closed_east_mem_iff_north C omega e

/--
[open_west_mem_iff_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma open_west_mem_iff_north_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P} :
-- imply
  (e, .west) ∈ C.exploration (setOpen e.1 omega) ↔ (e, .north) ∈ C.exploration (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.open_west_mem_iff_north C omega e

/--
[open_east_mem_iff_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma open_east_mem_iff_south_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P} :
-- imply
  (e, .east) ∈ C.exploration (setOpen e.1 omega) ↔ (e, .south) ∈ C.exploration (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.open_east_mem_iff_south C omega e

/--
[loopGraph_setOpen_eq_twoEdgeSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma loopGraph_setOpen_eq_twoEdgeSwitch_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P} :
-- imply
  C.loopGraph (setOpen e.1 omega) = medialTwoEdgeSwitch (C.loopGraph (setClosed e.1 omega)) (e, .west) (e, .south) (e, .east) (e, .north) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.loopGraph_setOpen_eq_twoEdgeSwitch C omega e

/--
[open_local_mem_of_closed_west_mem_not_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma open_local_mem_of_closed_west_mem_not_east_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P}
-- given
  (hwest : (e, .west) ∈ C.exploration (setClosed e.1 omega))
  (heast : (e, .east) ∉ C.exploration (setClosed e.1 omega)) :
-- imply
  forall side, (e, side) ∈ C.exploration (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.open_local_mem_of_closed_west_mem_not_east C omega e hwest heast

/--
[open_local_mem_of_closed_east_mem_not_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma open_local_mem_of_closed_east_mem_not_west_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P}
-- given
  (heast : (e, .east) ∈ C.exploration (setClosed e.1 omega))
  (hwest : (e, .west) ∉ C.exploration (setClosed e.1 omega)) :
-- imply
  forall side, (e, side) ∈ C.exploration (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.open_local_mem_of_closed_east_mem_not_west C omega e heast hwest

/--
[open_local_not_mem_of_closed_west_east_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma open_local_not_mem_of_closed_west_east_not_mem_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P}
-- given
  (hwest : (e, .west) ∉ C.exploration (setClosed e.1 omega))
  (heast : (e, .east) ∉ C.exploration (setClosed e.1 omega)) :
-- imply
  forall side, (e, side) ∉ C.exploration (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.open_local_not_mem_of_closed_west_east_not_mem C omega e hwest heast

/--
[local_switch_membership_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean)
-/
@[path]
private lemma local_switch_membership_classification_eq
  {P : PlanarZ2Subgraph}
  {C : FKIsingDobrushinMedialComplex P}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : FKIsingMedialVertex P} :
-- imply
  ((e, .west) ∉ C.exploration (setClosed e.1 omega) ∧ (e, .east) ∉ C.exploration (setClosed e.1 omega) ∧ forall side, (e, side) ∉ C.exploration (setOpen e.1 omega)) ∨ ((e, .west) ∈ C.exploration (setClosed e.1 omega) ∧ (e, .east) ∉ C.exploration (setClosed e.1 omega) ∧ forall side, (e, side) ∈ C.exploration (setOpen e.1 omega)) ∨ ((e, .west) ∉ C.exploration (setClosed e.1 omega) ∧ (e, .east) ∈ C.exploration (setClosed e.1 omega) ∧ forall side, (e, side) ∈ C.exploration (setOpen e.1 omega)) ∨ ((e, .west) ∈ C.exploration (setClosed e.1 omega) ∧ (e, .east) ∈ C.exploration (setClosed e.1 omega)) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinMedialComplex.local_switch_membership_classification C omega e


-- created on 2026-10-23
