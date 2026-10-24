import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc66construct
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc66_ygConnector_connK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_ygConnector_connK_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {D : Finset ι}
  {y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hyg : y ≠ g)
  (hDsrc : sources ends D = ({y, g} : Finset W)) :
-- imply
  connK ends D y g := by
-- proof
  apply StatMech.Walls.gc66_ygConnector_connK ends hnd hyg hDsrc

/--
[gc66_strictly_smaller_of_removable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_strictly_smaller_of_removable_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {D : Finset ι}
  {y g : W}
  {i₀ : ι}
-- given
  (hyg : y ≠ g)
  (hi₀ : i₀ ∈ D)
  (hrem : connK ends (D \ {i₀}) y g) :
-- imply
  ∃ D', D' ⊆ D ∧ sources ends D' = ({y, g} : Finset W) ∧ #D' < #D := by
-- proof
  apply StatMech.Walls.gc66_strictly_smaller_of_removable ends hyg hi₀ hrem

/--
[gc66_choose_D](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_choose_D_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hrem : gc66_RemovableGEdge ends K y g) :
-- imply
  ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1 := by
-- proof
  apply StatMech.Walls.gc66_choose_D ends hnd K hoy hog hxy hxg hyg huniv hKsrc hrem

/--
[gc66_choose_D_of_ygEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_choose_D_of_ygEdge_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {y g : W}
  {i : ι}
-- given
  (hyg : y ≠ g)
  (hiV : i ∈ univ \ K)
  (hi : ends i = s(y, g)) :
-- imply
  ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1 := by
-- proof
  apply StatMech.Walls.gc66_choose_D_of_ygEdge ends hyg hiV hi

/--
[gc66_gDeg1Connector_of_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_gDeg1Connector_of_removalSurvival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hxg : x ≠ g)
  (h : gc66_GDeg1RemovalSurvival ends K o x y g) :
-- imply
  gc65_GDeg1Connector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc66_gDeg1Connector_of_removalSurvival ends hnd K hxg h

/--
[gc66_sharedSinkFixedD_of_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_sharedSinkFixedD_of_removalSurvival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (h : gc66_GDeg1RemovalSurvival ends K o x y g) :
-- imply
  gc64_SharedSinkFixedD ends K o x y g := by
-- proof
  apply StatMech.Walls.gc66_sharedSinkFixedD_of_removalSurvival ends K h

/--
[gc66_disjointConnector_of_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_disjointConnector_of_removalSurvival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hxg : x ≠ g)
  (h : gc66_GDeg1RemovalSurvival ends K o x y g) :
-- imply
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc66_disjointConnector_of_removalSurvival ends hnd K hxg h

/--
[gc66_countIneq_of_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_countIneq_of_removalSurvival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {o x y g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc66_GDeg1RemovalSurvival ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc66_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc66_removalSurvival_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_removalSurvival_of_disjoint_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {D : Finset ι}
-- given
  (hDV : D ⊆ univ \ K)
  (hDsrc : sources ends D = ({y, g} : Finset W))
  (hD1 : degK ends D g = 1)
  (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) :
-- imply
  gc66_GDeg1RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc66_removalSurvival_of_disjoint ends K hDV hDsrc hD1 hdisj

/--
[gc66_removalSurvival_of_gDeg1Witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_removalSurvival_of_gDeg1Witness_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {D : Finset ι}
-- given
  (hDV : D ⊆ univ \ K)
  (hDsrc : sources ends D = ({y, g} : Finset W))
  (hD1 : degK ends D g = 1)
  (hsurv : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g) :
-- imply
  gc66_GDeg1RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc66_removalSurvival_of_gDeg1Witness ends K hDV hDsrc hD1 hsurv

/--
[gc66_witness_surv_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_witness_surv_23_eq :
-- imply
  connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc66_witness_surv_23

/--
[gc66_witness_surv_24](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_witness_surv_24_eq :
-- imply
  connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc66_witness_surv_24

/--
[gc66_witness_surv_34](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_witness_surv_34_eq :
-- imply
  connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc66_witness_surv_34

/--
[gc66_witness_choose_D](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_witness_choose_D_eq :
-- imply
  ∃ D, D ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) ∧ sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) ∧ degK gc59_witnessEnds D 3 = 1 := by
-- proof
  apply StatMech.Walls.gc66_witness_choose_D

/--
[gc66_witness_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_witness_removalSurvival_eq :
-- imply
  gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc66_witness_removalSurvival

/--
[gc66_witness_removableGEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_witness_removableGEdge_eq :
-- imply
  gc66_RemovableGEdge gc59_witnessEnds ({0} : Finset (Fin 5)) 2 3 := by
-- proof
  apply StatMech.Walls.gc66_witness_removableGEdge

/--
[gc66_witness_choose_D_via_hyp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_witness_choose_D_via_hyp_eq :
-- imply
  ∃ D, D ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) ∧ sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) ∧ degK gc59_witnessEnds D 3 = 1 := by
-- proof
  apply StatMech.Walls.gc66_witness_choose_D_via_hyp

/--
[gc66_witness_gDeg1Connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_witness_gDeg1Connector_eq :
-- imply
  gc65_GDeg1Connector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc66_witness_gDeg1Connector

/--
[gc66_witness_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_witness_disjointConnector_eq :
-- imply
  gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc66_witness_disjointConnector

/--
[gc66_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean)
-/
@[path]
private lemma gc66_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W), x ≠ g → gc66_GDeg1RemovalSurvival ends K o x y g → gc65_GDeg1Connector ends K o x y g) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W), x ≠ g → gc66_GDeg1RemovalSurvival ends K o x y g → gc57_DisjointConnector ends K o x y g) ∧ (∃ D, D ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) ∧ sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) ∧ degK gc59_witnessEnds D 3 = 1) ∧ gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 ∧ gc65_GDeg1Connector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 ∧ gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc66_status


-- created on 2026-10-23
