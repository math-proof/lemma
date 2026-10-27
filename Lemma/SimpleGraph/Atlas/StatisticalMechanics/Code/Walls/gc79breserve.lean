import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc79breserve.Part2
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc79b_reservedGEdge_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_reservedGEdge_exists_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {D : Finset ι}
  {g : W}
-- given
  (hD1 : degK ends D g = 1) :
-- imply
  ∃ eY, gc79b_gEdges ends D g = {eY} ∧ eY ∈ D ∧ g ∈ ends eY := by
-- proof
  apply StatMech.Walls.gc79b_reservedGEdge_exists ends hD1

/--
[gc79b_leaf_of_reservedSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_leaf_of_reservedSurvival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {D : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g)
  (hDV : D ⊆ univ \ K)
  (hDsrc : sources ends D = ({y, g} : Finset W))
  (hD1 : degK ends D g = 1)
  (hsurv : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g := by
-- proof
  apply StatMech.Walls.gc79b_leaf_of_reservedSurvival ends hnd K hog hDV hDsrc hD1 hsurv

/--
[gc79b_leaf_of_reservedSurvival_xg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_leaf_of_reservedSurvival_xg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {D : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hog : o ≠ g)
  (hKsrc : sources ends K = ({o, x} : Finset W))
  (hDV : D ⊆ univ \ K)
  (hDsrc : sources ends D = ({y, g} : Finset W))
  (hD1 : degK ends D g = 1)
  (hsurv : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g := by
-- proof
  apply StatMech.Walls.gc79b_leaf_of_reservedSurvival_xg ends hnd K hox hog hKsrc hDV hDsrc hD1 hsurv

/--
[gc79b_pathEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_pathEnds_loopless_eq :
-- imply
  ∀ i : Fin 2, ¬ (gc79b_pathEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc79b_pathEnds_loopless

/--
[gc79b_pathEnds_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_pathEnds_boundary_eq :
-- imply
  sources gc79b_pathEnds (univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 3)) := by
-- proof
  apply StatMech.Walls.gc79b_pathEnds_boundary

/--
[gc79b_pathEnds_og](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_pathEnds_og_eq :
-- imply
  connK gc79b_pathEnds (univ : Finset (Fin 2)) 0 2 := by
-- proof
  apply StatMech.Walls.gc79b_pathEnds_og

/--
[gc79b_pathEnds_xg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_pathEnds_xg_eq :
-- imply
  connK gc79b_pathEnds (univ : Finset (Fin 2)) 1 2 := by
-- proof
  apply StatMech.Walls.gc79b_pathEnds_xg

/--
[gc79b_path_removeGEdge_cuts_o](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_path_removeGEdge_cuts_o_eq :
-- imply
  ¬ connK gc79b_pathEnds ((univ : Finset (Fin 2)) \ ({0} : Finset (Fin 2))) 0 2 := by
-- proof
  apply StatMech.Walls.gc79b_path_removeGEdge_cuts_o

/--
[gc79b_single_gEdge_survival_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_single_gEdge_survival_false_eq :
-- imply
  sources gc79b_pathEnds (univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 3)) ∧ connK gc79b_pathEnds (univ : Finset (Fin 2)) 0 2 ∧ connK gc79b_pathEnds (univ : Finset (Fin 2)) 1 2 ∧ (¬ connK gc79b_pathEnds ((univ : Finset (Fin 2)) \ ({0} : Finset (Fin 2))) 0 2) := by
-- proof
  apply StatMech.Walls.gc79b_single_gEdge_survival_false

/--
[gc79b_xEnds_workingD_reserved](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_workingD_reserved_eq :
-- imply
  gc79b_gEdges gc78b_xEnds ({5, 6} : Finset (Fin 7)) 3 = ({6} : Finset (Fin 7)) ∧ (6 : Fin 7) ∈ ({5, 6} : Finset (Fin 7)) ∧ (3 : Fin 5) ∈ gc78b_xEnds 6 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_workingD_reserved

/--
[gc79b_xEnds_gate_34](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_gate_34_eq :
-- imply
  connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({3, 4} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_gate_34

/--
[gc79b_xEnds_gate_0134](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_gate_0134_eq :
-- imply
  connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({0, 1, 3, 4} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_gate_0134

/--
[gc79b_xEnds_gate_0356](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_gate_0356_eq :
-- imply
  connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_gate_0356

/--
[gc79b_xEnds_gate_0456](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_gate_0456_eq :
-- imply
  connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({0, 4, 5, 6} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_gate_0456

/--
[gc79b_xEnds_gate_1356](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_gate_1356_eq :
-- imply
  connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({1, 3, 5, 6} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_gate_1356

/--
[gc79b_xEnds_gate_1456](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_gate_1456_eq :
-- imply
  connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_gate_1456

/--
[gc79b_xEnds_gate_fail_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_gate_fail_empty_eq :
-- imply
  ¬ connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ (∅ : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_gate_fail_empty

/--
[gc79b_xEnds_gate_fail_01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_gate_fail_01_eq :
-- imply
  ¬ connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({0, 1} : Finset (Fin 7))) 1 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_gate_fail_01

/--
[gc79b_xEnds_sourceEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_sourceEmpty_eq :
-- imply
  ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)).powerset.filter (fun L => sources gc78b_xEnds L = (∅ : Finset (Fin 5))) = ({∅, {0, 1}, {3, 4}, {0, 1, 3, 4}, {0, 3, 5, 6}, {0, 4, 5, 6}, {1, 3, 5, 6}, {1, 4, 5, 6}} : Finset (Finset (Fin 7))) := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_sourceEmpty

/--
[gc79b_xEnds_LblockSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_LblockSet_eq :
-- imply
  gc51_LblockSet gc78b_xEnds ({2} : Finset (Fin 7)) 0 1 3 = ({({3, 4} : Finset (Fin 7)), ({0, 1, 3, 4} : Finset (Fin 7)), ({0, 3, 5, 6} : Finset (Fin 7)), ({0, 4, 5, 6} : Finset (Fin 7)), ({1, 3, 5, 6} : Finset (Fin 7)), ({1, 4, 5, 6} : Finset (Fin 7))} : Finset (Finset (Fin 7))) := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_LblockSet

/--
[gc79b_xEnds_D_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_D_data_eq :
-- imply
  ({5, 6} : Finset (Fin 7)) ⊆ (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7)) ∧ sources gc78b_xEnds ({5, 6} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) ∧ degK gc78b_xEnds ({5, 6} : Finset (Fin 7)) 3 = 1 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_D_data

/--
[gc79b_xEnds_surv_34](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_surv_34_eq :
-- imply
  connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({3, 4} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_surv_34

/--
[gc79b_xEnds_surv_0134](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_surv_0134_eq :
-- imply
  connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 1, 3, 4} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_surv_0134

/--
[gc79b_xEnds_surv_0356](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_surv_0356_eq :
-- imply
  connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_surv_0356

/--
[gc79b_xEnds_surv_0456](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_surv_0456_eq :
-- imply
  connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 4, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_surv_0456

/--
[gc79b_xEnds_surv_1356](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_surv_1356_eq :
-- imply
  connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({1, 3, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_surv_1356

/--
[gc79b_xEnds_surv_1456](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_surv_1456_eq :
-- imply
  connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_surv_1456

/--
[gc79b_xEnds_workingD_survives_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_workingD_survives_all_eq :
-- imply
  ∀ L ∈ gc51_LblockSet gc78b_xEnds ({2} : Finset (Fin 7)) 0 1 3, connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ L) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_workingD_survives_all

/--
[gc79b_xEnds_twoCommodityLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_twoCommodityLeaf_eq :
-- imply
  gc71_TwoCommodityLeaf gc78b_xEnds ({2} : Finset (Fin 7)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_twoCommodityLeaf

/--
[gc79b_xEnds_minCard_03_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_minCard_03_fails_eq :
-- imply
  ¬ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))) 0 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_minCard_03_fails

/--
[gc79b_xEnds_minCard_14_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_minCard_14_fails_eq :
-- imply
  ¬ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) \ ({1, 4} : Finset (Fin 7))) 0 3 := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_minCard_14_fails

/--
[gc79b_xEnds_Luniformity_verdict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_xEnds_Luniformity_verdict_eq :
-- imply
  (∀ L ∈ gc51_LblockSet gc78b_xEnds ({2} : Finset (Fin 7)) 0 1 3, connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ L) \ ({5, 6} : Finset (Fin 7))) 0 3) ∧ (¬ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))) 0 3) ∧ (¬ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) \ ({1, 4} : Finset (Fin 7))) 0 3) := by
-- proof
  apply StatMech.Walls.gc79b_xEnds_Luniformity_verdict

/--
[gc79b_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean)
-/
@[path]
private lemma gc79b_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W) (D : Finset ι), o ≠ g → D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) → degK ends D g = 1 → (∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) → gc71_TwoCommodityLeaf ends K o x y g) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (D : Finset ι) (g : W), degK ends D g = 1 → ∃ eY, gc79b_gEdges ends D g = {eY} ∧ eY ∈ D ∧ g ∈ ends eY) ∧ (sources gc79b_pathEnds (univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 3)) ∧ connK gc79b_pathEnds (univ : Finset (Fin 2)) 0 2 ∧ connK gc79b_pathEnds (univ : Finset (Fin 2)) 1 2 ∧ (¬ connK gc79b_pathEnds ((univ : Finset (Fin 2)) \ ({0} : Finset (Fin 2))) 0 2)) ∧ gc71_TwoCommodityLeaf gc78b_xEnds ({2} : Finset (Fin 7)) 0 1 2 3 ∧ ((¬ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))) 0 3) ∧ (¬ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) \ ({1, 4} : Finset (Fin 7))) 0 3)) := by
-- proof
  apply StatMech.Walls.gc79b_status


-- created on 2026-10-23
