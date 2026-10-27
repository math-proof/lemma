import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc56pathremoval.Part3
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc56_multiRemove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_multiRemove_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {G : Finset ι}
  {E : Finset ι}
  {x g : W}
-- given
  (hrec : ∀ i ∈ E, ∀ p q : W, ends i = s(p, q) → connK ends (G \ E) p q)
  (hx : connK ends G x g) :
-- imply
  connK ends (G \ E) x g := by
-- proof
  apply StatMech.Walls.gc56_multiRemove ends G E hrec hx

/--
[gc56_graph_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_graph_restrict_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {K L D : Finset ι}
-- given
  (hKD : Disjoint K D) :
-- imply
  (K ∪ L) \ (L ∩ D) = K ∪ (L \ D) := by
-- proof
  apply StatMech.Walls.gc56_graph_restrict K L D hKD

/--
[gc56_removalSurvival_of_pathReconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_removalSurvival_of_pathReconnect_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (h : gc56_PathReconnect ends K o x y g) :
-- imply
  gc55_RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc56_removalSurvival_of_pathReconnect ends K h

/--
[gc56_pathReconnect_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_pathReconnect_of_disjoint_eq
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
  (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) :
-- imply
  gc56_PathReconnect ends K o x y g := by
-- proof
  apply StatMech.Walls.gc56_pathReconnect_of_disjoint ends K hDV hDsrc hdisj

/--
[gc56_pathReconnect_of_ygEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_pathReconnect_of_ygEdge_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {i : ι}
-- given
  (hnd : ∀ j : ι, ¬ (ends j).IsDiag)
  (hyg : y ≠ g)
  (hiV : i ∈ univ \ K)
  (hi : ends i = s(y, g)) :
-- imply
  gc56_PathReconnect ends K o x y g := by
-- proof
  apply StatMech.Walls.gc56_pathReconnect_of_ygEdge ends hnd K hyg hiV hi

/--
[gc56_countIneq_of_pathReconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_countIneq_of_pathReconnect_eq
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
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc56_PathReconnect ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc56_countIneq_of_pathReconnect ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc56_witness_pathReconnect_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_witness_pathReconnect_K13_eq :
-- imply
  gc56_PathReconnect gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc56_witness_pathReconnect_K13

/--
[gc56_witness_pathReconnect_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_witness_pathReconnect_K23_eq :
-- imply
  gc56_PathReconnect gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc56_witness_pathReconnect_K23

/--
[gc56_witness_cosetGateDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_witness_cosetGateDom_eq :
-- imply
  gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc56_witness_cosetGateDom

/--
[gc56_witness_perKCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_witness_perKCount_eq :
-- imply
  gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc56_witness_perKCount

/--
[gc56_refEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_refEnds_univ_sources_eq :
-- imply
  sources gc56_refEnds (univ : Finset (Fin 7)) = ({0, 1, 2, 3} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc56_refEnds_univ_sources

/--
[gc56_refEnds_K_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_refEnds_K_sources_eq :
-- imply
  sources gc56_refEnds ({2} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc56_refEnds_K_sources

/--
[gc56_ref_base_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_ref_base_eq_eq :
-- imply
  (({2} : Finset (Fin 7)) ∪ (({0, 1, 4, 5} : Finset (Fin 7)) \ ({1, 4} : Finset (Fin 7)))) = ({0, 2, 5} : Finset (Fin 7)) := by
-- proof
  apply StatMech.Walls.gc56_ref_base_eq

/--
[gc56_ref_removalSurvives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_ref_removalSurvives_eq :
-- imply
  connK gc56_refEnds ({0, 2, 5} : Finset (Fin 7)) 1 3 := by
-- proof
  apply StatMech.Walls.gc56_ref_removalSurvives

/--
[gc56_ref_noReconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_ref_noReconnect_eq :
-- imply
  ¬ connK gc56_refEnds ({0, 2, 5} : Finset (Fin 7)) 2 4 := by
-- proof
  apply StatMech.Walls.gc56_ref_noReconnect

/--
[gc56_pathReconnect_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_pathReconnect_refuted_eq :
-- imply
  sources gc56_refEnds ({2} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5)) ∧ (1 : Fin 7) ∈ ({0, 1, 4, 5} : Finset (Fin 7)) ∩ ({1, 4} : Finset (Fin 7)) ∧ gc56_refEnds 1 = s(2, 4) ∧ connK gc56_refEnds (({2} : Finset (Fin 7)) ∪ (({0, 1, 4, 5} : Finset (Fin 7)) \ ({1, 4} : Finset (Fin 7)))) 1 3 ∧ ¬ connK gc56_refEnds (({2} : Finset (Fin 7)) ∪ (({0, 1, 4, 5} : Finset (Fin 7)) \ ({1, 4} : Finset (Fin 7)))) 2 4 := by
-- proof
  apply StatMech.Walls.gc56_pathReconnect_refuted

/--
[gc56_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc56pathremoval.lean)
-/
@[path]
private lemma gc56_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W), gc56_PathReconnect ends K o x y g → gc55_RemovalSurvival ends K o x y g) ∧ (¬ connK gc56_refEnds (({2} : Finset (Fin 7)) ∪ (({0, 1, 4, 5} : Finset (Fin 7)) \ ({1, 4} : Finset (Fin 7)))) 2 4) ∧ gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 ∧ gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc56_status


-- created on 2026-10-23
