import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc57menger.Part3
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc57_graph_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_graph_sdiff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {K L D : Finset ι}
-- given
  (hKD : Disjoint K D) :
-- imply
  (K ∪ L) \ D = K ∪ (L \ D) := by
-- proof
  apply StatMech.Walls.gc57_graph_sdiff K L D hKD

/--
[gc57_connK_of_disjoint_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_connK_of_disjoint_connector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {P G D : Finset ι}
  {a b : W}
-- given
  (hPG : P ⊆ G)
  (hPD : Disjoint P D)
  (hab : connK ends P a b) :
-- imply
  connK ends (G \ D) a b := by
-- proof
  apply StatMech.Walls.gc57_connK_of_disjoint_connector ends hPG hPD hab

/--
[gc57_removalSurvival_of_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_removalSurvival_of_disjointConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
-- given
  (h : gc57_DisjointConnector ends K o x y g) :
-- imply
  gc55_RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc57_removalSurvival_of_disjointConnector ends K h

/--
[gc57_disjointConnector_of_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_disjointConnector_of_removalSurvival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {L D : Finset ι}
  {x g : W}
-- given
  (hKD : Disjoint K D)
  (hrs : connK ends (K ∪ (L \ D)) x g) :
-- imply
  ∃ P, P ⊆ K ∪ L ∧ Disjoint P D ∧ connK ends P x g := by
-- proof
  apply StatMech.Walls.gc57_disjointConnector_of_removalSurvival ends K hKD hrs

/--
[gc57_disjointConnector_iff_removalSurvival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_disjointConnector_iff_removalSurvival_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {L D : Finset ι}
  {x g : W}
-- given
  (hKD : Disjoint K D) :
-- imply
  (∃ P, P ⊆ K ∪ L ∧ Disjoint P D ∧ connK ends P x g) ↔ connK ends (K ∪ (L \ D)) x g := by
-- proof
  apply StatMech.Walls.gc57_disjointConnector_iff_removalSurvival ends K hKD

/--
[gc57_disjointConnector_iff_removalSurvival_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_disjointConnector_iff_removalSurvival_residue_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W} :
-- imply
  gc57_DisjointConnector ends K o x y g ↔ gc55_RemovalSurvival ends K o x y g := by
-- proof
  apply StatMech.Walls.gc57_disjointConnector_iff_removalSurvival_residue ends K

/--
[gc57_countIneq_of_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_countIneq_of_disjointConnector_eq
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
  (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)), gc57_DisjointConnector ends K o x y g) :
-- imply
  gc39_ThreeColouringCountIneq ends o x y g := by
-- proof
  apply StatMech.Walls.gc57_countIneq_of_disjointConnector ends hnd hox hoy hog hxy hxg hyg huniv h

/--
[gc57_disjointConnector_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_disjointConnector_of_disjoint_eq
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
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc57_disjointConnector_of_disjoint ends K hDV hDsrc hdisj

/--
[gc57_disjointConnector_of_ygEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_disjointConnector_of_ygEdge_eq
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
  gc57_DisjointConnector ends K o x y g := by
-- proof
  apply StatMech.Walls.gc57_disjointConnector_of_ygEdge ends hnd K hyg hiV hi

/--
[gc57_witness_disjointConnector_K13](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_witness_disjointConnector_K13_eq :
-- imply
  gc57_DisjointConnector gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc57_witness_disjointConnector_K13

/--
[gc57_witness_disjointConnector_K23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_witness_disjointConnector_K23_eq :
-- imply
  gc57_DisjointConnector gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc57_witness_disjointConnector_K23

/--
[gc57_witness_cosetGateDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_witness_cosetGateDom_eq :
-- imply
  gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc57_witness_cosetGateDom

/--
[gc57_witness_perKCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_witness_perKCount_eq :
-- imply
  gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc57_witness_perKCount

/--
[gc57_refEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_refEnds_univ_sources_eq :
-- imply
  sources gc57_refEnds (univ : Finset (Fin 7)) = ({0, 1, 2, 3} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc57_refEnds_univ_sources

/--
[gc57_refEnds_K_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_refEnds_K_sources_eq :
-- imply
  sources gc57_refEnds ({6} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc57_refEnds_K_sources

/--
[gc57_refEnds_D_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_refEnds_D_sources_eq :
-- imply
  sources gc57_refEnds ({0, 3} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) ∧ sources gc57_refEnds ({1, 2} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc57_refEnds_D_sources

/--
[gc57_ref_base_lex_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_ref_base_lex_eq_eq :
-- imply
  (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({0, 3} : Finset (Fin 7)))) = ({1, 2, 6} : Finset (Fin 7)) := by
-- proof
  apply StatMech.Walls.gc57_ref_base_lex_eq

/--
[gc57_ref_base_wk_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_ref_base_wk_eq_eq :
-- imply
  (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({1, 2} : Finset (Fin 7)))) = ({0, 3, 6} : Finset (Fin 7)) := by
-- proof
  apply StatMech.Walls.gc57_ref_base_wk_eq

/--
[gc57_ref_wk_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_ref_wk_survives_eq :
-- imply
  connK gc57_refEnds ({0, 3, 6} : Finset (Fin 7)) 1 3 := by
-- proof
  apply StatMech.Walls.gc57_ref_wk_survives

/--
[gc57_ref_lex_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_ref_lex_fails_eq :
-- imply
  ¬ connK gc57_refEnds ({1, 2, 6} : Finset (Fin 7)) 1 3 := by
-- proof
  apply StatMech.Walls.gc57_ref_lex_fails

/--
[gc57_lexMinD_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_lexMinD_refuted_eq :
-- imply
  sources gc57_refEnds ({6} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5)) ∧ sources gc57_refEnds ({0, 3} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) ∧ sources gc57_refEnds ({1, 2} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) ∧ ¬ connK gc57_refEnds (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({0, 3} : Finset (Fin 7)))) 1 3 ∧ connK gc57_refEnds (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({1, 2} : Finset (Fin 7)))) 1 3 := by
-- proof
  apply StatMech.Walls.gc57_lexMinD_refuted

/--
[gc57_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc57menger.lean)
-/
@[path]
private lemma gc57_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W), gc57_DisjointConnector ends K o x y g ↔ gc55_RemovalSurvival ends K o x y g) ∧ (¬ connK gc57_refEnds (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({0, 3} : Finset (Fin 7)))) 1 3) ∧ (connK gc57_refEnds (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({1, 2} : Finset (Fin 7)))) 1 3) ∧ gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 ∧ gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
-- proof
  apply StatMech.Walls.gc57_status


-- created on 2026-10-23
