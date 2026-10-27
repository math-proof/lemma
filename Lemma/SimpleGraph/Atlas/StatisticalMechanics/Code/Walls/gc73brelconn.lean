import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc73brelconn.Part2
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc73b_perLClause_of_notCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_perLClause_of_notCut_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D : Finset ι}
  {o g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g)
  (hsurv : connK ends ((K ∪ L) \ D) o g) :
-- imply
  ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g := by
-- proof
  apply StatMech.Walls.gc73b_perLClause_of_notCut ends hnd hog hsurv

/--
[gc73b_notCut_of_perLClause](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_notCut_of_perLClause_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D P : Finset ι}
  {o g : W}
-- given
  (hPG : P ⊆ K ∪ L)
  (hPD : Disjoint P D)
  (hPconn : connK ends P o g) :
-- imply
  connK ends ((K ∪ L) \ D) o g := by
-- proof
  apply StatMech.Walls.gc73b_notCut_of_perLClause ends hPG hPD hPconn

/--
[gc73b_twoCommodityLeaf_of_notCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_twoCommodityLeaf_of_notCut_eq
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
  (hnotcut : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g := by
-- proof
  apply StatMech.Walls.gc73b_twoCommodityLeaf_of_notCut ends hnd K hog hDV hDsrc hD1 hnotcut

/--
[gc73b_notCut_of_relConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_notCut_of_relConn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L : Finset ι}
  {o g : W}
  {D : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g)
  (hconn : connK ends (K ∪ L) o g)
  (hrel : ∀ P₁ : Finset ι, P₁ ⊆ K ∪ L → sources ends P₁ = ({o, g} : Finset W) → connK ends ((K ∪ L) \ P₁) o g)
  (hDsub : ∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁) :
-- imply
  connK ends ((K ∪ L) \ D) o g := by
-- proof
  apply StatMech.Walls.gc73b_notCut_of_relConn ends hnd hog hconn hrel hDsub

/--
[gc73b_twoCommodityLeaf_of_relConn_perL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_twoCommodityLeaf_of_relConn_perL_eq
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
  (hrel : ∀ L ∈ gc51_LblockSet ends K o x g, (∀ P₁ : Finset ι, P₁ ⊆ K ∪ L → sources ends P₁ = ({o, g} : Finset W) → connK ends ((K ∪ L) \ P₁) o g) ∧ (∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁)) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g := by
-- proof
  apply StatMech.Walls.gc73b_twoCommodityLeaf_of_relConn_perL ends hnd K hox hog hKsrc hDV hDsrc hD1 hrel

/--
[gc73b_gcopyRemoval_of_fullRemoval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_gcopyRemoval_of_fullRemoval_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D : Finset ι}
  {eD : ι}
  {o g : W}
-- given
  (heD : eD ∈ D)
  (hsurv : connK ends ((K ∪ L) \ D) o g) :
-- imply
  connK ends ((K ∪ L) \ ({eD} : Finset ι)) o g := by
-- proof
  apply StatMech.Walls.gc73b_gcopyRemoval_of_fullRemoval ends heD hsurv

/--
[gc73b_brEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_brEnds_loopless_eq :
-- imply
  ∀ i : Fin 5, ¬ (gc73b_brEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc73b_brEnds_loopless

/--
[gc73b_brEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_brEnds_univ_sources_eq :
-- imply
  sources gc73b_brEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc73b_brEnds_univ_sources

/--
[gc73b_brEnds_K_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_brEnds_K_sources_eq :
-- imply
  sources gc73b_brEnds ({0} : Finset (Fin 5)) = ({0, 1} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc73b_brEnds_K_sources

/--
[gc73b_brEnds_L_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_brEnds_L_sources_eq :
-- imply
  sources gc73b_brEnds ({3, 4} : Finset (Fin 5)) = (∅ : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc73b_brEnds_L_sources

/--
[gc73b_brEnds_gate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_brEnds_gate_eq :
-- imply
  connK gc73b_brEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc73b_brEnds_gate

/--
[gc73b_brEnds_og_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_brEnds_og_conn_eq :
-- imply
  connK gc73b_brEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc73b_brEnds_og_conn

/--
[gc73b_brEnds_bridge_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_brEnds_bridge_cut_eq :
-- imply
  ¬ connK gc73b_brEnds ((({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc73b_brEnds_bridge_cut

/--
[gc73b_bridge_edge_not_gEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_bridge_edge_not_gEdge_eq :
-- imply
  connK gc73b_brEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 0 3 ∧ (¬ connK gc73b_brEnds ((({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 0 3) ∧ (3 : Fin 4) ∉ gc73b_brEnds 0 := by
-- proof
  apply StatMech.Walls.gc73b_bridge_edge_not_gEdge

/--
[gc73b_gc59_surv_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_gc59_surv_23_eq :
-- imply
  connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc73b_gc59_surv_23

/--
[gc73b_gc59_surv_24](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_gc59_surv_24_eq :
-- imply
  connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc73b_gc59_surv_24

/--
[gc73b_gc59_surv_34](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_gc59_surv_34_eq :
-- imply
  connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc73b_gc59_surv_34

/--
[gc73b_witness_twoCommodityLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_witness_twoCommodityLeaf_eq :
-- imply
  gc71_TwoCommodityLeaf gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc73b_witness_twoCommodityLeaf

/--
[gc73b_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean)
-/
@[path]
private lemma gc73b_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W) (D : Finset ι), o ≠ g → D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) → degK ends D g = 1 → (∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) → gc71_TwoCommodityLeaf ends K o x y g) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K L : Finset ι) (o g : W), o ≠ g → connK ends (K ∪ L) o g → (∀ P₁ : Finset ι, P₁ ⊆ K ∪ L → sources ends P₁ = ({o, g} : Finset W) → connK ends ((K ∪ L) \ P₁) o g) → ∀ {D : Finset ι}, (∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁) → connK ends ((K ∪ L) \ D) o g) ∧ (connK gc73b_brEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 0 3 ∧ (¬ connK gc73b_brEnds ((({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 0 3) ∧ (3 : Fin 4) ∉ gc73b_brEnds 0) ∧ gc71_TwoCommodityLeaf gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc73b_status


-- created on 2026-10-23
