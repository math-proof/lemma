import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc74bbridge.Part2
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc74b_bridgeEdge_notMem_of_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_bridgeEdge_notMem_of_survives_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D : Finset ι}
  {eStar : ι}
  {o g : W}
-- given
  (hbridge : ¬ connK ends ((K ∪ L) \ ({eStar} : Finset ι)) o g)
  (hsurv : connK ends ((K ∪ L) \ D) o g) :
-- imply
  eStar ∉ D := by
-- proof
  apply StatMech.Walls.gc74b_bridgeEdge_notMem_of_survives ends hbridge hsurv

/--
[gc74b_survival_of_bridge_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_survival_of_bridge_reroute_eq
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
  apply StatMech.Walls.gc74b_survival_of_bridge_reroute ends hPG hPD hPconn

/--
[gc74b_bridge_perLClause_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_bridge_perLClause_iff_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D : Finset ι}
  {o g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g) :
-- imply
  (∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g) ↔ connK ends ((K ∪ L) \ D) o g := by
-- proof
  apply StatMech.Walls.gc74b_bridge_perLClause_iff ends hnd hog

/--
[gc74b_twoCommodityLeaf_of_bridgeConnectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_twoCommodityLeaf_of_bridgeConnectors_eq
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
  (hconn : ∀ L ∈ gc51_LblockSet ends K o x g, ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g) :
-- imply
  gc71_TwoCommodityLeaf ends K o x y g := by
-- proof
  apply StatMech.Walls.gc74b_twoCommodityLeaf_of_bridgeConnectors ends hnd K hog hDV hDsrc hD1 hconn

/--
[gc74b_survives_of_gEdge_off_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_survives_of_gEdge_off_route_eq
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
  apply StatMech.Walls.gc74b_survives_of_gEdge_off_route ends hPG hPD hPconn

/--
[gc74b_bridge_survives_of_disjointConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_bridge_survives_of_disjointConnector_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D P : Finset ι}
  {o g : W}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g)
  (hPG : P ⊆ K ∪ L)
  (hPD : Disjoint P D)
  (hPconn : connK ends P o g) :
-- imply
  ∃ P', P' ⊆ K ∪ L ∧ sources ends P' = ({o, g} : Finset W) ∧ Disjoint P' D ∧ connK ends P' o g := by
-- proof
  apply StatMech.Walls.gc74b_bridge_survives_of_disjointConnector ends hnd hog hPG hPD hPconn

/--
[gc74b_brEnds2_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_loopless_eq :
-- imply
  ∀ i : Fin 5, ¬ (gc74b_brEnds2 i).IsDiag := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_loopless

/--
[gc74b_brEnds2_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_univ_sources_eq :
-- imply
  sources gc74b_brEnds2 (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_univ_sources

/--
[gc74b_brEnds2_K_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_K_sources_eq :
-- imply
  sources gc74b_brEnds2 ({0} : Finset (Fin 5)) = ({0, 1} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_K_sources

/--
[gc74b_brEnds2_g_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_g_deg3_eq :
-- imply
  degK gc74b_brEnds2 (univ : Finset (Fin 5)) 3 = 3 := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_g_deg3

/--
[gc74b_brEnds2_L_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_L_sources_eq :
-- imply
  sources gc74b_brEnds2 ({1, 2, 3} : Finset (Fin 5)) = (∅ : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_L_sources

/--
[gc74b_brEnds2_gate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_gate_eq :
-- imply
  connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_gate

/--
[gc74b_brEnds2_og_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_og_conn_eq :
-- imply
  connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_og_conn

/--
[gc74b_brEnds2_bridge_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_bridge_cut_eq :
-- imply
  ¬ connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_bridge_cut

/--
[gc74b_bridge_edge_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_bridge_edge_in_K_eq :
-- imply
  connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) 0 3 ∧ (¬ connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 0 3) ∧ (0 : Fin 5) ∈ ({0} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc74b_bridge_edge_in_K

/--
[gc74b_brEnds2_badD_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_badD_data_eq :
-- imply
  ({1, 2} : Finset (Fin 5)) ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) ∧ sources gc74b_brEnds2 ({1, 2} : Finset (Fin 5)) = ({2, 3} : Finset (Fin 4)) ∧ degK gc74b_brEnds2 ({1, 2} : Finset (Fin 5)) 3 = 1 := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_badD_data

/--
[gc74b_bridge_badD_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_bridge_badD_fails_eq :
-- imply
  ¬ connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc74b_bridge_badD_fails

/--
[gc74b_brEnds2_goodD_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_goodD_data_eq :
-- imply
  ({3} : Finset (Fin 5)) ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) ∧ sources gc74b_brEnds2 ({3} : Finset (Fin 5)) = ({2, 3} : Finset (Fin 4)) ∧ degK gc74b_brEnds2 ({3} : Finset (Fin 5)) 3 = 1 := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_goodD_data

/--
[gc74b_bridge_goodD_works](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_bridge_goodD_works_eq :
-- imply
  connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc74b_bridge_goodD_works

/--
[gc74b_bridge_twoCommodity_content](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_bridge_twoCommodity_content_eq :
-- imply
  (¬ connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3) ∧ connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc74b_bridge_twoCommodity_content

/--
[gc74b_brEnds2_gate_fail_34](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_gate_fail_34_eq :
-- imply
  ¬ connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_gate_fail_34

/--
[gc74b_brEnds2_gate_fail_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_gate_fail_empty_eq :
-- imply
  ¬ connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ (∅ : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_gate_fail_empty

/--
[gc74b_brEnds2_gate_124](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_gate_124_eq :
-- imply
  connK gc74b_brEnds2 (({0} : Finset (Fin 5)) ∪ ({1, 2, 4} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_gate_124

/--
[gc74b_brEnds2_LblockSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_LblockSet_eq :
-- imply
  gc51_LblockSet gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 1 3 = ({({1, 2, 3} : Finset (Fin 5)), ({1, 2, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5))) := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_LblockSet

/--
[gc74b_brEnds2_surv_123](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_surv_123_eq :
-- imply
  connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_surv_123

/--
[gc74b_brEnds2_surv_124](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_brEnds2_surv_124_eq :
-- imply
  connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 4} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc74b_brEnds2_surv_124

/--
[gc74b_bridge_twoCommodityLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_bridge_twoCommodityLeaf_eq :
-- imply
  gc71_TwoCommodityLeaf gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc74b_bridge_twoCommodityLeaf

/--
[gc74b_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean)
-/
@[path]
private lemma gc74b_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (K L D : Finset ι) (eStar : ι) (o g : W), (¬ connK ends ((K ∪ L) \ ({eStar} : Finset ι)) o g) → connK ends ((K ∪ L) \ D) o g → eStar ∉ D) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W) (D : Finset ι), o ≠ g → D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) → degK ends D g = 1 → (∀ L ∈ gc51_LblockSet ends K o x g, ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g) → gc71_TwoCommodityLeaf ends K o x y g) ∧ ((¬ connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3) ∧ connK gc74b_brEnds2 ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3) ∧ gc71_TwoCommodityLeaf gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc74b_status


-- created on 2026-10-23
