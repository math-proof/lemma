import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc75bcyclespace
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc75b_disjoint_iff_gEdge_and_rest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_disjoint_iff_gEdge_and_rest_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {P D : Finset ι}
  {eD : ι}
-- given
  (heD : eD ∈ D) :
-- imply
  Disjoint P D ↔ eD ∉ P ∧ Disjoint P (D \ ({eD} : Finset ι)) := by
-- proof
  apply StatMech.Walls.gc75b_disjoint_iff_gEdge_and_rest heD

/--
[gc75b_survives_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_survives_of_disjoint_eq
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
  apply StatMech.Walls.gc75b_survives_of_disjoint ends hPG hPD hPconn

/--
[gc75b_disjointConnector_iff_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_disjointConnector_iff_survives_eq
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
  apply StatMech.Walls.gc75b_disjointConnector_iff_survives ends hnd hog

/--
[gc75b_bridgeConnectors_iff_notCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_bridgeConnectors_iff_notCut_eq
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
  (hog : o ≠ g) :
-- imply
  (∀ L ∈ gc51_LblockSet ends K o x g, ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g) ↔ (∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) := by
-- proof
  apply StatMech.Walls.gc75b_bridgeConnectors_iff_notCut ends hnd K hog

/--
[gc75b_bridgeConnectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_bridgeConnectors_eq
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
  apply StatMech.Walls.gc75b_bridgeConnectors ends hnd K hog hDV hDsrc hD1 hconn

/--
[gc75b_bridgeConnectors_of_notCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_bridgeConnectors_of_notCut_eq
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
  apply StatMech.Walls.gc75b_bridgeConnectors_of_notCut ends hnd K hog hDV hDsrc hD1 hnotcut

/--
[gc75b_room_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_room_survives_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {D : Finset ι}
  {y g : W}
-- given
  (hge3 : 3 ≤ degK ends (univ : Finset ι) g)
  (hDsrc : sources ends D = ({y, g} : Finset W))
  (hD1 : degK ends D g = 1) :
-- imply
  2 ≤ degK ends ((univ : Finset ι) \ D) g := by
-- proof
  apply StatMech.Walls.gc75b_room_survives ends hge3 hDsrc hD1

/--
[gc75b_brEnds2_P_src](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_brEnds2_P_src_eq :
-- imply
  sources gc74b_brEnds2 ({0, 2} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc75b_brEnds2_P_src

/--
[gc75b_brEnds2_P_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_brEnds2_P_conn_eq :
-- imply
  connK gc74b_brEnds2 ({0, 2} : Finset (Fin 5)) 0 3 := by
-- proof
  apply StatMech.Walls.gc75b_brEnds2_P_conn

/--
[gc75b_brEnds2_disjoint_P123](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_brEnds2_disjoint_P123_eq :
-- imply
  ({0, 2} : Finset (Fin 5)) ⊆ (({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) ∧ sources gc74b_brEnds2 ({0, 2} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) ∧ Disjoint ({0, 2} : Finset (Fin 5)) ({3} : Finset (Fin 5)) ∧ connK gc74b_brEnds2 ({0, 2} : Finset (Fin 5)) 0 3 := by
-- proof
  apply StatMech.Walls.gc75b_brEnds2_disjoint_P123

/--
[gc75b_brEnds2_disjoint_P124](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_brEnds2_disjoint_P124_eq :
-- imply
  ({0, 2} : Finset (Fin 5)) ⊆ (({0} : Finset (Fin 5)) ∪ ({1, 2, 4} : Finset (Fin 5))) ∧ sources gc74b_brEnds2 ({0, 2} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) ∧ Disjoint ({0, 2} : Finset (Fin 5)) ({3} : Finset (Fin 5)) ∧ connK gc74b_brEnds2 ({0, 2} : Finset (Fin 5)) 0 3 := by
-- proof
  apply StatMech.Walls.gc75b_brEnds2_disjoint_P124

/--
[gc75b_brEnds2_twoCommodityLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_brEnds2_twoCommodityLeaf_eq :
-- imply
  gc71_TwoCommodityLeaf gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc75b_brEnds2_twoCommodityLeaf

/--
[gc75b_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc75bcyclespace.lean)
-/
@[path]
private lemma gc75b_status_eq :
-- imply
  (∀ {ι : Type*} [DecidableEq ι] [Fintype ι] (P D : Finset ι) (eD : ι), eD ∈ D → (Disjoint P D ↔ eD ∉ P ∧ Disjoint P (D \ ({eD} : Finset ι)))) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K L D : Finset ι) (o g : W), o ≠ g → ((∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g) ↔ connK ends ((K ∪ L) \ D) o g)) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W) (D : Finset ι), o ≠ g → D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) → degK ends D g = 1 → (∀ L ∈ gc51_LblockSet ends K o x g, ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g) → gc71_TwoCommodityLeaf ends K o x y g) ∧ gc71_TwoCommodityLeaf gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc75b_status


-- created on 2026-10-23
