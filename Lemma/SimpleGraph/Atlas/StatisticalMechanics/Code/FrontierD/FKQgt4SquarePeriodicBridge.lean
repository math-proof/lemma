import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicBridge.Part3
open Finset SimpleGraph MeasureTheory StatMech StatMech.FrontierD


/--
[fkSquarePeriodic_orbitBox_eq_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodic_orbitBox_eq_box_eq
  {n : Nat} :
-- imply
  square.orbitBox n = (box_finite 2 n).toFinset := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_orbitBox_eq_box n

/--
[fkSquarePeriodic_mem_orbitBox_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodic_mem_orbitBox_iff_eq
  {n : Nat}
  {x : Site 2} :
-- imply
  x ∈ square.orbitBox n ↔ x ∈ box 2 n := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_mem_orbitBox_iff n x

/--
[fkSquarePeriodicVertexEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodicVertexEquiv_apply_eq
  {n : Nat}
  {x : square.OrbitVertex n} :
-- imply
  (fkSquarePeriodicVertexEquiv n x : Site 2) = (x : Site 2) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodicVertexEquiv_apply n x

/--
[fkSquarePeriodicVertexEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodicVertexEquiv_adj_eq
  {n : Nat}
  {x y : square.OrbitVertex n} :
-- imply
  (square.orbitGraph n).Adj x y ↔ (FK.boxGraph 2 n).Adj (fkSquarePeriodicVertexEquiv n x) (fkSquarePeriodicVertexEquiv n y) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodicVertexEquiv_adj n x y

/--
[fkSquarePeriodicVertexEquiv_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodicVertexEquiv_boundary_eq
  {n : Nat}
  {x : square.OrbitVertex n} :
-- imply
  square.orbitBoundary n x ↔ FK.boxBoundary 2 n (fkSquarePeriodicVertexEquiv n x) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodicVertexEquiv_boundary n x

/--
[fkSquarePeriodic_fkProb_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodic_fkProb_reCfgIso_eq
  {n : Nat}
  {p q : Real}
  {omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))} :
-- imply
  FK.fkProb (square.orbitGraph n) p q (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) = FK.fkProb (FK.boxGraph 2 n) p q omega := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_fkProb_reCfgIso n p q omega

/--
[fkSquarePeriodic_wiredFkProb_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodic_wiredFkProb_reCfgIso_eq
  {n : Nat}
  {p q : Real}
  {omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))} :
-- imply
  FK.wiredFkProb (square.orbitGraph n) (square.orbitBoundary n) p q (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) = FK.wiredFkProb (FK.boxGraph 2 n) (FK.boxBoundary 2 n) p q omega := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_wiredFkProb_reCfgIso n p q omega

/--
[fkSquarePeriodic_freeFinitePMF_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodic_freeFinitePMF_reCfgIso_eq
  {n : Nat}
  {p q : Real}
  {omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  square.freeFinitePMF n hp hp1 hq (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) = FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq omega := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_freeFinitePMF_reCfgIso n hp hp1 hq omega

/--
[fkSquarePeriodic_wiredFinitePMF_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodic_wiredFinitePMF_reCfgIso_eq
  {n : Nat}
  {p q : Real}
  {omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  square.wiredFinitePMF n hp hp1 hq (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) = FK.wiredFkPMF (FK.boxGraph 2 n) (FK.boxBoundary 2 n) hp hp1 hq omega := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_wiredFinitePMF_reCfgIso n hp hp1 hq omega

/--
[fkSquarePeriodic_freeFinitePMF_eq_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodic_freeFinitePMF_eq_map_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  square.freeFinitePMF n hp hp1 hq = (FK.fkPMF (FK.boxGraph 2 n) hp hp1 hq).map (fkSquarePeriodicConfigEquiv n) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_freeFinitePMF_eq_map n hp hp1 hq

/--
[fkSquarePeriodic_wiredFinitePMF_eq_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodic_wiredFinitePMF_eq_map_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  square.wiredFinitePMF n hp hp1 hq = (FK.wiredFkPMF (FK.boxGraph 2 n) (FK.boxBoundary 2 n) hp hp1 hq).map (fkSquarePeriodicConfigEquiv n) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_wiredFinitePMF_eq_map n hp hp1 hq

/--
[fkSquarePeriodic_edgeIncl_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodic_edgeIncl_eq_eq
  {n : Nat}
  {e : Sym2 (square.OrbitVertex n)} :
-- imply
  square.edgeIncl n e = FK.edgeIncl 2 n (Sym2.map (fkSquarePeriodicVertexEquiv n) e) := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_edgeIncl_eq n e

/--
[fkSquarePeriodic_extendEdge_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodic_extendEdge_reCfgIso_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (FK.boxVerts 2 n))} :
-- imply
  square.extendEdge n (FK.reCfgIso (fkSquarePeriodicVertexEquiv n) omega) = FK.extendEdge 2 n omega := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_extendEdge_reCfgIso n omega

/--
[fkSquarePeriodic_freeFiniteMeasure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodic_freeFiniteMeasure_eq_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  square.freeFiniteMeasure n hp hp1 hq = FK.freeFiniteMeasure 2 n hp hp1 hq := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_freeFiniteMeasure_eq n hp hp1 hq

/--
[fkSquarePeriodic_wiredFiniteMeasure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicBridge.lean)
-/
@[path]
private lemma fkSquarePeriodic_wiredFiniteMeasure_eq_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  square.wiredFiniteMeasure n hp hp1 hq = FK.wiredFiniteMeasure 2 n hp hp1 hq := by
-- proof
  apply StatMech.FrontierD.fkSquarePeriodic_wiredFiniteMeasure_eq n hp hp1 hq


-- created on 2026-10-23
