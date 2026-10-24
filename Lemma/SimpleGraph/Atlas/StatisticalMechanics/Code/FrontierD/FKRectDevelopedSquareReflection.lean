import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection
open Set SimpleGraph StatMech.Lattice StatMech StatMech.FrontierD


/--
[fkRectRowReflection_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectRowReflection_val_eq
  {R : FKRectTorus}
  {center : Nat}
  {y : Fin R.height} :
-- imply
  (fkRectRowReflection R center y).val = (2 * center + R.height - y.val) % R.height := by
-- proof
  apply StatMech.FrontierD.fkRectRowReflection_val R center y

/--
[fkRectRowReflection_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectRowReflection_involutive_eq
  {R : FKRectTorus}
  {center : Nat} :
-- imply
  Function.Involutive (fkRectRowReflection R center) := by
-- proof
  apply StatMech.FrontierD.fkRectRowReflection_involutive R center

/--
[fkRectRowReflection_twice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectRowReflection_twice_eq
  {R : FKRectTorus}
  {center : Nat}
  {y : Fin R.height} :
-- imply
  fkRectRowReflection R center (fkRectRowReflection R center y) = y := by
-- proof
  apply StatMech.FrontierD.fkRectRowReflection_twice R center y

/--
[fkRectRowReflection_even_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectRowReflection_even_iff_eq
  {R : FKRectTorus}
  {center : Nat}
  {y : Fin R.height} :
-- imply
  Even (fkRectRowReflection R center y).val ↔ Even y.val := by
-- proof
  apply StatMech.FrontierD.fkRectRowReflection_even_iff R center y

/--
[fkRectRowReflection_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectRowReflection_cast_eq
  {R : FKRectTorus}
  {center : Nat}
  {y : Fin R.height} :
-- imply
  ((fkRectRowReflection R center y).val : ZMod R.height) = (2 * center : ZMod R.height) - y.val := by
-- proof
  apply StatMech.FrontierD.fkRectRowReflection_cast R center y

/--
[fkRectIntModFin_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectIntModFin_cast_eq
  {N : Nat}
  {z : Int}
-- given
  (hN : 0 < N) :
-- imply
  ((fkRectIntModFin hN z).val : ZMod N) = z := by
-- proof
  apply StatMech.FrontierD.fkRectIntModFin_cast hN z

/--
[fkRectRowReflection_intModFin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectRowReflection_intModFin_eq
  {R : FKRectTorus}
  {center : Nat}
  {z : Int} :
-- imply
  fkRectRowReflection R center (fkRectIntModFin R.height_pos z) = fkRectIntModFin R.height_pos (2 * (center : Int) - z) := by
-- proof
  apply StatMech.FrontierD.fkRectRowReflection_intModFin R center z

/--
[fkRectRowReflection_cyclicPred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectRowReflection_cyclicPred_eq
  {R : FKRectTorus}
  {center : Nat}
  {y : Fin R.height} :
-- imply
  fkRectRowReflection R center (SixVertexArrows.cyclicPred R.height_pos y) = finitePeriodicSucc R.height_pos (fkRectRowReflection R center y) := by
-- proof
  apply StatMech.FrontierD.fkRectRowReflection_cyclicPred R center y

/--
[fkRectRowReflection_succ_cyclicPred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectRowReflection_succ_cyclicPred_eq
  {R : FKRectTorus}
  {center : Nat}
  {y : Fin R.height} :
-- imply
  SixVertexArrows.cyclicPred R.height_pos (finitePeriodicSucc R.height_pos (fkRectRowReflection R center y)) = fkRectRowReflection R center y := by
-- proof
  apply StatMech.FrontierD.fkRectRowReflection_succ_cyclicPred R center y

/--
[fkRectDevelopedReflectionVertexEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectDevelopedReflectionVertexEquiv_apply_eq
  {R : FKRectTorus}
  {center : Nat}
  {v : R.Vertex} :
-- imply
  fkRectDevelopedReflectionVertexEquiv R center v = (v.1, fkRectRowReflection R center v.2) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectionVertexEquiv_apply R center v

/--
[fkRectSquareUndevelopPoint_developedSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectSquareUndevelopPoint_developedSwap_eq
  {n : Nat}
  {z : Site 2} :
-- imply
  fkRectSquareUndevelopPoint (fkRectDevelopedSquarePoint n (StatMech.Universality.crf_swap z)) = let p := fkRectSquareUndevelopPoint (fkRectDevelopedSquarePoint n z) (p.1, 2 * (n : Int) - p.2) := by
-- proof
  apply StatMech.FrontierD.fkRectSquareUndevelopPoint_developedSwap n z

/--
[fkRectDevelopedReflectionVertex_developedSquareVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectDevelopedReflectionVertex_developedSquareVertex_eq
  {R : FKRectTorus}
  {n : Nat}
  {z : Site 2} :
-- imply
  fkRectDevelopedReflectionVertexEquiv R n (fkRectDevelopedSquareVertex R n z) = fkRectDevelopedSquareVertex R n (StatMech.Universality.crf_swap z) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectionVertex_developedSquareVertex R n z

/--
[fkRectDevelopedReflectionEdgeEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectDevelopedReflectionEdgeEquiv_apply_eq
  {R : FKRectTorus}
  {center : Nat}
  {a : R.EdgeIndex} :
-- imply
  fkRectDevelopedReflectionEdgeEquiv R center a = (a.1, (a.2.1, finitePeriodicSucc R.height_pos (fkRectRowReflection R center a.2.2))) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectionEdgeEquiv_apply R center a

/--
[fkRectTorusIndexedEdge_developedReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectTorusIndexedEdge_developedReflection_eq
  {R : FKRectTorus}
  {center : Nat}
  {a : R.EdgeIndex} :
-- imply
  fkRectTorusIndexedEdge R (fkRectDevelopedReflectionEdgeEquiv R center a) = Sym2.map (fkRectDevelopedReflectionVertexEquiv R center) (fkRectTorusIndexedEdge R a) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusIndexedEdge_developedReflection R center a

/--
[fkRectTorusGraph_adj_developedReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectTorusGraph_adj_developedReflection_eq
  {R : FKRectTorus}
  {center : Nat}
  {x y : R.Vertex} :
-- imply
  (fkRectTorusGraph R).Adj (fkRectDevelopedReflectionVertexEquiv R center x) (fkRectDevelopedReflectionVertexEquiv R center y) ↔ (fkRectTorusGraph R).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectTorusGraph_adj_developedReflection R center x y

/--
[fkRectDevelopedReflectionVertexEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectDevelopedReflectionVertexEquiv_symm_apply_eq
  {R : FKRectTorus}
  {center : Nat}
  {v : R.Vertex} :
-- imply
  (fkRectDevelopedReflectionVertexEquiv R center).symm v = fkRectDevelopedReflectionVertexEquiv R center v := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectionVertexEquiv_symm_apply R center v

/--
[fkRectDevelopedReflectionEdgeEquiv_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectDevelopedReflectionEdgeEquiv_involutive_eq
  {R : FKRectTorus}
  {center : Nat} :
-- imply
  Function.Involutive (fkRectDevelopedReflectionEdgeEquiv R center) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectionEdgeEquiv_involutive R center

/--
[fkRectDevelopedReflectionEdgeEquiv_twice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectDevelopedReflectionEdgeEquiv_twice_eq
  {R : FKRectTorus}
  {center : Nat}
  {a : R.EdgeIndex} :
-- imply
  fkRectDevelopedReflectionEdgeEquiv R center (fkRectDevelopedReflectionEdgeEquiv R center a) = a := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectionEdgeEquiv_twice R center a

/--
[fkRectDevelopedReflectionEdgeEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectDevelopedReflectionEdgeEquiv_symm_apply_eq
  {R : FKRectTorus}
  {center : Nat}
  {a : R.EdgeIndex} :
-- imply
  (fkRectDevelopedReflectionEdgeEquiv R center).symm a = fkRectDevelopedReflectionEdgeEquiv R center a := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectionEdgeEquiv_symm_apply R center a

/--
[fkRectDevelopedReflectionConfigurationEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectDevelopedReflectionConfigurationEquiv_apply_eq
  {R : FKRectTorus}
  {center : Nat}
  {omega : R.Configuration}
  {a : R.EdgeIndex} :
-- imply
  fkRectDevelopedReflectionConfigurationEquiv R center omega a = omega ((fkRectDevelopedReflectionEdgeEquiv R center).symm a) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectionConfigurationEquiv_apply R center omega a

/--
[fkRectOpenGraph_developedReflection_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectOpenGraph_developedReflection_adj_eq
  {R : FKRectTorus}
  {center : Nat}
  {omega : R.Configuration}
  {x y : R.Vertex} :
-- imply
  (fkRectOpenGraph R (fkRectDevelopedReflectionConfigurationEquiv R center omega)).Adj (fkRectDevelopedReflectionVertexEquiv R center x) (fkRectDevelopedReflectionVertexEquiv R center y) ↔ (fkRectOpenGraph R omega).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_developedReflection_adj R center omega x y

/--
[fkRectOpenEdgeCount_developedReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectOpenEdgeCount_developedReflection_eq
  {R : FKRectTorus}
  {center : Nat}
  {omega : R.Configuration} :
-- imply
  fkRectOpenEdgeCount R (fkRectDevelopedReflectionConfigurationEquiv R center omega) = fkRectOpenEdgeCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectOpenEdgeCount_developedReflection R center omega

/--
[fkRectNumClusters_developedReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectNumClusters_developedReflection_eq
  {R : FKRectTorus}
  {center : Nat}
  {omega : R.Configuration} :
-- imply
  fkRectNumClusters R (fkRectDevelopedReflectionConfigurationEquiv R center omega) = fkRectNumClusters R omega := by
-- proof
  apply StatMech.FrontierD.fkRectNumClusters_developedReflection R center omega

/--
[fkRectCriticalReducedWeight_developedReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectCriticalReducedWeight_developedReflection_eq
  {R : FKRectTorus}
  {center : Nat}
  {q : Real}
  {omega : R.Configuration} :
-- imply
  fkRectCriticalReducedWeight R q (fkRectDevelopedReflectionConfigurationEquiv R center omega) = fkRectCriticalReducedWeight R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedWeight_developedReflection R center q omega

/--
[fkRectCriticalRandomClusterProb_developedReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectCriticalRandomClusterProb_developedReflection_eq
  {R : FKRectTorus}
  {center : Nat}
  {q : Real}
  {omega : R.Configuration} :
-- imply
  fkRectCriticalRandomClusterProb R q (fkRectDevelopedReflectionConfigurationEquiv R center omega) = fkRectCriticalRandomClusterProb R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalRandomClusterProb_developedReflection R center q omega

/--
[fkRectFullGraphConfiguration_developedReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectFullGraphConfiguration_developedReflection_eq
  {R : FKRectTorus}
  {center : Nat}
  {omega : R.Configuration}
  {e : Sym2 R.Vertex} :
-- imply
  fkRectFullGraphConfiguration R (fkRectDevelopedReflectionConfigurationEquiv R center omega) (Sym2.map (fkRectDevelopedReflectionVertexEquiv R center) e) = fkRectFullGraphConfiguration R omega e := by
-- proof
  apply StatMech.FrontierD.fkRectFullGraphConfiguration_developedReflection R center omega e

/--
[fkRectDevelopedSquarePullback_developedReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectDevelopedSquarePullback_developedReflection_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega : R.Configuration} :
-- imply
  fkRectDevelopedSquarePullback R n (fkRectDevelopedReflectionConfigurationEquiv R n omega) = StatMech.Universality.crf_swapConfig (fkRectDevelopedSquarePullback R n omega) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquarePullback_developedReflection R n omega

/--
[fkRectDevelopedSquare_reflection_mem_vertical_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_reflection_mem_vertical_iff_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega : R.Configuration} :
-- imply
  fkRectDevelopedReflectionConfigurationEquiv R n omega ∈ fkRectDevelopedSquareVerticalCrossingEvent R n ↔ omega ∈ fkRectDevelopedSquareHorizontalCrossingEvent R n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_reflection_mem_vertical_iff R n omega

/--
[fkRectCritical_developedSquareHorizontalMass_eq_verticalMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectCritical_developedSquareHorizontalMass_eq_verticalMass_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real} :
-- imply
  fkRectCriticalEventMass R q (fkRectDevelopedSquareHorizontalCrossingEvent R n) = fkRectCriticalEventMass R q (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedSquareHorizontalMass_eq_verticalMass R n q

/--
[fkRectCritical_developedSquareHorizontalMass_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectCritical_developedSquareHorizontalMass_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 <= n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 <= q) :
-- imply
  1 / (2 * (1 + q)) <= fkRectCriticalEventMass R q (fkRectDevelopedSquareHorizontalCrossingEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedSquareHorizontalMass_ge R n hn hwidth hheight hq

/--
[fkRectCritical_developedSquareVerticalMass_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectCritical_developedSquareVerticalMass_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 <= n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 <= q) :
-- imply
  1 / (2 * (1 + q)) <= fkRectCriticalEventMass R q (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedSquareVerticalMass_ge R n hn hwidth hheight hq

/--
[fkRectCritical_developedThreeByOneVerticalMass_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOneVerticalMass_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 <= n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 <= q) :
-- imply
  1 / (2 * (1 + q)) <= fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOneVerticalMass_ge R n hn hwidth hheight hq


-- created on 2026-10-23
