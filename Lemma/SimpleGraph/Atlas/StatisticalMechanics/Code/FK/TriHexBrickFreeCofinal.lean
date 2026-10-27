import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFreeCofinal.Part2
open Filter Finset Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexPlanarFiniteStarToHexBuffered_edgeIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarToHexBuffered_edgeIncl_eq
  {m : Nat}
  {e : Sym2 (triHexPlanarFiniteStarPlanar m).V} :
-- imply
  triHexPlanarFiniteStarEdgeIncl m e = hexagonal.edgeIncl (hexagonal.bufferedRadius (m + 2)) (ocd_innerEdge (triHexPlanarFiniteStarToHexBuffered m) e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarToHexBuffered_edgeIncl m e

/--
[triHexFaceDualInnerActive_starRestrict_buffered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexFaceDualInnerActive_starRestrict_buffered_eq
  {N m : Nat}
  {rho : ConfigSpace (Sym2 (hexagonal.BufferedVertex (m + 2)))}
-- given
  (hNm : N < m) :
-- imply
  triHexFaceDualInnerActive N (triHexPlanarFiniteStarExtendEdge m (ocd_innerRestrict (triHexPlanarFiniteStarToHexBuffered m) rho)) = triHexFaceDualInnerActive N (hexagonal.extendEdge (hexagonal.bufferedRadius (m + 2)) rho) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFaceDualInnerActive_starRestrict_buffered hNm rho

/--
[triHexStarFaceDualInnerEvent_preimage_outerBuffered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexStarFaceDualInnerEvent_preimage_outerBuffered_eq
  {N m : Nat}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hNm : N < m) :
-- imply
  ocd_innerRestrict (triHexPlanarFiniteStarToHexBuffered m) ⁻¹' triHexStarFaceDualInnerEvent hNm A = triHexHexBufferedFaceDualInnerEvent N (m + 2) A := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexStarFaceDualInnerEvent_preimage_outerBuffered hNm A

/--
[triHexStarFaceDualInnerEvent_isDecreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexStarFaceDualInnerEvent_isDecreasing_eq
  {N m : Nat}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hNm : N < m)
  (hA : IsIncreasing A) :
-- imply
  IsDecreasing (triHexStarFaceDualInnerEvent hNm A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexStarFaceDualInnerEvent_isDecreasing hNm hA

/--
[triHexHexBufferedFaceDualInnerEvent_le_freeStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexHexBufferedFaceDualInnerEvent_le_freeStar_eq
  {N m : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ rho, (triHexHexBufferedFaceDualInnerEvent N (m + 2) A).indicator (fun _ => (1 : Real)) rho * fkProb (hexagonal.bufferedGraph (m + 2)) p q rho) ≤ ∑ omega : ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex m)), (triHexStarFaceDualInnerEvent hNm A).indicator (fun _ => (1 : Real)) omega * fkProb (triHexPlanarFiniteStarGraph m) p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexHexBufferedFaceDualInnerEvent_le_freeStar hNm hp hp1 hq hA

/--
[triHexPlanarFiniteStarToHexBufferedLE_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarToHexBufferedLE_val_eq
  {r n : Nat}
  {v : TriHexPlanarFiniteStarVertex r}
-- given
  (hrn : r + 2 ≤ n) :
-- imply
  (triHexPlanarFiniteStarToHexBufferedLE hrn v : HexVertex) = triHexPlanarFiniteStarVertexEmbedding r v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarToHexBufferedLE_val hrn v

/--
[triHexPlanarFiniteStarToHexBufferedLE_edgeIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarToHexBufferedLE_edgeIncl_eq
  {r n : Nat}
  {e : Sym2 (TriHexPlanarFiniteStarVertex r)}
-- given
  (hrn : r + 2 ≤ n) :
-- imply
  triHexPlanarFiniteStarEdgeIncl r e = hexagonal.edgeIncl (hexagonal.bufferedRadius n) (ocd_innerEdge (triHexPlanarFiniteStarToHexBufferedLE hrn) e) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarToHexBufferedLE_edgeIncl hrn e

/--
[triHexPlanarHexBufferedToFiniteStar_edgeIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexBufferedToFiniteStar_edgeIncl_eq
  {n : Nat}
  {e : Sym2 (hexagonal.BufferedVertex n)} :
-- imply
  triHexPlanarFiniteStarEdgeIncl (triHexPlanarHexBufferedOuterStarLevel n) (ocd_innerEdge (triHexPlanarHexBufferedToFiniteStar n) e) = hexagonal.edgeIncl (hexagonal.bufferedRadius n) e := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexBufferedToFiniteStar_edgeIncl n e

/--
[triHexFaceDualInnerActive_bufferedRestrict_outerStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexFaceDualInnerActive_bufferedRestrict_outerStar_eq
  {N n : Nat}
  {rho : ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex (triHexPlanarHexBufferedOuterStarLevel n)))}
-- given
  (hNn : N + 3 ≤ n) :
-- imply
  triHexFaceDualInnerActive N (hexagonal.extendEdge (hexagonal.bufferedRadius n) (ocd_innerRestrict (triHexPlanarHexBufferedToFiniteStar n) rho)) = triHexFaceDualInnerActive N (triHexPlanarFiniteStarExtendEdge (triHexPlanarHexBufferedOuterStarLevel n) rho) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFaceDualInnerActive_bufferedRestrict_outerStar hNn rho

/--
[triHexHexBufferedFaceDualInnerEvent_preimage_outerStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexHexBufferedFaceDualInnerEvent_preimage_outerStar_eq
  {N n : Nat}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hNn : N + 3 ≤ n) :
-- imply
  ocd_innerRestrict (triHexPlanarHexBufferedToFiniteStar n) ⁻¹' triHexHexBufferedFaceDualInnerEvent N n A = triHexStarFaceDualInnerEvent (show N < triHexPlanarHexBufferedOuterStarLevel n by unfold triHexPlanarHexBufferedOuterStarLevel have hn : n ≤ hexagonal.bufferedRadius (n + 1) := (Nat.le_succ n).trans (hexagonal.id_le_bufferedRadius (n + 1)) omega) A := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexHexBufferedFaceDualInnerEvent_preimage_outerStar hNn A

/--
[freeOuterStar_le_triHexHexBufferedFaceDualInnerEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma freeOuterStar_le_triHexHexBufferedFaceDualInnerEvent_eq
  {N n : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hNn : N + 3 ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ rho : ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex (triHexPlanarHexBufferedOuterStarLevel n))), (triHexStarFaceDualInnerEvent (show N < triHexPlanarHexBufferedOuterStarLevel n by unfold triHexPlanarHexBufferedOuterStarLevel have hn : n ≤ hexagonal.bufferedRadius (n + 1) := (Nat.le_succ n).trans (hexagonal.id_le_bufferedRadius (n + 1)) omega) A).indicator (fun _ => (1 : Real)) rho * fkProb (triHexPlanarFiniteStarGraph (triHexPlanarHexBufferedOuterStarLevel n)) p q rho) ≤ ∑ omega, (triHexHexBufferedFaceDualInnerEvent N n A).indicator (fun _ => (1 : Real)) omega * fkProb (hexagonal.bufferedGraph n) p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.freeOuterStar_le_triHexHexBufferedFaceDualInnerEvent hNn hp hp1 hq hA

/--
[triHexFaceDualInnerActive_extend_bufferedRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexFaceDualInnerActive_extend_bufferedRestrict_eq
  {N n : Nat}
  {omega : ConfigSpace (Sym2 HexVertex)}
-- given
  (hNn : N + 3 ≤ n) :
-- imply
  triHexFaceDualInnerActive N (hexagonal.extendEdge (hexagonal.bufferedRadius n) (hexagonal.bufferedRestrict n omega)) = triHexFaceDualInnerActive N omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFaceDualInnerActive_extend_bufferedRestrict hNn omega

/--
[triHexFaceDualInnerEvent_eq_bufferedCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexFaceDualInnerEvent_eq_bufferedCylinder_eq
  {N : Nat}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)} :
-- imply
  triHexFaceDualInnerEvent N A = hexagonal.bufferedCylinder (N + 3) (triHexHexBufferedFaceDualInnerEvent N (N + 3) A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFaceDualInnerEvent_eq_bufferedCylinder N A

/--
[freeBufferedMeasure_real_triHexFaceDualInnerEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma freeBufferedMeasure_real_triHexFaceDualInnerEvent_eq
  {N n : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hNn : N + 3 ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (hexagonal.freeBufferedMeasure n hp hp1 hq : MeasureTheory.Measure (ConfigSpace (Sym2 HexVertex))).real (triHexFaceDualInnerEvent N A) = ∑ rho, (triHexHexBufferedFaceDualInnerEvent N n A).indicator (fun _ => (1 : Real)) rho * fkProb (hexagonal.bufferedGraph n) p q rho := by
-- proof
  apply StatMech.FK.PeriodicPlanar.freeBufferedMeasure_real_triHexFaceDualInnerEvent hNn hp hp1 hq A

/--
[triHexFreeOuterStarFaceDualInnerEvent_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean)
-/
@[path]
private lemma triHexFreeOuterStarFaceDualInnerEvent_tendsto_eq
  {N : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  Filter.Tendsto (fun j => let n := N + 3 + j let m := triHexPlanarHexBufferedOuterStarLevel n ∑ rho : ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex m)), (triHexStarFaceDualInnerEvent (show N < m by dsimp only [m, n] unfold triHexPlanarHexBufferedOuterStarLevel have hn : N + 3 + j ≤ hexagonal.bufferedRadius (N + 3 + j + 1) := (Nat.le_succ (N + 3 + j)).trans (hexagonal.id_le_bufferedRadius (N + 3 + j + 1)) omega) A).indicator (fun _ => (1 : Real)) rho * fkProb (triHexPlanarFiniteStarGraph m) p q rho) Filter.atTop (nhds ((hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 HexVertex))).real (triHexFaceDualInnerEvent N A))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFreeOuterStarFaceDualInnerEvent_tendsto N hp hp1 hq A hA


-- created on 2026-10-23
