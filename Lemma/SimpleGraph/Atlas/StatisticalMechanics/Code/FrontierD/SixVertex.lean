import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertex
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexUpPositions_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexUpPositions_length_eq
  {N : ℕ}
  {x : SixVertexRow N} :
-- imply
  (sixVertexUpPositions x).length = sixVertexUpCount x := by
-- proof
  apply StatMech.FrontierD.sixVertexUpPositions_length x

/--
[sixVertexInterlaced_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexInterlaced_comm_eq
  {N : ℕ}
  {x y : SixVertexRow N} :
-- imply
  SixVertexInterlaced x y ↔ SixVertexInterlaced y x := by
-- proof
  apply StatMech.FrontierD.sixVertexInterlaced_comm x y

/--
[sixVertexInterlaced_upCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexInterlaced_upCount_eq_eq
  {N : ℕ}
  {x y : SixVertexRow N}
-- given
  (h : SixVertexInterlaced x y) :
-- imply
  sixVertexUpCount x = sixVertexUpCount y := by
-- proof
  apply StatMech.FrontierD.sixVertexInterlaced_upCount_eq h

/--
[sixVertexRowDistance_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexRowDistance_comm_eq
  {N : ℕ}
  {x y : SixVertexRow N} :
-- imply
  sixVertexRowDistance x y = sixVertexRowDistance y x := by
-- proof
  apply StatMech.FrontierD.sixVertexRowDistance_comm x y

/--
[sixVertexTransfer_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexTransfer_apply_eq
  {N : ℕ}
  {c : ℝ}
  {x y : SixVertexRow N} :
-- imply
  sixVertexTransfer N c x y = if x = y then 2 else if SixVertexInterlaced x y then c ^ sixVertexRowDistance x y else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexTransfer_apply N c x y

/--
[sixVertexTransfer_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexTransfer_symmetric_eq
  {N : ℕ}
  {c : ℝ}
  {x y : SixVertexRow N} :
-- imply
  sixVertexTransfer N c x y = sixVertexTransfer N c y x := by
-- proof
  apply StatMech.FrontierD.sixVertexTransfer_symmetric N c x y

/--
[sixVertexTransfer_eq_zero_of_upCount_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexTransfer_eq_zero_of_upCount_ne_eq
  {N : ℕ}
  {c : ℝ}
  {x y : SixVertexRow N}
-- given
  (hxy : sixVertexUpCount x ≠ sixVertexUpCount y) :
-- imply
  sixVertexTransfer N c x y = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexTransfer_eq_zero_of_upCount_ne c hxy

/--
[sixVertexTransfer_preserves_upCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexTransfer_preserves_upCount_eq
  {N : ℕ}
  {c : ℝ}
  {x y : SixVertexRow N}
-- given
  (h : sixVertexTransfer N c x y ≠ 0) :
-- imply
  sixVertexUpCount x = sixVertexUpCount y := by
-- proof
  apply StatMech.FrontierD.sixVertexTransfer_preserves_upCount c h

/--
[sixVertexTransfer_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexTransfer_nonneg_eq
  {N : ℕ}
  {c : ℝ}
  {x y : SixVertexRow N}
-- given
  (hc : 0 ≤ c) :
-- imply
  0 ≤ sixVertexTransfer N c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexTransfer_nonneg hc x y

/--
[sixVertexSectorRow_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexSectorRow_apply_eq
  {N n : ℕ}
  {x : SixVertexSector N n}
  {i : Fin N} :
-- imply
  sixVertexSectorRow x i = decide (i ∈ (x : Finset (Fin N))) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorRow_apply x i

/--
[sixVertexSectorRow_upCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexSectorRow_upCount_eq
  {N n : ℕ}
  {x : SixVertexSector N n} :
-- imply
  sixVertexUpCount (sixVertexSectorRow x) = n := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorRow_upCount x

/--
[sixVertexSectorRow_upPositions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexSectorRow_upPositions_eq
  {N n : ℕ}
  {x : SixVertexSector N n} :
-- imply
  sixVertexUpPositions (sixVertexSectorRow x) = (x : Finset (Fin N)).sort (· ≤ ·) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorRow_upPositions x

/--
[sixVertexSectorTransfer_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_isHermitian_eq
  {N n : ℕ}
  {c : ℝ} :
-- imply
  (sixVertexSectorTransfer N n c).IsHermitian := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_isHermitian N n c

/--
[sixVertexSector_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexSector_nonempty_eq
  {N n : ℕ}
-- given
  (hn : n ≤ N) :
-- imply
  Nonempty (SixVertexSector N n) := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_nonempty hn

/--
[sixVertexSectorTopEigenvalue_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexSectorTopEigenvalue_ge_eq
  {N n : ℕ}
  {c : ℝ}
  {i : Fin (Fintype.card (SixVertexSector N n))}
-- given
  (hn : n ≤ N) :
-- imply
  (sixVertexSectorTransfer_isHermitian N n c).eigenvalues₀ i ≤ sixVertexSectorTopEigenvalue N n hn c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTopEigenvalue_ge N n hn c i

/--
[sixVertexSectorTop_hasEigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean)
-/
@[path]
private lemma sixVertexSectorTop_hasEigenvalue_eq
  {N n : ℕ}
  {c : ℝ}
-- given
  (hn : n ≤ N) :
-- imply
  Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)) (sixVertexSectorTopEigenvalue N n hn c) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTop_hasEigenvalue N n hn c


-- created on 2026-10-23
