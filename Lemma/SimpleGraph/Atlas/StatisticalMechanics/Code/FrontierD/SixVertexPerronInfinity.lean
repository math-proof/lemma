import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexPerronInfinity
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexNoAdjacentTransferInfinity_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexNoAdjacentTransferInfinity_isHermitian_eq
  {N n : Nat} :
-- imply
  (sixVertexNoAdjacentTransferInfinity N n).IsHermitian := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentTransferInfinity_isHermitian N n

/--
[sixVertexNoAdjacentInfinityTopEigenvalue_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinityTopEigenvalue_ge_eq
  {N n : Nat}
  {i : Fin (Fintype.card (SixVertexNoAdjacentSector N n))}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  (sixVertexNoAdjacentTransferInfinity_isHermitian N n).eigenvalues₀ i ≤ sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinityTopEigenvalue_ge N n hn hhalf i

/--
[sixVertexNoAdjacentInfinityTop_hasEigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinityTop_hasEigenvalue_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n)) (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf) := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinityTop_hasEigenvalue N n hn hhalf

/--
[sixVertexNoAdjacentInfinityTop_exists_nonnegative_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinityTop_exists_nonnegative_eigenvector_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  ∃ v : EuclideanSpace Real (SixVertexNoAdjacentSector N n), v ≠ 0 ∧ (∀ i, 0 ≤ v i) ∧ sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i) = sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf • (fun i => v i) := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinityTop_exists_nonnegative_eigenvector hn hhalf

/--
[sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  ∃ v : EuclideanSpace Real (SixVertexNoAdjacentSector N n), (∀ i, 0 < v i) ∧ sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i) = sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf • (fun i => v i) := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf

/--
[sixVertexNoAdjacentInfinityTopEigenvalue_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinityTopEigenvalue_pos_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  0 < sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinityTopEigenvalue_pos hn hhalf

/--
[sixVertexNoAdjacentInfinityTop_eigenspace_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinityTop_eigenspace_finrank_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  Module.finrank Real (Module.End.eigenspace (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n)) (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf)) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinityTop_eigenspace_finrank hn hhalf

/--
[sixVertexNoAdjacentInfinityTop_isSimplePerron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinityTop_isSimplePerron_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  0 < sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf ∧ (∃ v : EuclideanSpace Real (SixVertexNoAdjacentSector N n), (∀ i, 0 < v i) ∧ sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i) = sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf • (fun i => v i)) ∧ Module.finrank Real (Module.End.eigenspace (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n)) (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf)) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinityTop_isSimplePerron hn hhalf

/--
[sixVertexFulmekPerronBound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexFulmekPerronBound_pos_eq
  {n r : Nat}
-- given
  (hn : 0 < n) :
-- imply
  0 < sixVertexFulmekPerronBound n r := by
-- proof
  apply StatMech.FrontierD.sixVertexFulmekPerronBound_pos hn

/--
[sixVertexNoAdjacentInfinityTop_le_of_positive_supersolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinityTop_le_of_positive_supersolution_eq
  {N n : Nat}
  {R : Real}
  {q : SixVertexNoAdjacentSector N n → Real}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N)
  (hqpos : ∀ i, 0 < q i)
  (hq : ∀ i, (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) i ≤ R * q i) :
-- imply
  sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf ≤ R := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinityTop_le_of_positive_supersolution hn hhalf q hqpos hq

/--
[sixVertexNoAdjacentZeroExtend_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexNoAdjacentZeroExtend_apply_eq
  {N n : Nat}
  {q : SixVertexNoAdjacentSector N n → Real}
  {x : SixVertexNoAdjacentSector N n} :
-- imply
  sixVertexNoAdjacentZeroExtend q x.1 = q x := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentZeroExtend_apply q x

/--
[sixVertexSectorTransferInfinity_mulVec_zeroExtend_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_mulVec_zeroExtend_apply_eq
  {N n : Nat}
  {q : SixVertexNoAdjacentSector N n → Real}
  {x : SixVertexSector N n}
-- given
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  (sixVertexSectorTransferInfinity N n *ᵥ sixVertexNoAdjacentZeroExtend q) x = (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) ⟨x, hx⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_mulVec_zeroExtend_apply q x hx

/--
[sixVertexSectorTransferInfinity_mulVec_zeroExtend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_mulVec_zeroExtend_eq
  {N n : Nat}
  {q : SixVertexNoAdjacentSector N n → Real} :
-- imply
  sixVertexSectorTransferInfinity N n *ᵥ sixVertexNoAdjacentZeroExtend q = sixVertexNoAdjacentZeroExtend (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_mulVec_zeroExtend q

/--
[sixVertexSectorTransferInfinity_exists_Perron_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_exists_Perron_eigenvector_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  ∃ v : EuclideanSpace Real (SixVertexSector N n), v ≠ 0 ∧ (sixVertexSectorTransferInfinity N n *ᵥ (fun i ↦ v i) = sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf • (fun i ↦ v i)) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_exists_Perron_eigenvector hn hhalf

/--
[sixVertexSectorTransferInfinity_Perron_eigenspace_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_Perron_eigenspace_finrank_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  Module.finrank Real (Module.End.eigenspace (Matrix.toEuclideanLin (sixVertexSectorTransferInfinity N n)) (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf)) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_Perron_eigenspace_finrank hn hhalf

/--
[sixVertexSectorTransferInfinity_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_isHermitian_eq
  {N n : Nat} :
-- imply
  (sixVertexSectorTransferInfinity N n).IsHermitian := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_isHermitian N n

/--
[sixVertexSectorInfinityTopEigenvalue_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexSectorInfinityTopEigenvalue_ge_eq
  {N n : Nat}
  {i : Fin (Fintype.card (SixVertexSector N n))}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  (sixVertexSectorTransferInfinity_isHermitian N n).eigenvalues₀ i ≤ sixVertexSectorInfinityTopEigenvalue N n hn hhalf := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorInfinityTopEigenvalue_ge N n hn hhalf i

/--
[sixVertexSectorInfinityTop_hasEigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexSectorInfinityTop_hasEigenvalue_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  Module.End.HasEigenvalue (Matrix.toEuclideanLin (sixVertexSectorTransferInfinity N n)) (sixVertexSectorInfinityTopEigenvalue N n hn hhalf) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorInfinityTop_hasEigenvalue N n hn hhalf

/--
[sixVertexSectorInfinityTop_le_of_positive_supersolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexSectorInfinityTop_le_of_positive_supersolution_eq
  {N n : Nat}
  {R : Real}
  {q : SixVertexSector N n → Real}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N)
  (hqpos : ∀ i, 0 < q i)
  (hq : ∀ i, (sixVertexSectorTransferInfinity N n *ᵥ q) i ≤ R * q i) :
-- imply
  sixVertexSectorInfinityTopEigenvalue N n hn hhalf ≤ R := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorInfinityTop_le_of_positive_supersolution hn hhalf q hqpos hq

/--
[sixVertexSectorInfinityTopEigenvalue_eq_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexSectorInfinityTopEigenvalue_eq_noAdjacent_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  sixVertexSectorInfinityTopEigenvalue N n hn hhalf = sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorInfinityTopEigenvalue_eq_noAdjacent hn hhalf

/--
[sixVertexSectorInfinityTop_isSimplePerron](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean)
-/
@[path]
private lemma sixVertexSectorInfinityTop_isSimplePerron_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  0 < sixVertexSectorInfinityTopEigenvalue N n hn hhalf ∧ Module.finrank Real (Module.End.eigenspace (Matrix.toEuclideanLin (sixVertexSectorTransferInfinity N n)) (sixVertexSectorInfinityTopEigenvalue N n hn hhalf)) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorInfinityTop_isSimplePerron hn hhalf


-- created on 2026-10-23
