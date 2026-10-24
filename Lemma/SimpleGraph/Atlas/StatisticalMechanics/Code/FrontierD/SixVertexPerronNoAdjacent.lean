import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexPerronNoAdjacent
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexSectorNoAdjacent_position_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean)
-/
@[path]
private lemma sixVertexSectorNoAdjacent_position_lower_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {k : Nat}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hk : k < n) :
-- imply
  (sixVertexSectorPosition x ⟨0, by omega⟩).val + 2 * k ≤ (sixVertexSectorPosition x ⟨k, hk⟩).val := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorNoAdjacent_position_lower x hx k hk

/--
[sixVertexSectorNoAdjacent_position_add_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean)
-/
@[path]
private lemma sixVertexSectorNoAdjacent_position_add_lower_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {k m : Nat}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hkm : k + m < n) :
-- imply
  (sixVertexSectorPosition x ⟨k, by omega⟩).val + 2 * m ≤ (sixVertexSectorPosition x ⟨k + m, hkm⟩).val := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorNoAdjacent_position_add_lower x hx k m hkm

/--
[sixVertexSectorNoAdjacent_twice_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean)
-/
@[path]
private lemma sixVertexSectorNoAdjacent_twice_le_eq
  {N n : Nat}
  {x : SixVertexSector N n}
-- given
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  2 * n ≤ N := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorNoAdjacent_twice_le x hx

/--
[sixVertexSectorNoAdjacent_position_eq_of_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean)
-/
@[path]
private lemma sixVertexSectorNoAdjacent_position_eq_of_half_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {k : Fin n}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hn : 0 < n)
  (hhalf : 2 * n = N) :
-- imply
  (sixVertexSectorPosition x k).val = (sixVertexSectorPosition x ⟨0, hn⟩).val + 2 * k.val := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorNoAdjacent_position_eq_of_half x hx hn hhalf k

/--
[sixVertexSectorNoAdjacent_eq_alternating_of_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean)
-/
@[path]
private lemma sixVertexSectorNoAdjacent_eq_alternating_of_half_eq
  {N n : Nat}
  {x : SixVertexSector N n}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hn : 0 < n)
  (hhalf : 2 * n = N) :
-- imply
  x = sixVertexAlternatingEvenSector N n hhalf.le ∨ x = sixVertexAlternatingOddSector N n hhalf.le := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorNoAdjacent_eq_alternating_of_half x hx hn hhalf

/--
[sixVertexInfinityGraph_adj_twice_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_adj_twice_le_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
-- given
  (hxy : (sixVertexInfinityGraph N n).Adj x y) :
-- imply
  2 * n ≤ N := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_adj_twice_le hxy

/--
[sixVertexInfinityGraph_adj_alternating_of_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_adj_alternating_of_half_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N) :
-- imply
  (sixVertexInfinityGraph N n).Adj (sixVertexAlternatingEvenSector N n hhalf.le) (sixVertexAlternatingOddSector N n hhalf.le) := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_adj_alternating_of_half hn hhalf

/--
[sixVertexInfinityGraph_adj_iff_alternating_of_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_adj_iff_alternating_of_half_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N) :
-- imply
  (sixVertexInfinityGraph N n).Adj x y ↔ (x = sixVertexAlternatingEvenSector N n hhalf.le ∧ y = sixVertexAlternatingOddSector N n hhalf.le) ∨ (x = sixVertexAlternatingOddSector N n hhalf.le ∧ y = sixVertexAlternatingEvenSector N n hhalf.le) := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_adj_iff_alternating_of_half hn hhalf x y

/--
[sixVertexSectorTransferInfinity_apply_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_apply_half_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N) :
-- imply
  sixVertexSectorTransferInfinity N n x y = if (x = sixVertexAlternatingEvenSector N n hhalf.le ∧ y = sixVertexAlternatingOddSector N n hhalf.le) ∨ (x = sixVertexAlternatingOddSector N n hhalf.le ∧ y = sixVertexAlternatingEvenSector N n hhalf.le) then 1 else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_apply_half hn hhalf x y

/--
[sixVertexSectorTransferInfinity_mulVec_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_mulVec_half_eq
  {N n : Nat}
  {v : SixVertexSector N n → Real}
  {x : SixVertexSector N n}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N) :
-- imply
  (sixVertexSectorTransferInfinity N n *ᵥ v) x = if x = sixVertexAlternatingEvenSector N n hhalf.le then v (sixVertexAlternatingOddSector N n hhalf.le) else if x = sixVertexAlternatingOddSector N n hhalf.le then v (sixVertexAlternatingEvenSector N n hhalf.le) else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_mulVec_half hn hhalf v x

/--
[sixVertexHalfFilledTransferInfinityVector_eigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean)
-/
@[path]
private lemma sixVertexHalfFilledTransferInfinityVector_eigenrelation_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N) :
-- imply
  sixVertexSectorTransferInfinity N n *ᵥ sixVertexHalfFilledTransferInfinityVector N n hhalf = sixVertexHalfFilledTransferInfinityVector N n hhalf := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledTransferInfinityVector_eigenrelation hn hhalf

/--
[sixVertexSectorTransferInfinity_eigenvector_one_eq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronNoAdjacent.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_eigenvector_one_eq_smul_eq
  {N n : Nat}
  {v : SixVertexSector N n → Real}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N)
  (hv : sixVertexSectorTransferInfinity N n *ᵥ v = v) :
-- imply
  v = v (sixVertexAlternatingEvenSector N n hhalf.le) • sixVertexHalfFilledTransferInfinityVector N n hhalf := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_eigenvector_one_eq_smul hn hhalf v hv


-- created on 2026-10-23
