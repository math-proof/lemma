import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorOrientedSplit
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexSector_forwardInterlaced_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientedSplit.lean)
-/
@[path]
private lemma sixVertexSector_forwardInterlaced_refl_eq
  {N n : Nat}
  {x : SixVertexSector N n} :
-- imply
  SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow x) := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_forwardInterlaced_refl x

/--
[sixVertexSector_forwardInterlaced_antisymm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientedSplit.lean)
-/
@[path]
private lemma sixVertexSector_forwardInterlaced_antisymm_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
-- given
  (hxy : SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y))
  (hyx : SixVertexForwardInterlaced (sixVertexSectorRow y) (sixVertexSectorRow x)) :
-- imply
  x = y := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_forwardInterlaced_antisymm x y hxy hyx

/--
[sixVertexSectorTransfer_eq_forward_add_transpose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientedSplit.lean)
-/
@[path]
private lemma sixVertexSectorTransfer_eq_forward_add_transpose_eq
  {N n : Nat}
  {c : Real} :
-- imply
  sixVertexSectorTransfer N n c = sixVertexSectorForwardTransfer N n c + (sixVertexSectorForwardTransfer N n c)ᵀ := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransfer_eq_forward_add_transpose N n c

/--
[sixVertexSectorForwardTransfer_transpose_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientedSplit.lean)
-/
@[path]
private lemma sixVertexSectorForwardTransfer_transpose_apply_eq
  {N n : Nat}
  {c : Real}
  {x y : SixVertexSector N n} :
-- imply
  (sixVertexSectorForwardTransfer N n c)ᵀ x y = if SixVertexForwardInterlaced (sixVertexSectorRow y) (sixVertexSectorRow x) then c ^ sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorForwardTransfer_transpose_apply N n c x y


-- created on 2026-10-23
