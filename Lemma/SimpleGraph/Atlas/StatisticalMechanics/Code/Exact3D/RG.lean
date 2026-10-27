import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
open StatMech StatMech.Exact3D StatMech.Exact3D.BlockScale


/--
[toReal_gt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RG.lean)
-/
@[path]
private lemma toReal_gt_one_eq
  {s : BlockScale} :
-- imply
  1 < s.toReal := by
-- proof
  apply StatMech.Exact3D.BlockScale.toReal_gt_one s

/--
[toReal_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RG.lean)
-/
@[path]
private lemma toReal_pos_eq
  {s : BlockScale} :
-- imply
  0 < s.toReal := by
-- proof
  apply StatMech.Exact3D.BlockScale.toReal_pos s

/--
[L_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RG.lean)
-/
@[path]
private lemma L_ne_zero_eq
  {s : BlockScale} :
-- imply
  s.L ≠ 0 := by
-- proof
  apply StatMech.Exact3D.BlockScale.L_ne_zero s

/--
[tendsto_mul_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RG.lean)
-/
@[path]
private lemma tendsto_mul_atTop_eq
  {s : BlockScale} :
-- imply
  Filter.Tendsto (fun n : ℕ => s.L * n) Filter.atTop Filter.atTop := by
-- proof
  apply StatMech.Exact3D.BlockScale.tendsto_mul_atTop s

/--
[HasInverseCorrelationLength.rescale_blockScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RG.lean)
-/
@[path]
private lemma rescale_blockScale_eq
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {m : ℝ}
  {scale : BlockScale}
-- given
  (h : HasInverseCorrelationLength M β origin ray m) :
-- imply
  HasInverseCorrelationLength M β origin (fun n => ray (scale.L * n)) (scale.toReal * m) := by
-- proof
  apply StatMech.Exact3D.HasInverseCorrelationLength.rescale_blockScale scale h

/--
[HasCorrelationLength.rescale_blockScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RG.lean)
-/
@[path]
private lemma rescale_blockScale_eq_2
  {M : CriticalModel ι}
  {β : ℝ}
  {origin : ι}
  {ray : ℕ → ι}
  {ξ : ℝ}
  {scale : BlockScale}
-- given
  (h : HasCorrelationLength M β origin ray ξ) :
-- imply
  HasCorrelationLength M β origin (fun n => ray (scale.L * n)) (ξ / scale.toReal) := by
-- proof
  apply StatMech.Exact3D.HasCorrelationLength.rescale_blockScale scale h


-- created on 2026-10-23
