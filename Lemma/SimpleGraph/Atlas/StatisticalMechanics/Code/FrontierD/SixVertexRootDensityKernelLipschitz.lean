import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRootDensityKernelLipschitz
open StatMech StatMech.FrontierD


/--
[sixVertexRootDensityKernelLipschitzBound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRootDensityKernelLipschitz.lean)
-/
@[path]
private lemma sixVertexRootDensityKernelLipschitzBound_pos_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexRootDensityKernelLipschitzBound c := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernelLipschitzBound_pos hc

/--
[sixVertexRootDensityKernel_lipschitz_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRootDensityKernelLipschitz.lean)
-/
@[path]
private lemma sixVertexRootDensityKernel_lipschitz_left_eq
  {c : Real}
  {x z y : Real}
-- given
  (hc : 2 < c) :
-- imply
  |sixVertexRootDensityKernel c x y - sixVertexRootDensityKernel c z y| <= sixVertexRootDensityKernelLipschitzBound c * |x - z| := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernel_lipschitz_left hc x z y

/--
[sixVertexRootDensityKernel_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRootDensityKernelLipschitz.lean)
-/
@[path]
private lemma sixVertexRootDensityKernel_swap_eq
  {c x y : Real} :
-- imply
  sixVertexRootDensityKernel c x y = sixVertexRootDensityKernel c y x := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernel_swap c x y

/--
[sixVertexRootDensityKernel_lipschitz_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRootDensityKernelLipschitz.lean)
-/
@[path]
private lemma sixVertexRootDensityKernel_lipschitz_right_eq
  {c : Real}
  {x y z : Real}
-- given
  (hc : 2 < c) :
-- imply
  |sixVertexRootDensityKernel c x y - sixVertexRootDensityKernel c x z| <= sixVertexRootDensityKernelLipschitzBound c * |y - z| := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernel_lipschitz_right hc x y z


-- created on 2026-10-23
