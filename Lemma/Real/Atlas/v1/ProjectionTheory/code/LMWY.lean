import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.LMWY
open Matrix HomogeneousDynamics


/--
[unipotentU_det](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LMWY.lean)
-/
@[path]
private lemma unipotentU_det_eq
  {t : ℝ} :
-- imply
  (unipotentU t).det = 1 := by
-- proof
  apply HomogeneousDynamics.unipotentU_det t


-- created on 2026-10-23
