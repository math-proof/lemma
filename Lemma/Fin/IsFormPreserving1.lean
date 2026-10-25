import Mathlib
import sympy.Basic
import Structure.v1.Atlas.Buildings.code.GeometricAlgebra.CoordinateExamples
open Matrix CoordinateExamples


/--
[isFormPreserving_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CoordinateExamples.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  [CommRing k]
  {F : Matrix (Fin m) (Fin m) k} :
-- imply
  IsFormPreserving F 1 := by
-- proof
  unfold IsFormPreserving
  simp [Matrix.transpose_one]



-- created on 2026-10-23
-- updated on 2026-10-24
