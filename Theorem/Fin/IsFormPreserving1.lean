module

public import Mathlib
public import Structure.v1.Atlas.Buildings.code.GeometricAlgebra.CoordinateExamples

public section

open Matrix CoordinateExamples


/--
[isFormPreserving_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CoordinateExamples.lean)
-/
public theorem Fin.IsFormPreserving1
  {m : ℕ}
  [CommRing k]
  {F : Matrix (Fin m) (Fin m) k} :
-- imply
  IsFormPreserving F 1 := by
-- proof
  unfold IsFormPreserving
  simp [Matrix.transpose_one]



-- created on 2026-10-23
-- updated on 2026-10-26
