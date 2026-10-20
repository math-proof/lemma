import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.Galois.Abelian
open scoped IsMulCommutative
open IsAbelianGalois


/--
[isModularLattice_intermediateField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/Abelian.lean)
-/
@[path]
private lemma isModularLattice_intermediateField_eq
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] :
-- imply
  IsModularLattice (IntermediateField K L) := by
-- proof
  apply IsAbelianGalois.isModularLattice_intermediateField


-- created on 2026-10-20
