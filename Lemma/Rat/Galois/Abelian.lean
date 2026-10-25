import Mathlib
import sympy.Basic
import Theorem.FieldTheory.Galois.Abelian
open scoped IsMulCommutative
open IsAbelianGalois


namespace IsAbelianGalois

/--
[isModularLattice_intermediateField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/Abelian.lean)
-/
@[path]
lemma isModularLattice_intermediateField
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] :
-- imply
  IsModularLattice (IntermediateField K L) := by
-- proof
  have e := IsGalois.intermediateFieldEquivSubgroup (F := K) (E := L)
  constructor
  intro x y z hxz
  have h := IsModularLattice.sup_inf_le_assoc_of_le (e y) (e.le_iff_le.mpr hxz)
  rw [← e.map_sup, ← e.map_inf, ← e.map_inf, ← e.map_sup] at h
  exact e.le_iff_le.mp h

end IsAbelianGalois


-- created on 2026-10-20
-- updated on 2026-10-23
