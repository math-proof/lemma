import Mathlib
import sympy.Basic
import sympy.atlas.Dynamics.SymbolicDynamics.FullShift
open SymbolicDynamics.FullShift


/--
[unitShift_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean)
-/
@[path]
private lemma unitShift_apply_eq
  {N : ℕ}
  {x : FullShiftSpace N}
  {i : ℤ} :
-- imply
  unitShift N x i = x (1 + i) := by
-- proof
  apply SymbolicDynamics.FullShift.unitShift_apply N x i

/--
[shiftHomeomorph_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean)
-/
@[path]
private lemma shiftHomeomorph_apply_eq
  {N : ℕ}
  {x : FullShiftSpace N} :
-- imply
  shiftHomeomorph N x = unitShift N x := by
-- proof
  apply SymbolicDynamics.FullShift.shiftHomeomorph_apply N x

/--
[shiftHomeomorph_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean)
-/
@[path]
private lemma shiftHomeomorph_symm_apply_eq
  {N : ℕ}
  {x : FullShiftSpace N}
  {i : ℤ} :
-- imply
  (shiftHomeomorph N).symm x i = x (-1 + i) := by
-- proof
  apply SymbolicDynamics.FullShift.shiftHomeomorph_symm_apply N x i

/--
[isOneDimensionalCA_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean)
-/
@[path]
private lemma isOneDimensionalCA_iff_eq
  {N : ℕ}
  {f : FullShiftSpace N → FullShiftSpace N} :
-- imply
  IsOneDimensionalCA N f ↔ Continuous f ∧ Function.Commute f (unitShift N) := by
-- proof
  apply SymbolicDynamics.FullShift.isOneDimensionalCA_iff N f

/--
[mem_jointlyPeriodicPoints](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean)
-/
@[path]
private lemma mem_jointlyPeriodicPoints_eq
  {N : ℕ}
  {f : FullShiftSpace N → FullShiftSpace N}
  {x : FullShiftSpace N} :
-- imply
  x ∈ jointlyPeriodicPoints N f ↔
      x ∈ Function.periodicPts f ∧ x ∈ Function.periodicPts (unitShift N) := by
-- proof
  apply SymbolicDynamics.FullShift.mem_jointlyPeriodicPoints N f x


-- created on 2026-10-20
