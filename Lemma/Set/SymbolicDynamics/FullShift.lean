import Mathlib
import sympy.Basic
import Def.Dynamics.SymbolicDynamics.FullShift
open SymbolicDynamics.FullShift


namespace SymbolicDynamics.FullShift

/--
[unitShift_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean)
-/
@[path]
lemma unitShift_apply
  {N : ℕ}
  {x : FullShiftSpace N}
  {i : ℤ} :
-- imply
  unitShift N x i = x (1 + i) :=
-- proof
  rfl

end SymbolicDynamics.FullShift

namespace SymbolicDynamics.FullShift

/--
[shiftHomeomorph_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean)
-/
@[path]
lemma shiftHomeomorph_apply
  {N : ℕ}
  {x : FullShiftSpace N} :
-- imply
  shiftHomeomorph N x = unitShift N x :=
-- proof
  rfl

end SymbolicDynamics.FullShift

namespace SymbolicDynamics.FullShift

/--
[shiftHomeomorph_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean)
-/
@[path]
lemma shiftHomeomorph_symm_apply
  {N : ℕ}
  {x : FullShiftSpace N}
  {i : ℤ} :
-- imply
  (shiftHomeomorph N).symm x i = x (-1 + i) :=
-- proof
  rfl

end SymbolicDynamics.FullShift

namespace SymbolicDynamics.FullShift

/--
[isOneDimensionalCA_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean)
-/
@[path]
lemma isOneDimensionalCA_iff
  {N : ℕ}
  {f : FullShiftSpace N → FullShiftSpace N} :
-- imply
  IsOneDimensionalCA N f ↔ Continuous f ∧ Function.Commute f (unitShift N) :=
-- proof
  Iff.rfl

end SymbolicDynamics.FullShift

namespace SymbolicDynamics.FullShift

/--
[mem_jointlyPeriodicPoints](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/SymbolicDynamics/FullShift.lean)
-/
@[path]
lemma mem_jointlyPeriodicPoints
  {N : ℕ}
  {f : FullShiftSpace N → FullShiftSpace N}
  {x : FullShiftSpace N} :
-- imply
  x ∈ jointlyPeriodicPoints N f ↔
      x ∈ Function.periodicPts f ∧ x ∈ Function.periodicPts (unitShift N) :=
-- proof
  Iff.rfl

end SymbolicDynamics.FullShift


-- created on 2026-10-20
-- updated on 2026-10-23
