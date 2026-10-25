/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean -/

import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Def.Combinatorics.Order.ErdosSzekeres


namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/-- Classical decidability for filtering positions by `IsIncrEnd`. -/
noncomputable instance decIncrEnd (N : ℕ) (f : Fin N → ℝ) (p : Fin N) :
    DecidablePred (IsIncrEnd f p) :=
  fun _ => Classical.propDecidable _

/-- Classical decidability for filtering positions by `IsDecrEnd`. -/
noncomputable instance decDecrEnd (N : ℕ) (f : Fin N → ℝ) (p : Fin N) :
    DecidablePred (IsDecrEnd f p) :=
  fun _ => Classical.propDecidable _

end MathlibExt.Combinatorics.Order.ErdosSzekeres
