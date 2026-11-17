/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean -/

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Real.Basic
public import Def.Combinatorics.Order.ErdosSzekeres

@[expose] public section

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
