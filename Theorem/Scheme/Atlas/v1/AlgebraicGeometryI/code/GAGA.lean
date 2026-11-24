module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology


public section

namespace GAGA

/--
[P1_gaga_algebraic_side](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GAGA.lean)
-/
@[path]
theorem P1_gaga_algebraic_side
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  (Module.finrank k (SheafCohomology.H0 k n) : ℤ) - (Module.finrank k (SheafCohomology.H1 k n) : ℤ) = n + 1 :=
-- proof
  SheafCohomology.euler_characteristic k n

end GAGA


-- created on 2026-10-23
