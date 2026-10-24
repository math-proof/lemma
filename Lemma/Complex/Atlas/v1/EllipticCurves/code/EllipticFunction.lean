import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.EllipticFunction
open Complex ComplexLattice


namespace ComplexLattice

/--
[periodic_int_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EllipticFunction.lean)
-/
@[path]
lemma periodic_int_mul
  {L : ComplexLattice}
  {f : ℂ → ℂ}
  {ω : ℂ}
  {n : ℤ}
  {w : ℂ}
-- given
  (h : ∀ w, f (w + ω) = f w) :
-- imply
  f (w + ↑n * ω) = f w := by
-- proof
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    suffices f ((w + (↑↑k : ℂ) * ω) + ω) = f w by
      convert this using 2; push_cast; ring
    rw [h]; exact ih
  | pred k ih =>
    suffices f ((w + (↑(-↑k : ℤ) : ℂ) * ω) - ω) = f w by
      convert this using 2; push_cast; ring
    have hminus : ∀ u, f (u - ω) = f u := fun u => by
      have := (h (u - ω)).symm; rwa [sub_add_cancel] at this
    rw [hminus]; exact ih

end ComplexLattice

namespace ComplexLattice

/--
[isLatticePeriodic_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EllipticFunction.lean)
-/
@[path]
lemma isLatticePeriodic_const
  {L : ComplexLattice}
  {L}
  {c : ℂ} :
-- imply
  L.IsLatticePeriodic (fun _ => c) :=
-- proof
  fun _ _ _ => rfl

end ComplexLattice

/--
[polesInFundParallelogram_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EllipticFunction.lean)
-/
@[path]
private lemma polesInFundParallelogram_finite_eq
  {L : ComplexLattice}
  {L}
  (L)
  {f : ℂ → ℂ}
  {α : ℂ}
-- given
  (hf : L.IsEllipticFunction f) :
-- imply
  Set.Finite (L.polesInFundParallelogram f α) := by
-- proof
  apply ComplexLattice.polesInFundParallelogram_finite L hf α


-- created on 2026-10-23
