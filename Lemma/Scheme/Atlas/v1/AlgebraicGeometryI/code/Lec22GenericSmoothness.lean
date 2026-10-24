import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec22GenericSmoothness
open Lec22
open MvPolynomial


namespace Lec22

/--
[veroneseTargetDim_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec22GenericSmoothness.lean)
-/
@[path]
lemma veroneseTargetDim_pos
  {n d : ℕ}
-- given
  (hn : 0 < n)
  (hd : 0 < d) :
-- imply
  0 < veroneseTargetDim n d := by
-- proof
  unfold veroneseTargetDim veroneseMonomialCount
  have h1 : Nat.choose (n + 1) n = n + 1 := Nat.choose_succ_self_right n
  have h2 : Nat.choose (n + 1) n ≤ Nat.choose (n + d) n :=
    Nat.choose_le_choose n (by omega)
  have h3 : Nat.choose (n + d) n = Nat.choose (n + d) d := by
    have := Nat.choose_symm (show n ≤ n + d by omega)
    have hnd : n + d - n = d := by omega
    rw [hnd] at this; exact this.symm
  omega
/-- Corollary 28 (generic smooth hypersurface): Over an algebraically closed field,
a generic degree-`d` hypersurface in `ℙⁿ` is smooth. -/
end Lec22



-- created on 2026-10-23
