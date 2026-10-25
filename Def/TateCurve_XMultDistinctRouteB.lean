import Mathlib
import Structure.TateCurve_XMultAlignment
import Theorems.Thm_TateCurve_pointY_inv
import Theorems.Thm_TateCurve_pointY_zpow_mul
import Theorems.Thm_TateCurve_pointX_qExpansion

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WeierstrassCurve

section Bezout

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def bezF (x : F) : F :=
  (8 * W.b₂ ^ 3 * W.b₆ - 8 * W.b₂ ^ 2 * W.b₄ ^ 2 + 16 * W.b₂ ^ 2 * W.b₈ -
      336 * W.b₂ * W.b₄ * W.b₆ + 288 * W.b₄ ^ 3 - 384 * W.b₄ * W.b₈ + 1296 * W.b₆ ^ 2) * x ^ 2 +
    (2 * W.b₂ ^ 4 * W.b₆ - 2 * W.b₂ ^ 3 * W.b₄ ^ 2 - 80 * W.b₂ ^ 2 * W.b₄ * W.b₆ +
      72 * W.b₂ * W.b₄ ^ 3 + 32 * W.b₂ * W.b₄ * W.b₈ + 360 * W.b₂ * W.b₆ ^ 2 -
      144 * W.b₄ ^ 2 * W.b₆ - 576 * W.b₆ * W.b₈) * x +
    (-W.b₂ ^ 4 * W.b₈ + 5 * W.b₂ ^ 3 * W.b₄ * W.b₆ - 4 * W.b₂ ^ 2 * W.b₄ ^ 3 +
      48 * W.b₂ ^ 2 * W.b₄ * W.b₈ + W.b₂ ^ 2 * W.b₆ ^ 2 - 204 * W.b₂ * W.b₄ ^ 2 * W.b₆ -
      176 * W.b₂ * W.b₆ * W.b₈ + 144 * W.b₄ ^ 4 - 384 * W.b₄ ^ 2 * W.b₈ +
      864 * W.b₄ * W.b₆ ^ 2 + 256 * W.b₈ ^ 2)

def bezG (x : F) : F :=
  (-2 * W.b₂ ^ 3 * W.b₆ + 2 * W.b₂ ^ 2 * W.b₄ ^ 2 - 4 * W.b₂ ^ 2 * W.b₈ +
      84 * W.b₂ * W.b₄ * W.b₆ - 72 * W.b₄ ^ 3 + 96 * W.b₄ * W.b₈ - 324 * W.b₆ ^ 2) * x ^ 3 +
    (W.b₂ ^ 3 * W.b₈ - W.b₂ ^ 2 * W.b₄ * W.b₆ - 32 * W.b₂ * W.b₄ * W.b₈ - 9 * W.b₂ * W.b₆ ^ 2 +
      36 * W.b₄ ^ 2 * W.b₆ + 144 * W.b₆ * W.b₈) * x ^ 2 +
    (2 * W.b₂ ^ 3 * W.b₄ * W.b₆ - 2 * W.b₂ ^ 2 * W.b₄ ^ 3 + 2 * W.b₂ ^ 2 * W.b₄ * W.b₈ +
      2 * W.b₂ ^ 2 * W.b₆ ^ 2 - 84 * W.b₂ * W.b₄ ^ 2 * W.b₆ + 8 * W.b₂ * W.b₆ * W.b₈ +
      72 * W.b₄ ^ 4 - 48 * W.b₄ ^ 2 * W.b₈ + 270 * W.b₄ * W.b₆ ^ 2 - 64 * W.b₈ ^ 2) * x +
    (-W.b₂ ^ 3 * W.b₄ * W.b₈ + 4 * W.b₂ ^ 3 * W.b₆ ^ 2 - 3 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ +
      7 * W.b₂ ^ 2 * W.b₆ * W.b₈ + 36 * W.b₂ * W.b₄ ^ 2 * W.b₈ - 162 * W.b₂ * W.b₄ * W.b₆ ^ 2 +
      16 * W.b₂ * W.b₈ ^ 2 + 108 * W.b₄ ^ 3 * W.b₆ - 432 * W.b₄ * W.b₆ * W.b₈ +
      729 * W.b₆ ^ 3)

end Bezout

end WeierstrassCurve


set_option linter.unusedSectionVars false

open WeierstrassCurve.Affine
open Polynomial
open IsUltrametricDist

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v : K}

section Factorization

noncomputable def xPairNum (u v : K) (d : ℕ) : K :=
  (d : K) * (∑ k ∈ Finset.range d, u ^ k * v ^ (d - 1 - k)) *
    (∑ j ∈ Finset.range d, (u * v) ^ j)

noncomputable def xPairCoeff (u v : K) (M : ℕ) : K :=
  (∑ d ∈ M.divisors, xPairNum u v d * (u * v) ^ (M - d)) / (u * v) ^ M

end Factorization

end TateCurve
