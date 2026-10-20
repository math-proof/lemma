/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/BellRiordanCentralCoefficient.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import sympy.atlas.NumberTheory.BellMatrix
import sympy.atlas.RingTheory.PowerSeries.LagrangeBurmannCoefficient
namespace MetaMathlibExt

/--
Central coefficients of Bell-subgroup Riordan matrices: for the Bell matrix
`(g(X), X*g(X))`, the entry in row `2*n` and column `n` equals `(n+1)`
times the degree-`(n+1)` coefficient of the compositional inverse `u` of
`X / g(X)`.

Source: Paul Barry, "On the Central Coefficients of Bell Matrices,"
Journal of Integer Sequences 14 (2011), Article 11.4.3, Theorem `laterthm`,
lines 167-169, <https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry3/barry132.tex>.

The paper's `[x^n] (1/x) u(x)` is rendered as `coeff (n+1) u`, and
`T_{2n,n} = [x^{2n}] g*(X*g)^n` follows the paper's proof.

Proves `Wanted` entry `bell_riordan_central_coefficient`; it is now a proved
theorem, obtained by specializing the Lagrange–Bürmann coefficient formula
`fps_lagrange_burmann_coeff'`.
-/
theorem bell_riordan_central_coefficient
    (M : BellMatrix ℤ) (u : PowerSeries ℤ)
    (hg : PowerSeries.constantCoeff M.g = 1)
    (hu₀ : PowerSeries.constantCoeff u = 0)
    (hu : (PowerSeries.X * PowerSeries.invOfUnit M.g (1 : ℤˣ)).subst u = PowerSeries.X)
    (n : ℕ) :
    M.entry (2 * n) n =
      (n + 1 : ℤ) * PowerSeries.coeff (n + 1) u := by
  have hsubst : PowerSeries.HasSubst u :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hu₀
  have hfix : u = PowerSeries.X * PowerSeries.subst u M.g := by
    have h1 : PowerSeries.subst u M.g *
        PowerSeries.subst u (PowerSeries.invOfUnit M.g (1 : ℤˣ)) = 1 := by
      have hunit : PowerSeries.constantCoeff M.g = ((1 : ℤˣ) : ℤ) := by
        rw [hg]; rfl
      have hmul := PowerSeries.mul_invOfUnit M.g (1 : ℤˣ) hunit
      rw [← PowerSeries.subst_mul hsubst, hmul, ← PowerSeries.coe_substAlgHom hsubst]
      exact map_one _
    have h2 : u * PowerSeries.subst u (PowerSeries.invOfUnit M.g (1 : ℤˣ)) =
        PowerSeries.X := by
      have h := hu
      rw [PowerSeries.subst_mul hsubst, PowerSeries.subst_X hsubst] at h
      exact h
    calc u = u * 1 := (mul_one u).symm
      _ = u * (PowerSeries.subst u M.g *
            PowerSeries.subst u (PowerSeries.invOfUnit M.g (1 : ℤˣ))) := by rw [h1]
      _ = PowerSeries.X * PowerSeries.subst u M.g := by
            rw [mul_left_comm, h2, mul_comm]
  have hlb := fps_lagrange_burmann_coeff' u M.g PowerSeries.X hfix (n + 1) (Nat.succ_pos n)
  rw [PowerSeries.subst_X hsubst, PowerSeries.derivative_X, one_mul,
    Nat.add_sub_cancel] at hlb
  have hentry : M.entry (2 * n) n = PowerSeries.coeff n (M.g ^ (n + 1)) := by
    show PowerSeries.coeff (2 * n) (M.g * (PowerSeries.X * M.g) ^ n) = _
    have e : M.g * (PowerSeries.X * M.g) ^ n = PowerSeries.X ^ n * M.g ^ (n + 1) := by ring
    rw [e, show 2 * n = n + n from by ring]
    exact PowerSeries.coeff_X_pow_mul (M.g ^ (n + 1)) n n
  rw [hentry]
  exact_mod_cast hlb.symm

end MetaMathlibExt
