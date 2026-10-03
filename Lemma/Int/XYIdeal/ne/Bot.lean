import Mathlib
import sympy.Basic

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

/--
[WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot.lean)
-/
@[main]
private lemma main
  [CommRing R] [Nontrivial R]
  {W : Affine R}
  {x : R}
  {y : R[X]} :
-- imply
  XYIdeal W x y ≠ ⊥ :=
-- proof
  fun h0 =>
  XClass_ne_zero (W' := W) x <| by
    have : XClass W x ∈ XYIdeal W x y := Ideal.subset_span (by simp)
    rwa [h0, Ideal.mem_bot] at this


-- created on 2026-10-03
