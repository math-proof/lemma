import Mathlib

open UpperHalfPlane Set
open scoped MatrixGroups Topology

noncomputable section

namespace ModularCurve.SmoothedFundamental

def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num γ z / denom γ z


def pOne (x : ℝ) : ℝ := Real.smoothTransition (x + 1) - Real.smoothTransition x


def pTwo (T y : ℝ) : ℝ := Real.smoothTransition (8 * y - 5) * Real.smoothTransition (T + 4 - y)


def bump (T : ℝ) (z : ℂ) : ℝ := pOne z.re * pTwo T z.im


def box (T : ℝ) : Set ℂ := Icc (-1 : ℝ) 1 ×ℂ Icc (5 / 8 : ℝ) (T + 4)


def recip (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 1) / t


def gcut (T : ℝ) (z : ℂ) : ℝ := 1 - Real.smoothTransition (z.im - T)


def cover (T : ℝ) (z : ℂ) : ℝ := ∑ᶠ γ : SL(2, ℤ), bump T (mob γ z)


def pu (T : ℝ) (z : ℂ) : ℝ := bump T z * recip (cover T z)


def puCut (T : ℝ) (z : ℂ) : ℝ := pu T z * gcut T z

end ModularCurve.SmoothedFundamental

def ModularCurve.smoothedFundamental (Γ : Subgroup SL(2, ℤ)) (T : ℝ) (z : ℂ) : ℝ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ Γ,
    ModularCurve.SmoothedFundamental.puCut T (ModularCurve.SmoothedFundamental.mob (Quotient.out q) z)

end
