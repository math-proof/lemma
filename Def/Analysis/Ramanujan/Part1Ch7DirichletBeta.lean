/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.NumberTheory.LSeries.ZMod
/-!
# Shared Dirichlet beta API for Chapter 7, Entries 17 and 18

The beta character, the Dirichlet beta function, and the Euler star function.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace DirichletBeta

noncomputable section

def chapter7BetaCharacter (a : ZMod 4) : ℂ :=
  if a = 1 then 1 else if a = 3 then -1 else 0

def chapter7DirichletBeta (s : ℂ) : ℂ :=
  ZMod.LFunction chapter7BetaCharacter s

def chapter7EulerStar (s : ℂ) : ℂ :=
  2 * Complex.Gamma s * chapter7DirichletBeta s /
    Complex.cpow ((Real.pi / 2 : ℝ) : ℂ) s

end
end DirichletBeta
end MathlibExt.Analysis.Ramanujan.Part1Ch7
