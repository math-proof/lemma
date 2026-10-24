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

@[simp] theorem betaChar0 : chapter7BetaCharacter 0 = 0 := by
  simp [chapter7BetaCharacter, show (0 : ZMod 4) ≠ 1 from by decide,
    show (0 : ZMod 4) ≠ 3 from by decide]

@[simp] theorem betaChar1 : chapter7BetaCharacter 1 = 1 := by simp [chapter7BetaCharacter]

@[simp] theorem betaChar2 : chapter7BetaCharacter 2 = 0 := by
  simp [chapter7BetaCharacter, show (2 : ZMod 4) ≠ 1 from by decide,
    show (2 : ZMod 4) ≠ 3 from by decide]

@[simp] theorem betaChar3 : chapter7BetaCharacter 3 = -1 := by
  simp [chapter7BetaCharacter, show (3 : ZMod 4) ≠ 1 from by decide]
end
end DirichletBeta
