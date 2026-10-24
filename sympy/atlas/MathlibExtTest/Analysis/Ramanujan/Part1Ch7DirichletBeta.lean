/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch7DirichletBeta.lean -/


import sympy.atlas.Analysis.Ramanujan.Part1Ch7DirichletBeta
import Lemma.Complex.Part1Ch7DirichletBeta

/-!
# Shared Dirichlet beta API checks

The four residue-class evaluations of the beta character and its vanishing sum.
-/

namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch7DirichletBeta

open MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

example : chapter7BetaCharacter 0 = 0 := by simp

example : chapter7BetaCharacter 1 = 1 := by simp

example : chapter7BetaCharacter 2 = 0 := by simp

example : chapter7BetaCharacter 3 = -1 := by simp

example : ∑ j : ZMod 4, chapter7BetaCharacter j = 0 := betaCharSum

end MathlibExtTest.Analysis.Ramanujan.Part1Ch7DirichletBeta
