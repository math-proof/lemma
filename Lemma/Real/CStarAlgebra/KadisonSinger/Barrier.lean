import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.CStarAlgebra.KadisonSinger.Barrier
open scoped BigOperators ComplexOrder Real
open Filter MvPolynomial
open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


/--
[mixedCharacteristicPolynomial_maxRealRoot_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/Barrier.lean)
-/
@[path]
private lemma mixedCharacteristicPolynomial_maxRealRoot_le_eq
  [Fintype d] [DecidableEq d] [Nonempty d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
  {η : ℝ}
-- given
  (hη : 0 ≤ η)
  (hA : ∀ i, (A i).PosSemidef)
  (hsum : ∑ i, A i = 1)
  (htrace : ∀ i, (Matrix.trace (A i)).re ≤ η) :
-- imply
  (mixedCharacteristicPolynomial A).maxRealRoot ≤ (1 + Real.sqrt η) ^ 2 := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.mixedCharacteristicPolynomial_maxRealRoot_le A η hη hA hsum htrace


-- created on 2026-10-20
