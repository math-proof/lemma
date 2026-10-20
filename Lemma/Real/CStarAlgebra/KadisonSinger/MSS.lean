import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.CStarAlgebra.KadisonSinger.MSS
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


/--
[exists_outcome_maxRealRoot_le_mixedCharacteristicPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MSS.lean)
-/
@[path]
private lemma exists_outcome_maxRealRoot_le_mixedCharacteristicPolynomial_eq
  [Fintype d] [DecidableEq d] [Nonempty d]
  {m : ℕ}
  {s : Fin m → ℕ}
  {p : (i : Fin m) → Fin (s i) → ℝ}
  {v : (i : Fin m) → Fin (s i) → d → ℂ}
-- given
  (hs : ∀ i, 0 < s i)
  (hp : ∀ i a, 0 ≤ p i a)
  (hsum : ∀ i, ∑ a, p i a = 1) :
-- imply
  ∃ ω : (i : Fin m) → Fin (s i),
    (Matrix.charpoly
    (∑ i, Matrix.vecMulVec (v i (ω i)) (star (v i (ω i))))).maxRealRoot ≤
    (mixedCharacteristicPolynomial (fun i ↦
    ∑ a, p i a • Matrix.vecMulVec (v i a) (star (v i a)))).maxRealRoot := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.exists_outcome_maxRealRoot_le_mixedCharacteristicPolynomial hs p v hp hsum

/--
[finiteMSSBound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MSS.lean)
-/
@[path]
private lemma finiteMSSBound_eq
  :
-- imply
  FiniteMSSBound.{u} := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.finiteMSSBound


-- created on 2026-10-20
