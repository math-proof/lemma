import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.CStarAlgebra.KadisonSinger.RealStable
open scoped BigOperators ComplexOrder
open Filter MvPolynomial
open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


/--
[mixedDetPolynomial_isStable_of_posSemidef](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/RealStable.lean)
-/
@[path]
private lemma mixedDetPolynomial_isStable_of_posSemidef_eq
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
-- given
  (hA : ∀ i, (A i).PosSemidef) :
-- imply
  (mixedDetPolynomial A).IsStable := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.mixedDetPolynomial_isStable_of_posSemidef A hA

/--
[mixedDetPolynomial_isRealStable_of_posSemidef](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/RealStable.lean)
-/
@[path]
private lemma mixedDetPolynomial_isRealStable_of_posSemidef_eq
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
-- given
  (hA : ∀ i, (A i).PosSemidef) :
-- imply
  (mixedDetPolynomial A).IsRealStable := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.mixedDetPolynomial_isRealStable_of_posSemidef A hA

/--
[mixedCharacteristicPolynomial_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/RealStable.lean)
-/
@[path]
private lemma mixedCharacteristicPolynomial_monic_eq
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ} :
-- imply
  (mixedCharacteristicPolynomial A).Monic := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.mixedCharacteristicPolynomial_monic A

/--
[mixedCharacteristicPolynomial_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/RealStable.lean)
-/
@[path]
private lemma mixedCharacteristicPolynomial_natDegree_eq
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ} :
-- imply
  (mixedCharacteristicPolynomial A).natDegree = Fintype.card d := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.mixedCharacteristicPolynomial_natDegree A

/--
[mixedCharacteristicPolynomial_isRealRooted_of_posSemidef](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/RealStable.lean)
-/
@[path]
private lemma mixedCharacteristicPolynomial_isRealRooted_of_posSemidef_eq
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
-- given
  (hA : ∀ i, (A i).PosSemidef) :
-- imply
  (mixedCharacteristicPolynomial A).IsRealRooted := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.mixedCharacteristicPolynomial_isRealRooted_of_posSemidef A hA


-- created on 2026-10-20
