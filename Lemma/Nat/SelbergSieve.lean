import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SelbergSieve
open MathlibExt.SelbergSieve


/--
[levelSum_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SelbergSieve.lean)
-/
@[path]
private lemma levelSum_ge_one_eq
  {s : BoundingSieve}
  {R : ℕ}
-- given
  (hR : 1 ≤ R) :
-- imply
  1 ≤ levelSum s R := by
-- proof
  apply MathlibExt.SelbergSieve.levelSum_ge_one s R hR

/--
[levelWeights_inner](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SelbergSieve.lean)
-/
@[path]
private lemma levelWeights_inner_eq
  {s : BoundingSieve}
  {R l : ℕ}
-- given
  (hl : l ∣ s.prodPrimes) :
-- imply
  (∑ d ∈ s.prodPrimes.divisors,
    if l ∣ d then s.nu d * levelWeights s R d else 0) =
    levelY s R l := by
-- proof
  apply MathlibExt.SelbergSieve.levelWeights_inner s R l hl

/--
[levelWeights_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SelbergSieve.lean)
-/
@[path]
private lemma levelWeights_one_eq
  {s : BoundingSieve}
  {R : ℕ}
-- given
  (hR : 1 ≤ R) :
-- imply
  levelWeights s R 1 = 1 := by
-- proof
  apply MathlibExt.SelbergSieve.levelWeights_one s R hR

/--
[levelWeights_mainSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SelbergSieve.lean)
-/
@[path]
private lemma levelWeights_mainSum_eq
  {s : BoundingSieve}
  {R : ℕ}
-- given
  (hR : 1 ≤ R) :
-- imply
  s.mainSum (BoundingSieve.lambdaSquared (levelWeights s R)) =
    1 / levelSum s R := by
-- proof
  apply MathlibExt.SelbergSieve.levelWeights_mainSum s R hR

/--
[levelWeights_nu_mul_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SelbergSieve.lean)
-/
@[path]
private lemma levelWeights_nu_mul_abs_le_eq
  {s : BoundingSieve}
  {R d : ℕ}
-- given
  (hR : 1 ≤ R)
  (hd : d ∣ s.prodPrimes) :
-- imply
  |s.nu d * levelWeights s R d| ≤ 1 := by
-- proof
  apply MathlibExt.SelbergSieve.levelWeights_nu_mul_abs_le s R d hR hd

/--
[levelWeights_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SelbergSieve.lean)
-/
@[path]
private lemma levelWeights_abs_le_eq
  {s : BoundingSieve}
  {R d : ℕ}
-- given
  (hR : 1 ≤ R)
  (hd : d ∣ s.prodPrimes) :
-- imply
  |levelWeights s R d| ≤ 1 := by
-- proof
  apply MathlibExt.SelbergSieve.levelWeights_abs_le s R d hR hd

/--
[levelWeights_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SelbergSieve.lean)
-/
@[path]
private lemma levelWeights_support_eq
  {s : BoundingSieve}
  {R d : ℕ}
-- given
  (hd : levelWeights s R d ≠ 0) :
-- imply
  d ≤ R := by
-- proof
  apply MathlibExt.SelbergSieve.levelWeights_support s R d hd

/--
[levelWeights_errSum_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SelbergSieve.lean)
-/
@[path]
private lemma levelWeights_errSum_le_eq
  {s : BoundingSieve}
  {R : ℕ}
-- given
  (hR : 1 ≤ R)
  (hnu : ∀ d : ℕ, d ∣ s.prodPrimes → 1 ≤ (d : ℝ) * s.nu d)
  (hrem : ∀ d : ℕ, d ∣ s.prodPrimes → |s.rem d| ≤ (d : ℝ)) :
-- imply
  s.errSum (BoundingSieve.lambdaSquared (levelWeights s R)) ≤
    (R : ℝ) ^ 12 := by
-- proof
  apply MathlibExt.SelbergSieve.levelWeights_errSum_le s R hR hnu hrem


-- created on 2026-10-20
