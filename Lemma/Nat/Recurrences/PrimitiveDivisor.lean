import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Recurrences.PrimitiveDivisor
open scoped BigOperators
open LucasSequence


namespace LucasSequence

/--
[IsPrimitiveDivisor.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitiveDivisor.pos
  {u : ℕ → ℤ}
  {discriminant : ℤ}
  {n p : ℕ}
-- given
  (h : IsPrimitiveDivisor u discriminant n p) :
-- imply
  0 < n :=
-- proof
  h.1

end LucasSequence

namespace LucasSequence

/--
[IsPrimitiveDivisor.prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitiveDivisor.prime
  {u : ℕ → ℤ}
  {discriminant : ℤ}
  {n p : ℕ}
-- given
  (h : IsPrimitiveDivisor u discriminant n p) :
-- imply
  p.Prime :=
-- proof
  h.2.1

end LucasSequence

namespace LucasSequence

/--
[IsPrimitiveDivisor.dvd_term](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitiveDivisor.dvd_term
  {u : ℕ → ℤ}
  {discriminant : ℤ}
  {n p : ℕ}
-- given
  (h : IsPrimitiveDivisor u discriminant n p) :
-- imply
  (p : ℤ) ∣ u n :=
-- proof
  h.2.2.1

end LucasSequence

namespace LucasSequence

/--
[IsPrimitiveDivisor.not_dvd_badPart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitiveDivisor.not_dvd_badPart
  {u : ℕ → ℤ}
  {discriminant : ℤ}
  {n p : ℕ}
-- given
  (h : IsPrimitiveDivisor u discriminant n p) :
-- imply
  ¬(p : ℤ) ∣ discriminant * ∏ k ∈ Finset.Ico 1 n, u k :=
-- proof
  h.2.2.2

end LucasSequence

namespace LucasSequence

/--
[IsPrimitiveDivisor.not_dvd_discriminant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitiveDivisor.not_dvd_discriminant
  {u : ℕ → ℤ}
  {discriminant : ℤ}
  {n p : ℕ}
-- given
  (h : IsPrimitiveDivisor u discriminant n p) :
-- imply
  ¬(p : ℤ) ∣ discriminant := by
-- proof
  intro hp
  exact h.not_dvd_badPart (dvd_mul_of_dvd_left hp _)

end LucasSequence

namespace LucasSequence

/--
[IsPrimitiveDivisor.not_dvd_prior](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitiveDivisor.not_dvd_prior
  {u : ℕ → ℤ}
  {discriminant : ℤ}
  {n p k : ℕ}
-- given
  (h : IsPrimitiveDivisor u discriminant n p)
  (hk : k ∈ Finset.Ico 1 n) :
-- imply
  ¬(p : ℤ) ∣ u k := by
-- proof
  intro hp
  apply h.not_dvd_badPart
  exact dvd_mul_of_dvd_right (dvd_trans hp (Finset.dvd_prod_of_mem u hk)) _

end LucasSequence


-- created on 2026-10-20
-- updated on 2026-10-26
