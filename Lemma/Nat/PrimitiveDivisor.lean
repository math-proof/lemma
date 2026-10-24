import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimitiveDivisor
open IntegerSequence


namespace IntegerSequence

/--
[IsPrimitiveDivisor.one_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitiveDivisor.one_le
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitiveDivisor a m u) :
-- imply
  1 ≤ m :=
-- proof
  h.1

end IntegerSequence

namespace IntegerSequence

/--
[IsPrimitiveDivisor.two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitiveDivisor.two_le
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitiveDivisor a m u) :
-- imply
  2 ≤ u :=
-- proof
  h.2.1

end IntegerSequence

namespace IntegerSequence

/--
[IsPrimitiveDivisor.dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitiveDivisor.dvd
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitiveDivisor a m u) :
-- imply
  (u : ℤ) ∣ a m :=
-- proof
  h.2.2.1

end IntegerSequence

namespace IntegerSequence

/--
[IsPrimitiveDivisor.not_dvd_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitiveDivisor.not_dvd_of_lt
  {a : ℕ → ℤ}
  {m u s : ℕ}
-- given
  (h : IsPrimitiveDivisor a m u)
  (hs : 1 ≤ s)
  (hsm : s < m) :
-- imply
  ¬ (u : ℤ) ∣ a s :=
-- proof
  h.2.2.2 s hs hsm

end IntegerSequence

namespace IntegerSequence

/--
[IsPrimitivePrimeDivisor.prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitivePrimeDivisor.prime
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitivePrimeDivisor a m u) :
-- imply
  Nat.Prime u :=
-- proof
  h.1

end IntegerSequence

namespace IntegerSequence

/--
[IsPrimitivePrimeDivisor.toIsPrimitiveDivisor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitivePrimeDivisor.toIsPrimitiveDivisor
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitivePrimeDivisor a m u) :
-- imply
  IsPrimitiveDivisor a m u :=
-- proof
  h.2

end IntegerSequence

namespace IntegerSequence

/--
[IsPrimitivePrimeDivisor.one_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitivePrimeDivisor.one_le
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitivePrimeDivisor a m u) :
-- imply
  1 ≤ m :=
-- proof
  h.toIsPrimitiveDivisor.one_le

end IntegerSequence

namespace IntegerSequence

/--
[IsPrimitivePrimeDivisor.two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitivePrimeDivisor.two_le
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitivePrimeDivisor a m u) :
-- imply
  2 ≤ u :=
-- proof
  h.toIsPrimitiveDivisor.two_le

end IntegerSequence

namespace IntegerSequence

/--
[IsPrimitivePrimeDivisor.dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitivePrimeDivisor.dvd
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitivePrimeDivisor a m u) :
-- imply
  (u : ℤ) ∣ a m :=
-- proof
  h.toIsPrimitiveDivisor.dvd

end IntegerSequence

namespace IntegerSequence

/--
[IsPrimitivePrimeDivisor.not_dvd_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitivePrimeDivisor.not_dvd_of_lt
  {a : ℕ → ℤ}
  {m u s : ℕ}
-- given
  (h : IsPrimitivePrimeDivisor a m u)
  (hs : 1 ≤ s)
  (hsm : s < m) :
-- imply
  ¬ (u : ℤ) ∣ a s :=
-- proof
  h.toIsPrimitiveDivisor.not_dvd_of_lt hs hsm

end IntegerSequence

namespace IntegerSequence

/--
[isPrimitivePrimeDivisor_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma isPrimitivePrimeDivisor_iff
  {a : ℕ → ℤ}
  {m u : ℕ} :
-- imply
  IsPrimitivePrimeDivisor a m u ↔
    Nat.Prime u ∧ 1 ≤ m ∧ 2 ≤ u ∧ (u : ℤ) ∣ a m ∧
    ∀ s : ℕ, 1 ≤ s → s < m → ¬ (u : ℤ) ∣ a s :=
-- proof
  Iff.rfl

end IntegerSequence

namespace IntegerSequence

/--
[IsPrimitiveDivisor.le_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitiveDivisor.le_of_dvd
  {a : ℕ → ℤ}
  {m u n : ℕ}
-- given
  (hm : IsPrimitiveDivisor a m u)
  (hn : 1 ≤ n)
  (hdvd : (u : ℤ) ∣ a n) :
-- imply
  m ≤ n := by
-- proof
  by_contra hmn
  exact hm.not_dvd_of_lt hn (by omega) hdvd

end IntegerSequence

namespace IntegerSequence

/--
[IsPrimitiveDivisor.unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitiveDivisor.unique
  {a : ℕ → ℤ}
  {m n u : ℕ}
-- given
  (hm : IsPrimitiveDivisor a m u)
  (hn : IsPrimitiveDivisor a n u) :
-- imply
  m = n :=
-- proof
  le_antisymm (hm.le_of_dvd hn.one_le hn.dvd) (hn.le_of_dvd hm.one_le hm.dvd)

end IntegerSequence

namespace IntegerSequence

/--
[IsPrimitivePrimeDivisor.unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
lemma IsPrimitivePrimeDivisor.unique
  {a : ℕ → ℤ}
  {m n u : ℕ}
-- given
  (hm : IsPrimitivePrimeDivisor a m u)
  (hn : IsPrimitivePrimeDivisor a n u) :
-- imply
  m = n :=
-- proof
  hm.toIsPrimitiveDivisor.unique hn.toIsPrimitiveDivisor

end IntegerSequence


-- created on 2026-10-20
-- updated on 2026-10-23
