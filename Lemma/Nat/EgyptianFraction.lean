import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.EgyptianFraction
open scoped BigOperators
open EgyptianFraction


namespace EgyptianFraction.IsNondecreasingEgyptian

/--
[denominator_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma denominator_ge_two
  {n : ℕ}
  {a : Fin n → ℕ}
  {i : Fin n}
-- given
  (h : IsNondecreasingEgyptian a) :
-- imply
  2 ≤ a i :=
-- proof
  h.1 i

end EgyptianFraction.IsNondecreasingEgyptian

namespace EgyptianFraction.IsNondecreasingEgyptian

/--
[monotone](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma monotone
  {n : ℕ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingEgyptian a) :
-- imply
  Monotone a :=
-- proof
  h.2

end EgyptianFraction.IsNondecreasingEgyptian

namespace EgyptianFraction.IsStrictEgyptian

/--
[denominator_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma denominator_ge_two
  {n : ℕ}
  {a : Fin n → ℕ}
  {i : Fin n}
-- given
  (h : IsNondecreasingEgyptian a) :
-- imply
  2 ≤ a i :=
-- proof
  h.1 i

end EgyptianFraction.IsStrictEgyptian

namespace EgyptianFraction.IsStrictEgyptian

/--
[strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma strictMono
  {n : ℕ}
  {a : Fin n → ℕ}
-- given
  (h : IsStrictEgyptian a) :
-- imply
  StrictMono a :=
-- proof
  h.2

end EgyptianFraction.IsStrictEgyptian

namespace EgyptianFraction.IsStrictEgyptian

/--
[toIsNondecreasingEgyptian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma toIsNondecreasingEgyptian
  {n : ℕ}
  {a : Fin n → ℕ}
-- given
  (h : IsStrictEgyptian a) :
-- imply
  IsNondecreasingEgyptian a :=
-- proof
  ⟨h.1, h.strictMono.monotone⟩

end EgyptianFraction.IsStrictEgyptian

namespace EgyptianFraction.IsNondecreasingUnderapproximation

/--
[nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma nonempty
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  0 < n :=
-- proof
  h.1

end EgyptianFraction.IsNondecreasingUnderapproximation

namespace EgyptianFraction.IsNondecreasingUnderapproximation

/--
[target_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma target_pos
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  0 < target :=
-- proof
  h.2.1

end EgyptianFraction.IsNondecreasingUnderapproximation

namespace EgyptianFraction.IsNondecreasingUnderapproximation

/--
[isNondecreasingEgyptian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma isNondecreasingEgyptian
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  IsNondecreasingEgyptian a :=
-- proof
  h.2.2.1

end EgyptianFraction.IsNondecreasingUnderapproximation

namespace EgyptianFraction.IsNondecreasingUnderapproximation

/--
[denominator_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma denominator_ge_two
  {n : ℕ}
  {a : Fin n → ℕ}
  {i : Fin n}
-- given
  (h : IsNondecreasingEgyptian a) :
-- imply
  2 ≤ a i :=
-- proof
  h.1 i

end EgyptianFraction.IsNondecreasingUnderapproximation

namespace EgyptianFraction.IsNondecreasingUnderapproximation

/--
[monotone](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma monotone
  {n : ℕ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingEgyptian a) :
-- imply
  Monotone a :=
-- proof
  h.2

end EgyptianFraction.IsNondecreasingUnderapproximation

namespace EgyptianFraction.IsNondecreasingUnderapproximation

/--
[sum_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma sum_lt
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  ∑ i, ((a i : ℝ)⁻¹) < target :=
-- proof
  h.2.2.2

end EgyptianFraction.IsNondecreasingUnderapproximation

namespace EgyptianFraction.IsStrictUnderapproximation

/--
[nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma nonempty
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  0 < n :=
-- proof
  h.1

end EgyptianFraction.IsStrictUnderapproximation

namespace EgyptianFraction.IsStrictUnderapproximation

/--
[target_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma target_pos
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  0 < target :=
-- proof
  h.2.1

end EgyptianFraction.IsStrictUnderapproximation

namespace EgyptianFraction.IsStrictUnderapproximation

/--
[isStrictEgyptian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma isStrictEgyptian
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsStrictUnderapproximation target a) :
-- imply
  IsStrictEgyptian a :=
-- proof
  h.2.2.1

end EgyptianFraction.IsStrictUnderapproximation

namespace EgyptianFraction.IsStrictUnderapproximation

/--
[denominator_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma denominator_ge_two
  {n : ℕ}
  {a : Fin n → ℕ}
  {i : Fin n}
-- given
  (h : IsNondecreasingEgyptian a) :
-- imply
  2 ≤ a i :=
-- proof
  h.1 i

end EgyptianFraction.IsStrictUnderapproximation

namespace EgyptianFraction.IsStrictUnderapproximation

/--
[strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma strictMono
  {n : ℕ}
  {a : Fin n → ℕ}
-- given
  (h : IsStrictEgyptian a) :
-- imply
  StrictMono a :=
-- proof
  h.2

end EgyptianFraction.IsStrictUnderapproximation

namespace EgyptianFraction.IsStrictUnderapproximation

/--
[sum_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma sum_lt
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  ∑ i, ((a i : ℝ)⁻¹) < target :=
-- proof
  h.2.2.2

end EgyptianFraction.IsStrictUnderapproximation

namespace EgyptianFraction.IsStrictUnderapproximation

/--
[toIsNondecreasingUnderapproximation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
lemma toIsNondecreasingUnderapproximation
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsStrictUnderapproximation target a) :
-- imply
  IsNondecreasingUnderapproximation target a :=
-- proof
  ⟨h.1, h.2.1, ⟨h.2.2.1.1, h.2.2.1.2.monotone⟩, h.2.2.2⟩

end EgyptianFraction.IsStrictUnderapproximation


-- created on 2026-10-20
-- updated on 2026-10-28
