/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/ShannonSourceCoding.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.InformationTheory.Coding.UniquelyDecodable
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Def.InformationTheory.PrefixFree
import Lemma.Real.PrefixFree
import Lemma.Real.KraftMcMillan
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.InformationTheory.Coding.KraftMcMillan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.InformationTheory.KraftMcMillan


section

open Real BigOperators Finset

namespace MathlibExt.InformationTheory.ShannonSourceCodingWanted

/-!
# One-symbol Shannon source coding bounds

For finite alphabets `α`, `β` with `q = |β| ≥ 2`, pmf `p` on `α`,
base-`q` entropy `H_q`, and codes `α → List β`:

* any injective uniquely decodable code has `H_q ≤ E[length]`;
* there exists prefix-free with `E[length] < H_q + 1`.

These are single-letter bounds, not the asymptotic block-coding theorem
(block coding / typical sequences).

C. E. Shannon, A Mathematical Theory of Communication,
Bell System Technical Journal 27 (1948), 379–423 and 623–656,
DOI 10.1002/j.1538-7305.1948.tb01338.x and
10.1002/j.1538-7305.1948.tb00917.x.
-/

/-- A code is prefix-free if distinct source symbols have no prefix relation.

Compatibility alias for the production predicate
`MathlibExt.InformationTheory.IsPrefixFree`, which both Shannon bounds and the
proved Kraft–McMillan theorem share. -/
abbrev IsPrefixFree {α β : Type*} (code : α → List β) : Prop :=
  MathlibExt.InformationTheory.IsPrefixFree code

end MathlibExt.InformationTheory.ShannonSourceCodingWanted
end
