import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Thm2321
open CategoryTheory GroupCohomology


namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]
/--
[homology_long_exact_sequence_exact₁](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2321.lean)
-/
@[path]
lemma homology_long_exact_sequence_exact₁
  {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
  {i j : ℕ} (hij : j + 1 = i) :
  (groupHomology.mapShortComplex₁ hX hij).Exact :=
  groupHomology.mapShortComplex₁_exact hX hij

end GroupCohomology

/--
[homology_long_exact_sequence_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2321.lean)
-/
@[path]
private lemma homology_long_exact_sequence_exact_eq
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  {X : ShortComplex (Rep k G)}
  {i j : ℕ}
-- given
  (hX : X.ShortExact)
  (hij : j + 1 = i) :
-- imply
  (groupHomology.mapShortComplex₁ hX hij).Exact := by
-- proof
  apply GroupCohomology.homology_long_exact_sequence_exact hX hij


-- created on 2026-10-23
