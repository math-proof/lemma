import Mathlib
import sympy.Basic
import sympy.atlas.InformationTheory.ShannonSourceCoding
open Real BigOperators Finset
open MathlibExt.InformationTheory.ShannonSourceCodingWanted


/--
[shannon_source_coding_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/ShannonSourceCoding.lean)
-/
@[path]
private lemma shannon_source_coding_lower_bound_eq
  [Fintype α] [Fintype β]
  {p : α → ℝ}
  {code : α → List β}
-- given
  (hp_pos : ∀ a, 0 < p a)
  (hp_sum : ∑ a : α, p a = 1)
  (hq : 2 ≤ Fintype.card β)
  (h_inj : Function.Injective code)
  (h_ud : InformationTheory.IsUniquelyDecodable (Set.range code)) :
-- imply
  -(∑ a : α, p a * Real.log (p a)) / Real.log (Fintype.card β : ℝ)
    ≤ ∑ a : α, p a * ((code a).length : ℝ) := by
-- proof
  apply MathlibExt.InformationTheory.ShannonSourceCodingWanted.shannon_source_coding_lower_bound p hp_pos hp_sum hq code h_inj h_ud

/--
[shannon_source_coding_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/ShannonSourceCoding.lean)
-/
@[path]
private lemma shannon_source_coding_upper_bound_eq
  [Fintype α] [Fintype β]
  {p : α → ℝ}
-- given
  (hp_pos : ∀ a, 0 < p a)
  (hp_sum : ∑ a : α, p a = 1)
  (hq : 2 ≤ Fintype.card β) :
-- imply
  ∃ (code : α → List β),
    IsPrefixFree code ∧
    (∑ a : α, p a * ((code a).length : ℝ)) <
    -(∑ a : α, p a * Real.log (p a)) / Real.log (Fintype.card β : ℝ) + 1 := by
-- proof
  apply MathlibExt.InformationTheory.ShannonSourceCodingWanted.shannon_source_coding_upper_bound p hp_pos hp_sum hq


-- created on 2026-10-20
