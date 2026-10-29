import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.NumberTheory.NumberField.NormOneIdeleClassGroup
open NumberField.TopologicalIdeleGroup


namespace NumberField.TopologicalIdeleGroup

/--
[normOne_mk_principalEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormOneIdeleClassGroup.lean)
-/
@[path]
lemma normOne_mk_principalEmbedding
  (K : Type*) [Field K] [NumberField K]
  (x : Kˣ) :
-- imply
  QuotientGroup.mk (s := normOnePrincipalIdeles K)
      ⟨principalEmbedding (NumberField.RingOfIntegers K) K x,
        principalIdeles_le_normOneIdeles ⟨x, rfl⟩⟩ = 1 := by
-- proof
  rw [QuotientGroup.eq_one_iff]
  exact ⟨x, rfl⟩

end NumberField.TopologicalIdeleGroup


-- created on 2026-10-20
-- updated on 2026-10-29
