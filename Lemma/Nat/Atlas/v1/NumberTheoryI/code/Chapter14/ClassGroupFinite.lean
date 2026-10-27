import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.Chapter14.ClassGroupFinite
open NumberField ClassGroupFinite


namespace ClassGroupFinite

/--
[idealClass_exists_integral_absNorm_le_minkowskiConstant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter14/ClassGroupFinite.lean)
-/
@[path]
lemma idealClass_exists_integral_absNorm_le_minkowskiConstant
  {K : Type*}
  [Field K]
  [NumberField K]
  {C : ClassGroup (𝓞 K)} :
-- imply
  ∃ I : ↥(nonZeroDivisors (Ideal (𝓞 K))), ClassGroup.mk0 I = C ∧ ↑(Ideal.absNorm (I : Ideal (𝓞 K))) ≤ minkowskiConstant K :=
-- proof
  NumberField.exists_ideal_in_class_of_norm_le C

end ClassGroupFinite

namespace ClassGroupFinite

/--
[ideals_bounded_absNorm_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter14/ClassGroupFinite.lean)
-/
@[path]
lemma ideals_bounded_absNorm_card_le
  {K : Type*}
  [Field K]
  [NumberField K]
  {M : ℕ} :
-- imply
  Nat.card {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} ≤ (Module.finrank ℚ K * M) ^ Nat.log 2 M :=
-- proof
  GeometryOfNumbers.ideals_bounded_norm_card_le K M

end ClassGroupFinite

namespace ClassGroupFinite

/--
[classGroup_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter14/ClassGroupFinite.lean)
-/
@[path]
lemma classGroup_finite
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  Finite (ClassGroup (𝓞 K)) :=
-- proof
  inferInstance

end ClassGroupFinite


-- created on 2026-10-23
