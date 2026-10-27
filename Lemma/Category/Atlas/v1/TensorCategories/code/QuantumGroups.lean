import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.QuantumGroups


/--
[qAnalog_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumGroups.lean)
-/
@[path]
lemma qAnalog_zero
  [Field k]
  {q : k} :
-- imply
  qAnalog q 0 = 0 := by
-- proof
  simp [qAnalog]

/--
[qAnalog_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumGroups.lean)
-/
@[path]
lemma qAnalog_one
  [Field k]
  {q : k}
-- given
  (hq : q - q⁻¹ ≠ 0) :
-- imply
  qAnalog q 1 = 1 := by
-- proof
  simp only [qAnalog, pow_one]
  exact div_self hq

/--
[qAnalogFactorial_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumGroups.lean)
-/
@[path]
lemma qAnalogFactorial_zero
  [Field k]
  {q : k} :
-- imply
  qAnalogFactorial q 0 = 1 := by
-- proof
  simp [qAnalogFactorial]

/--
[qAnalogFactorial_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumGroups.lean)
-/
@[path]
lemma qAnalogFactorial_one
  [Field k]
  {q : k}
-- given
  (hq : q - q⁻¹ ≠ 0) :
-- imply
  qAnalogFactorial q 1 = 1 := by
-- proof
  simp [qAnalogFactorial, qAnalog_one q hq]

/--
[qAnalogFactorial_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumGroups.lean)
-/
@[path]
lemma qAnalogFactorial_succ
  [Field k]
  {q : k}
  {n : ℕ} :
-- imply
  qAnalogFactorial q (n + 1) = qAnalogFactorial q n * qAnalog q (n + 1) := by
-- proof
  simp [qAnalogFactorial, Finset.prod_range_succ]


-- created on 2026-10-23
