import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.TaftHopfInstance.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.TaftHopfInstance
import Lemma.Category.Atlas.v1.TensorCategories.code.QBinomial
import Theorem.v1.Atlas.TensorCategories.code.QBinomial.Part2
open Coalgebra HopfAlgebra
open scoped TensorProduct


namespace TaftAlgebraType

/--
[q_comm_sum_pow_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfDataInstance.lean)
-/
@[path]
lemma q_comm_sum_pow_zero
  {k : Type*}
  [Field k]
  {n : ℕ}
  [NeZero n]
  {q : k}
  [Fact (q ^ n = 1)]
  [Ring B]
  [Algebra k B]
  {a b : B}
-- given
  (hn : 1 < n)
  (hq : IsPrimitiveRoot q n)
  (hcomm : b * a = algebraMap k B q⁻¹ * (a * b))
  (ha : a ^ n = 0)
  (hb : b ^ n = 0) :
-- imply
  (a + b) ^ n = 0 := by
-- proof
  have hqi : IsPrimitiveRoot q⁻¹ n := hq.inv
  rw [q_comm_power q⁻¹ n hn hqi a b hcomm, ha, hb, add_zero]

end TaftAlgebraType


-- created on 2026-10-23
