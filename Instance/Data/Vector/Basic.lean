import Mathlib.Data.Vector.MapLemmas
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lemma.Nat.EqMin_SubMulS
import Lemma.Nat.EqAddMulDiv
import Lemma.List.LengthRange.eq.Length
import Lemma.List.Prod.eq.MulProdS
import Theorem.Algebra.Power.Part2
import Theorem.Function
import Notation.Data.Vector.Basic.Part2
import Macro.Data.List.List
import Instance.Data.List.List
open Nat Lean
open scoped BigOperators


namespace List.Vector

/--
Implement the instance for Vector
-/
instance : IsConstant (Vector α n) where
  is_constant v := v.val is constant

end List.Vector
