module

public import Mathlib.Data.Vector.MapLemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Theorem.Nat.EqMin_SubMulS
public import Theorem.Nat.EqAddMulDiv
public import Theorem.List.Prod.eq.MulProdS
public import Theorem.Algebra.Power.Part2
public import Notation.Data.Vector.Basic.Part2
public import Macro.Data.List.List
public import Instance.Data.List.List

open Nat Lean
open scoped BigOperators


@[expose] public section

namespace List.Vector

/--
Implement the instance for Vector
-/
instance : IsConstant (Vector α n) where
  is_constant v := v.val is constant

end List.Vector
