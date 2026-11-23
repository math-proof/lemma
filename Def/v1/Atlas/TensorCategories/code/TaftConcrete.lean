/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Fintype.Prod
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Theorem.v1.Atlas.TensorCategories.code.TaftConcrete

@[expose] public section

variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {q : k}

set_option linter.unusedSectionVars false


namespace TaftAlgebraType

/-- Structure constants for the Taft-algebra multiplication on the basis `{g^a x^b}`. The
product of `g^{i_1} x^{i_2}` and `g^{c_1} x^{c_2}` is the basis element `g^{(i_1+c_1) mod n}
x^{i_2+c_2}` with scalar coefficient `q^{n^2 - i_2 c_1}` when `i_2+c_2 < n`, and zero otherwise. -/
noncomputable def basisMul (q : k) (ij cd : Fin n × Fin n) : Fin n × Fin n → k := fun (e, f) =>
  if ij.2.val + cd.2.val < n
    ∧ e.val = (ij.1.val + cd.1.val) % n
    ∧ f.val = ij.2.val + cd.2.val
  then q ^ (n * n - ij.2.val * cd.1.val)
  else 0

end TaftAlgebraType
