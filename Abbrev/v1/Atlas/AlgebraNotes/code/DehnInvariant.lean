/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/DehnInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.NumberTheory.Real.Irrational
@[expose] public section

open Real TensorProduct Module


namespace DehnInvariant

abbrev tensorProduct (G : Type u) (H : Type v) [AddCommGroup G] [AddCommGroup H] :
    Type (max u v) :=
  TensorProduct ℤ G H

end DehnInvariant
