/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Def.v1.Atlas.TensorCategories.code.QuantumSl2.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.QuantumSl2
import Structure.v1.Atlas.TensorCategories.code.QuantumSl2Concrete
variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

/-- Zero element: the all-zero coefficient vector. -/
noncomputable instance : Zero (SmallQuantumSl2 n k) := ⟨⟨0⟩⟩

/-- Coefficient-wise addition. -/
noncomputable instance : Add (SmallQuantumSl2 n k) := ⟨fun a b => ⟨a.coeff + b.coeff⟩⟩

/-- Coefficient-wise negation. -/
noncomputable instance : Neg (SmallQuantumSl2 n k) := ⟨fun a => ⟨-a.coeff⟩⟩

/-- Coefficient-wise subtraction. -/
noncomputable instance : Sub (SmallQuantumSl2 n k) := ⟨fun a b => ⟨a.coeff - b.coeff⟩⟩

/-- Scalar multiplication by `k` on coefficients. -/
noncomputable instance instSMul : SMul k (SmallQuantumSl2 n k) := ⟨fun r a => ⟨r • a.coeff⟩⟩

end SmallQuantumSl2
