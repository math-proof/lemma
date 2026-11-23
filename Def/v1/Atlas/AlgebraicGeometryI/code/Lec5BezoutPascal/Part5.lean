/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutMultiplicitySum.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutMultiplicitySum
public import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal.Part2

@[expose] public section

open MvPolynomial Classical


noncomputable section

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- Cyclic successor on `Fin 6`, used to index the sides of an inscribed hexagon. -/
def hexNext (i : Fin 6) : Fin 6 := ⟨(i.val + 1) % 6, Nat.mod_lt _ (by omega)⟩

/-- Opposite vertex map on `Fin 6` (shift by 3), used to pair opposite sides of an inscribed
hexagon. -/
def hexOpposite (i : Fin 6) : Fin 6 := ⟨(i.val + 3) % 6, Nat.mod_lt _ (by omega)⟩

/-- The `i`-th side of an inscribed hexagon: the line through the `i`-th and `(i + 1)`-th
vertices. -/
def PascalInscribedHexagon.side (H : PascalInscribedHexagon k) (i : Fin 6) :
    MvPolynomial (Fin 3) k :=
  lineThroughPoints k (H.vertex i) (H.vertex (hexNext i))

end Lec5BezoutPascal
end
