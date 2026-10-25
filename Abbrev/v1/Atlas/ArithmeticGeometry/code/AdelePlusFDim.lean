/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdelePlusFDim.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.AdeleQuotientDim.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AdeleQuotientDim
import Mathlib.Order.ModularLattice
open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily


section Lemma22_9

variable {F : Type*} [Field F] {P : Type*} [DecidableEq P]
  {O : P → ValuationSubring F}
  (k : Type*) [Field k] [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  [HasResidueFieldSurjection P F k O]

/-- The $k$-subspace $A(D) + F \subseteq \mathbb{A}_F$: the sum of the adele
divisor space $A(D)$ and the principal adeles (the image of $F$ embedded
diagonally). -/
noncomputable abbrev AF_subspace (D : P → ℤ) :
    Submodule k (FunctionFieldAdeleRing F P O) :=
  adeleSpace (F := F) (O := O) k D ⊔ principalAdeles (F := F) (P := P) (O := O) k

/-- The $k$-subspace $A(D) \cap F$ inside $\mathbb{A}_F$: elements of the
function field that satisfy the divisor bounds at every place. -/
noncomputable abbrev LF_subspace (D : P → ℤ) :
    Submodule k (FunctionFieldAdeleRing F P O) :=
  adeleSpace (F := F) (O := O) k D ⊓ principalAdeles (F := F) (P := P) (O := O) k

end Lemma22_9
