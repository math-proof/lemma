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
import Abbrev.v1.Atlas.ArithmeticGeometry.code.AdelePlusFDim
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

/-- Riemann-Roch space $L(D) = \{f \in F \mid \mathrm{ord}_p(f) \ge -D(p)
\text{ for all } p\}$ realized as the preimage of $A(D)$ under the diagonal
embedding $F \hookrightarrow \mathbb{A}_F$. -/
noncomputable def rrSpaceAdele (D : P → ℤ) : Submodule k F :=
  Submodule.comap (diagonalLinearMap (F := F) (P := P) (O := O) k)
    (adeleSpace (F := F) (O := O) k D)

/-- $A(D) \cap F$ is finite-dimensional, as image of the finite-dimensional
$L(D)$ under the injective diagonal embedding. -/
noncomputable def ellD (D : P →₀ ℤ) : ℕ :=
  Module.finrank k (rrSpaceAdele (F := F) (O := O) k (D : P → ℤ))

/-- The *Riemann defect* attached to a divisor $D$:
$\delta(D) = \deg D + 1 - \ell(D)$, whose constant value (over varying $D$) is
the genus $g$ in the Riemann-Roch theorem. -/
noncomputable def riemannDefect (D : P →₀ ℤ) : ℤ :=
  adeleDivisorDeg (F := F) (k := k) (O := O) D + 1 -
    (ellD (F := F) (O := O) k D : ℤ)

end Lemma22_9
