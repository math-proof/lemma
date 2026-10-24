/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdelePlusFDim.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.AdeleQuotientDim
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

/-- Lemma 22.10. For divisors $A \le B$, the quotient
$(A(B) + F) / (A(A) + F)$ is finite-dimensional over $k$ and its dimension is
$\delta(B) - \delta(A)$, the difference of Riemann defects. Combines Lemmas
22.8 and 22.9 via the modular-lattice identity. -/
end Lemma22_9
