/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finite
import Def.v1.Atlas.ArithmeticGeometry.code.EffectiveDivisors
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.EffectiveDivisors
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CanonicalDivisors
import Def.v1.Atlas.ArithmeticGeometry.code.CanonicalDivisors.Part2
import Theorem.v1.Atlas.ArithmeticGeometry.code.RiemannRoch
open scoped RestrictedProduct

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}


namespace FunctionFieldAdeleRing

/-- A subfield $k \subseteq F$ is called a *field of constants* for the family of valuation
subrings $(O_p)$ if every element of $k$ is integral at every place $p$ and each residue
field $O_p / \mathfrak{m}_p$ is finite-dimensional over $k$. -/
class ConstantField (k : Type*) {F : Type*} {P : Type*} [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F} : Prop where
  algebraMap_mem : ∀ (p : P) (c : k), algebraMap k F c ∈ O p
  residueField_finiteDimensional : ∀ (p : P),
    letI : Algebra k ↥(O p) :=
      ((algebraMap k F).codRestrict (O p).toSubring (fun c => algebraMap_mem p c)).toAlgebra
    letI : Algebra k (IsLocalRing.ResidueField ↥(O p)) :=
      (IsLocalRing.residue ↥(O p) |>.comp (algebraMap k ↥(O p))).toAlgebra
    FiniteDimensional k (IsLocalRing.ResidueField ↥(O p))

end FunctionFieldAdeleRing
