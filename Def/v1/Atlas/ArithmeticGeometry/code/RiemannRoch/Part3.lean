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
import Class.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part2
open scoped RestrictedProduct

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}


namespace FunctionFieldAdeleRing

variable [ConstantField k (O := O)]

variable [DiscreteValuationFamily P F k]

open DiscreteValuationFamily in
/-- The adele subspace $\mathbb{A}_F(D) := \{\alpha \in \mathbb{A}_F :
\operatorname{ord}_p(\alpha_p) \ge -D(p) \text{ for all } p\}$ associated to a
$\mathbb{Z}$-valued divisor $D$. -/
noncomputable def adeleSpace (D : P → ℤ) :
    Submodule k (FunctionFieldAdeleRing F P O) where
  carrier := { α | ∀ p, ord (k := k) p (α p) ≥ ↑(-D p) }
  add_mem' {α β} hα hβ p :=
    le_trans (le_min (hα p) (hβ p)) (ord_add_ge_min (k := k) p (α p) (β p))
  zero_mem' p := by
    simp only [show (0 : FunctionFieldAdeleRing F P O) p = 0 from rfl, ord_zero]
    exact le_top
  smul_mem' c α hα p := by
    simp only [smul_apply]
    by_cases hc : c = 0
    · simp only [hc, map_zero, zero_mul, ord_zero]; exact le_top
    · rw [ord_mul, ord_algebraMap p c hc]; simp; exact hα p

end FunctionFieldAdeleRing
