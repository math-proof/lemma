/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Def.v1.Atlas.ArithmeticGeometry.code.PadicCompletion

@[expose] public section

universe u


namespace InverseLimit

variable {S : ℕ → Type u} (fn : (n : ℕ) → S (n + 1) → S n)

/-- `PolyRootSet f n` is a finite type, being a subtype of the finite ring
$\mathbb{Z}/p^n\mathbb{Z}$. -/
instance polyRootSetFintype (f : Polynomial ℤ_[p]) (n : ℕ) :
    Fintype (PolyRootSet f n) :=
  Subtype.fintype _

end InverseLimit
