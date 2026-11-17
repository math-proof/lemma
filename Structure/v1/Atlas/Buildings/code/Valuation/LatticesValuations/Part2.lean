/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/LatticesValuations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Def.v1.Atlas.Buildings.code.Valuation.LatticesValuations
public section

open Polynomial Matrix


namespace DVRContext

variable (C : DVRContext)

attribute [instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

/-- *An $\mathfrak{o}$-lattice in $V = k^n$*: a subset $\Lambda \subseteq k^n$ that is an
$\mathfrak{o}$-submodule (contains zero, is closed under addition and under the action of
$\mathfrak{o}$), spans $V$ as a $k$-vector space, and is closed under $\mathfrak{o}$-linear
combinations of $n$ vectors with $\mathfrak{o}$-coefficients (used as a substitute for finite
generation over $\mathfrak{o}$). -/
structure OLattice where
  carrier : Set (Fin C.n → C.k)
  zero_mem : (0 : Fin C.n → C.k) ∈ carrier
  add_mem : ∀ {x y}, x ∈ carrier → y ∈ carrier → x + y ∈ carrier
  smul_mem : ∀ (r : C.𝔬) {x}, x ∈ carrier → C.oscal r x ∈ carrier
  spans_V : ∀ v : Fin C.n → C.k,
    ∃ (m : ℕ) (cs : Fin m → C.k) (vs : Fin m → Fin C.n → C.k),
      (∀ j, vs j ∈ carrier) ∧ v = ∑ j, cs j • vs j
  closed_under_o_combination :
    ∀ (coeffs : Fin C.n → C.k) (vectors : Fin C.n → (Fin C.n → C.k)),
      (∀ i, C.isInO (coeffs i)) →
      (∀ i, vectors i ∈ carrier) →
      (∑ i, coeffs i • vectors i) ∈ carrier

end DVRContext
