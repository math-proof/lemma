/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Theorem.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangAsano
open scoped ComplexConjugate


namespace StatMech.FrontierA

def IsMultiAffine {I : Type*} [DecidableEq I] (p : (I → ℂ) → ℂ) : Prop :=
  ∀ (i : I) (z : I → ℂ) (t : ℂ),
    p (Function.update z i t) =
      p (Function.update z i 0) +
        t * (p (Function.update z i 1) - p (Function.update z i 0))

def PolydiscStable {I : Type*} (p : (I → ℂ) → ℂ) : Prop :=
  ∀ z : I → ℂ, (∀ i, ‖z i‖ < 1) → p z ≠ 0

def asanoContract {I : Type*} [DecidableEq I]
    (p : (I → ℂ) → ℂ) (i j : I) :
    (I → ℂ) → ℂ := fun z ↦
  let z00 := Function.update (Function.update z i 0) j 0
  let z10 := Function.update (Function.update z i 1) j 0
  let z01 := Function.update (Function.update z i 0) j 1
  let z11 := Function.update (Function.update z i 1) j 1
  p z00 + z i * (p z11 - p z10 - p z01 + p z00)

end StatMech.FrontierA
