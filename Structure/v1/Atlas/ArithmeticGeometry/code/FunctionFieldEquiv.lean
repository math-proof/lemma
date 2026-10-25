/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FunctionFieldEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part10
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CurveTheory


noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace ArithmeticGeometry

namespace Thm19_2

variable (k : Type u) [Field k] [PerfectField k]

structure FunctionFieldCat where
  carrier : Type u
  [fieldInst : Field carrier]
  [algInst : Algebra k carrier]
  finitelyGenerated : (⊤ : IntermediateField k carrier).FG
  transcendenceDegreeOne : ∃ (x : carrier), Transcendental k x ∧
    Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) carrier
  algClosedInF : ∀ (x : carrier), IsAlgebraic k x → x ∈ Set.range (algebraMap k carrier)

end Thm19_2
end ArithmeticGeometry
end
