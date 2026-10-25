/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.FunctionFieldGenerators
import Def.v1.Atlas.ArithmeticGeometry.code.ProductVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProductVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CotangentLocal
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RegularFunctions
import Def.v1.Atlas.ArithmeticGeometry.code.CotangentLocal.Part3
import Def.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part9
import Def.v1.Atlas.ArithmeticGeometry.code.TangentSpaces.Part2


noncomputable section

open Matrix Module Submodule LinearMap FiniteDimensional MvPolynomial

section GeometricTangentSpace

variable {k : Type*} [Field k] {n : ℕ}

noncomputable instance (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    Field (functionField k N V hV) := functionField.instField k N V hV

end GeometricTangentSpace
end
