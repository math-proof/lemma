/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TorsorIffJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.WeilChatelet.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WeilChatelet
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.JInvariant
import Def.v1.Atlas.ArithmeticGeometry.code.JInvariant.Part3
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Abbrev.v1.Atlas.ArithmeticGeometry.code.TorsorIffJacobian
set_option autoImplicit false


noncomputable section

universe u

/-- The absolute Galois group `AbsGaloisGroup k` is a group under composition. -/
noncomputable instance AbsGaloisGroup.instGroup (k : Type u) [Field k] :
    Group (AbsGaloisGroup k) :=
  inferInstance

end
