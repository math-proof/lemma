/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Theorem.v1.Atlas.GeometryOfManifolds.code.Counterexamples
set_option autoImplicit false

open DifferentialFormSpace


namespace KTGamma

instance : Group KTGamma where
  mul := mul'
  one := one'
  inv := inv'
  mul_assoc a b c := by
    show mul' (mul' a b) c = mul' a (mul' b c)
    simp only [mul']; ext <;> ring
  one_mul a := by
    show mul' one' a = a
    simp only [mul', one']; ext <;> simp
  mul_one a := by
    show mul' a one' = a
    simp only [mul', one']; ext <;> simp
  inv_mul_cancel a := by
    show mul' (inv' a) a = one'
    simp only [mul', one', inv']; ext <;> ring

end KTGamma
