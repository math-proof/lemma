/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
public import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
public import Def.v1.Atlas.GeometryOfManifolds.code.Counterexamples
set_option autoImplicit false

open DifferentialFormSpace

public section

namespace KTGamma

/-- Extensionality for `KTGamma`: two elements are equal iff all four components agree. -/
@[ext] theorem ext {g h : KTGamma} (ha : g.a = h.a) (hb : g.b = h.b)
    (hc : g.c = h.c) (hd : g.d = h.d) : g = h := by
  cases g; cases h; simp_all

end KTGamma
