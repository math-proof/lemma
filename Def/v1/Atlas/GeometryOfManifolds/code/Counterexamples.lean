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
import Structure.v1.Atlas.GeometryOfManifolds.code.Counterexamples
set_option autoImplicit false

open DifferentialFormSpace


namespace KTGamma

/-- Twisted group multiplication on `KTGamma`: $(a,b,c,d)(a',b',c',d') = (a+a',\,b+b',\,c+c'+bd',\,d+d')$. -/
def mul' (g h : KTGamma) : KTGamma :=
  ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.b * h.d, g.d + h.d⟩

/-- Identity element of `KTGamma`. -/
def one' : KTGamma := ⟨0, 0, 0, 0⟩

/-- Group inverse in `KTGamma`. -/
def inv' (g : KTGamma) : KTGamma :=
  ⟨-g.a, -g.b, -g.c + g.b * g.d, -g.d⟩

end KTGamma
