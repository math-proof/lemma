/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Structure.v1.Atlas.Buildings.code.HeckeAlgebra.Generic.Part2


namespace HeckeAlgebra

variable {B : Type*} {W : Type*} [Group W] {M : CoxeterMatrix B}

variable {R : Type*} [CommRing R]

section CoxeterLemmas

variable {M : CoxeterMatrix B}

/-- Converts Iwahori–Hecke parameters $q_s$ into the generic structure constants
$(a_s, b_s) = (q_s - 1, q_s)$. -/
def IwahoriHeckeData.toStructureConstants (d : IwahoriHeckeData B R) :
    StructureConstants B R where
  a s := d.q s - 1
  b s := d.q s

end CoxeterLemmas
end HeckeAlgebra
