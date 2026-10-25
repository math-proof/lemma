/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part14


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_listLengthEquivTuple
    {A : Type*} (k : ℕ) :
    {l : List A // l.length = k} ≃ (Fin k → A) where
  toFun l i := l.1.get (Fin.cast l.2.symm i)
  invFun f := ⟨List.ofFn f, List.length_ofFn⟩
  left_inv := by
    rintro ⟨l, hl⟩
    apply Subtype.ext
    subst k
    exact List.ofFn_get l
  right_inv := by
    intro f
    funext i
    simp only [List.get_ofFn]
    apply congrArg f
    apply Fin.ext
    rfl

end StatMech.Onsager
