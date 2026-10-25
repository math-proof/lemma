/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part5
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WreathOrbits
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part2
set_option autoImplicit false
set_option maxHeartbeats 800000

open WreathOrbits YoungLattice YoungLattice.Lmn


namespace QuotientIsoLmn

variable {m n : ℕ}

noncomputable def quotientIsoLmn (m n : ℕ) :
    GridYoungDiagram m n ≃o Lmn m n where
  toFun := gridYoungToLmn
  invFun := lmnToGridYoung
  left_inv := lmnToGridYoung_gridYoungToLmn
  right_inv := gridYoungToLmn_lmnToGridYoung
  map_rel_iff' := gridYoungToLmn_le_iff _ _

def wreathSetoid (m n : ℕ) : Setoid (Finset (Fin m × Fin n)) where
  r := WreathOrbits.SameOrbit
  iseqv := {
    refl := fun S => (WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S S).mpr rfl
    symm := fun {S T} h => (WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq T S).mpr
      ((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S T).mp h).symm
    trans := fun {S T U} h₁ h₂ => (WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S U).mpr
      (((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq S T).mp h₁).trans
       ((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq T U).mp h₂))
  }

def WreathQuotient (m n : ℕ) : Type := Quotient (wreathSetoid m n)

end QuotientIsoLmn
