/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightRootCutHallEquivalence
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalMaskRightLeftDegree
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) : Nat := by
  classical
  exact Fintype.card {q : rightMaskFiber ends m j k l zero p //
    q ∈ canonicalMaskRightImages ends m j k l zero p c}


noncomputable def canonicalMaskRightRightDegree
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (q : rightMaskFiber ends m j k l zero p) : Nat := by
  classical
  exact Fintype.card {c : leftMaskFiber ends m j k l zero p //
    q ∈ canonicalMaskRightImages ends m j k l zero p c}


def CanonicalMaskRightEdgeDegreeDominance
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ c : leftMaskFiber ends m j k l zero p,
    ∀ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p c ->
        canonicalMaskRightRightDegree ends m j k l zero p q <=
          canonicalMaskRightLeftDegree ends m j k l zero p c


def CanonicalMaskRightEdgePreimageEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ c : leftMaskFiber ends m j k l zero p,
    ∀ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p c ->
        Nonempty
          ({d : leftMaskFiber ends m j k l zero p //
              q ∈ canonicalMaskRightImages ends m j k l zero p d} ↪
            {r : rightMaskFiber ends m j k l zero p //
              r ∈ canonicalMaskRightImages ends m j k l zero p c})


end StatMech.GrahamGHS.FourColor
