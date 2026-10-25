/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Torsors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.AddTorsor.Defs
import Instance.v1.Atlas.ArithmeticGeometry.code.Torsors


/-- Choosing a base point $t_0 \in T$ of a $G$-torsor $T$ yields an equivalence $G \simeq T$
sending $g \mapsto g +_v t_0$. -/
noncomputable def IsTorsor.equivOfBasePoint {G : Type*} {T : Type*} [AddCommGroup G]
    [IsTorsor G T] (t₀ : T) : G ≃ T :=
  Equiv.vaddConst t₀

