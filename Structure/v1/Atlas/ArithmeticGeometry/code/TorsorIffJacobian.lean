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
import Instance.v1.Atlas.ArithmeticGeometry.code.TorsorIffJacobian
set_option autoImplicit false


noncomputable section

universe u

/-- A `GaloisAction G E_pts C_pts` packages an action of the group $G$ on both the elliptic curve
points $E$ (as additive equivalences) and on a torsor candidate $C$ (as set equivalences). -/
structure GaloisAction (G : Type u) [Group G] (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) where
  actE : G → E_pts ≃+ E_pts
  actC : G → C_pts ≃ C_pts

end
