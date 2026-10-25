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
import Def.v1.Atlas.ArithmeticGeometry.code.TorsorIffJacobian
set_option autoImplicit false


noncomputable section

universe u

variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts] {C_pts : Type u}


/-- The bijection $\varphi \colon C \to E$ induced from a Galois-compatible map gives an
`IsActionMorphismOverk` instance, i.e. the resulting $E$-action on $C$ is a $k$-morphism. -/
theorem isActionMorphismOverk_of_galoisCompat
    (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) [hne : Nonempty C_pts]
    (φ : C_pts ≃ E_pts) :
    @IsActionMorphismOverk _ _ W _ E_pts _ C_pts (addTorsorOfEquiv E_pts C_pts φ) :=
  IsActionMorphismOverk.ofEquiv k W E_pts C_pts φ

end
