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
import Theorem.v1.Atlas.ArithmeticGeometry.code.TorsorIffJacobian
set_option autoImplicit false


noncomputable section

universe u

variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts] {C_pts : Type u}


/-- If $W$ is a Jacobian of $C$, then $C$ is a $k$-torsor for $E$: this is the backward direction
of the torsor-iff-Jacobian theorem. -/
def isJacobianOf_imp_isETorsor
    (hJ : IsJacobianOf k W E_pts C_pts) :
    IsETorsor k W E_pts C_pts := by
  have hg := hJ.1


  let hexists := hJ.2

  let φ : C_pts ≃ E_pts :=
    hexists.choose_spec.choose

  have hne : Nonempty C_pts := ⟨φ.symm 0⟩
  exact
  { toAddTorsor := addTorsorOfEquiv E_pts C_pts φ
    genusOne := hg
    actionMorphism := isActionMorphismOverk_of_galoisCompat k W E_pts C_pts φ }

end
