/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Twists.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Def.v1.Atlas.ArithmeticGeometry.code.JInvariant.Part3
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.JInvariant
import Def.v1.Atlas.ArithmeticGeometry.code.Twists
open AlgebraicGeometry CategoryTheory Limits

universe u


namespace ArithmeticGeometry

variable (k : Type u) [Field k]

/-- The base change $X_{\overline{k}}$ is canonically a scheme over
$\mathrm{Spec}\, \overline{k}$. -/
noncomputable instance baseChangeToAlgClosure_over (X : Scheme.{u}) [X.Over (specOf k)] :
    (baseChangeToAlgClosure k X).Over (specOf (AlgebraicClosure k)) :=
  Scheme.canonicallyOverPullback.toOverClass

end ArithmeticGeometry
