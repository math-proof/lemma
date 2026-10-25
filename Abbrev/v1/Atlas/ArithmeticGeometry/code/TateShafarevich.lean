/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TateShafarevich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.WeilChatelet.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WeilChatelet
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisCohomology
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.WCGroupH1
import Abbrev.v1.Atlas.ArithmeticGeometry.code.GaloisCohomology.Part3
import Def.v1.Atlas.ArithmeticGeometry.code.WCGroupH1
import Def.v1.Atlas.ArithmeticGeometry.code.TateShafarevich


noncomputable section

universe u

open NumberField GaloisCohomology

/-- The Weil-Châtelet group $\mathrm{WC}(E/k)$ of an elliptic curve $E/k$: the set of
$E$-torsors modulo $k$-isomorphism. -/
abbrev WeilChateletGroup {k : Type u} [Field k] (E : EllipticCurveOver k) : Type (u + 1) :=
  haveI := E.isElliptic
  WC k E.curve (ECurvePointsAlgClosure k E.curve)

end
