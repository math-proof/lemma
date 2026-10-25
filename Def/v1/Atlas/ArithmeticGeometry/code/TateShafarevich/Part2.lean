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
import Instance.v1.Atlas.ArithmeticGeometry.code.TateShafarevich.Part2


noncomputable section

universe u

open NumberField GaloisCohomology

/-- The isomorphism between the Weil-Châtelet group of $E/k$ (torsors mod $k$-isomorphism) and
the first Galois cohomology group $H^1(\mathrm{Gal}(\bar k/k), E(\bar k))$. -/
noncomputable def WeilChatelet_iso_H1 {k : Type u} [Field k] (E : EllipticCurveOver k) :
    WeilChateletGroup E ≃+ GaloisCohomologyH1 k E :=
  haveI := E.isElliptic
  wc_h1_equiv (WCH1Data.mk' k E.curve (ECurvePointsAlgClosure k E.curve)
    (AbsGaloisGroup k))


end
