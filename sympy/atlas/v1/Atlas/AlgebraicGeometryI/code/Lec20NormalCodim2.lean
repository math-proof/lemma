/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20NormalCodim2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Noetherian.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec21NormalExtension
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec21NormalExtension

noncomputable section

open PrimeSpectrum
