/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.NoetherNormalization
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NoetherNormalization
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NakayamaApplications
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NoetherNullstellensatzChain
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.LinearChangeVariables
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NoetherianTopological
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec2AffineVarieties
import Theorem.v1.Atlas.AlgebraicGeometryI.code.NakayamaApplications
import Theorem.v1.Atlas.AlgebraicGeometryI.code.NoetherNullstellensatzChain
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.LinearChangeVariables
import Def.v1.Atlas.AlgebraicGeometryI.code.NoetherianTopological
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec2AffineVarieties.Part3
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.FieldTheory.IsAlgClosed.Basic
set_option maxHeartbeats 800000


attribute [local instance] MvPolynomial.gradedAlgebra

open PrimeSpectrum TopologicalSpace AlgebraicGeometry


noncomputable section thm31_section

open CategoryTheory

universe v

end thm31_section
