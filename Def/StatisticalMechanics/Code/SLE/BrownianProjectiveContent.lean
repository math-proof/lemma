/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveContent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianFiniteDimensional.Part4
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.SLE

noncomputable def brownianProjectiveContent :
    AddContent ENNReal (measurableCylinders fun _ : Real => Real) :=
  projectiveFamilyContent brownianFiniteDimensionalPiLaw_isProjective


end StatMech.SLE
