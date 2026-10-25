/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWAspectInduction
import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


noncomputable def cti_edgeEquiv (v : Site 2) : Sym2 (Site 2) ≃ Sym2 (Site 2) :=
  (sym2Congr (Equiv.addRight v)).symm


end Universality
end StatMech
