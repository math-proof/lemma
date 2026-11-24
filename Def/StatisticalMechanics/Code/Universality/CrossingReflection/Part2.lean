module
public import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


noncomputable def crf_edgeEquiv : Sym2 (Site 2) ≃ Sym2 (Site 2) := sym2Congr crf_swap


end Universality
end StatMech
