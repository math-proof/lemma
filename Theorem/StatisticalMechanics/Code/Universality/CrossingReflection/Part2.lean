/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Def.StatisticalMechanics.Code.Universality.CrossingReflection.Part2
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem crf_edgeEquiv_symm_apply (e : Sym2 (Site 2)) :
    crf_edgeEquiv.symm e = e.map crf_swap := by simp [crf_edgeEquiv, sym2Congr]


end Universality
end StatMech
