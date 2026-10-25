/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWAspectInduction
import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


def sym2Congr {α β : Type*} (e : α ≃ β) : Sym2 α ≃ Sym2 β where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv x := by rw [Sym2.map_map]; simp
  right_inv x := by rw [Sym2.map_map]; simp

end Universality
end StatMech
