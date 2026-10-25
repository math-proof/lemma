/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part10
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusDissemination.Part6
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorusIndexedField_polarizeLowerIndexAt
    (i : Fin d) (a : IsingDyadicTorus d k)
    (h : IsingDyadicTorus d k → Real)
    (g : IsingDyadicTorus d k → IsingDyadicTorus d k) :
    isingTorusIndexedField h (isingTorusPolarizeLowerIndexAt i a g) =
      isingTorusPolarizeLowerAt i a (isingTorusIndexedField h g) := by
  funext x
  unfold isingTorusIndexedField isingTorusPolarizeLowerIndexAt
    isingTorusPolarizeLowerAt isingTorusTranslateField
    isingTorusPolarizeLower
  split_ifs <;> rfl

theorem isingTorusIndexedField_polarizeUpperIndexAt
    (i : Fin d) (a : IsingDyadicTorus d k)
    (h : IsingDyadicTorus d k → Real)
    (g : IsingDyadicTorus d k → IsingDyadicTorus d k) :
    isingTorusIndexedField h (isingTorusPolarizeUpperIndexAt i a g) =
      isingTorusPolarizeUpperAt i a (isingTorusIndexedField h g) := by
  funext x
  unfold isingTorusIndexedField isingTorusPolarizeUpperIndexAt
    isingTorusPolarizeUpperAt isingTorusTranslateField
    isingTorusPolarizeUpper
  split_ifs <;> rfl


theorem isingTorus_polarizeLower_preserves_indexed_max
    (i : Fin d) (a : IsingDyadicTorus d k)
    (beta : Real) (hbeta : 0 ≤ beta)
    (h : IsingDyadicTorus d k → Real)
    (g : IsingDyadicTorus d k → IsingDyadicTorus d k)
    (hmax : ∀ g' : IsingDyadicTorus d k → IsingDyadicTorus d k,
      isingTorusShiftedPartition beta (isingTorusIndexedField h g') ≤
        isingTorusShiftedPartition beta (isingTorusIndexedField h g)) :
    isingTorusShiftedPartition beta
        (isingTorusIndexedField h (isingTorusPolarizeLowerIndexAt i a g)) =
      isingTorusShiftedPartition beta (isingTorusIndexedField h g) := by
  let gl := isingTorusPolarizeLowerIndexAt i a g
  let gu := isingTorusPolarizeUpperIndexAt i a g
  have hl := hmax gl
  have hu := hmax gu
  rw [isingTorusIndexedField_polarizeLowerIndexAt] at hl ⊢
  rw [isingTorusIndexedField_polarizeUpperIndexAt] at hu
  have hp := isingTorusShiftedPartition_polarization_at
    i a beta hbeta (isingTorusIndexedField h g)
  linarith


end StatMech.FrontierA
