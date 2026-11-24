module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.WindingBridge.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.InteriorRegion


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager.InteriorRegion

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches

open StatMech.Onsager.WindingBridge


noncomputable def Lcells : Finset Pt :=
  ((Finset.Icc (0 : ℤ) 3) ×ˢ (Finset.Icc (0 : ℤ) 3)).filter (fun q => ¬ (q.1 ≤ 1 ∧ q.2 ≤ 1))


end StatMech.Onsager.InteriorRegion
