/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteIsingFKBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge.Part5
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.ThetaZeroBelowPc
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
open scoped BigOperators
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


noncomputable def finiteIsingXAxisTwoPointBox (β : ℝ) (n : ℕ) : ℝ :=
  ∑ σ : ConfigSpace (boxVerts 3 n),
    Ising.isingProb (boxGraph 3 n) β 0 σ *
      (Ising.spin σ (ising3DOriginBoxVertex n) *
        Ising.spin σ (ising3DXAxisBoxVertex n))


noncomputable def finiteIsingXAxisTwoPointInBox
    (β : ℝ) (N n : ℕ) (hn : n ≤ N) : ℝ :=
  ∑ σ : ConfigSpace (boxVerts 3 N),
    Ising.isingProb (boxGraph 3 N) β 0 σ *
      (Ising.spin σ (ising3DOriginBoxVertex N) *
        Ising.spin σ (ising3DXAxisBoxVertexInBox N n hn))


noncomputable def finiteIsingXAxisTwoPointInVolume
    (β : ℝ) (N n : ℕ) : ℝ :=
  if hn : n ≤ N then
    finiteIsingXAxisTwoPointInBox β N n hn
  else
    0

end Exact3D
end StatMech
