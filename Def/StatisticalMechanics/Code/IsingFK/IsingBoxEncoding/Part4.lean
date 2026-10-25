/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/IsingBoxEncoding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsInfinite.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part3
open MeasureTheory
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice StatMech.Ising StatMech.Percolation


section Lattice

variable {d : ℕ}


noncomputable def latToBox (d n : ℕ) (τ : {x // x ∈ box d n} → Bool) :
    boxVerts d (n + 1) → Fin 2 :=
  fun v => if h : (v : Site d) ∈ box d n then bToF (τ ⟨v, h⟩) else 0


end Lattice
end IsingFK
end StatMech
