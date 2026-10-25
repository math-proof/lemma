/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeArmClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Def.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem stac_colorOf_faithful (ω : ConfigSpace (Sym2 (Site d))) (x₀ : Site d)
    (a : Fin 3 → Site d)
    (hsep : ∀ i j, i ≠ j → ¬ Connected d (removeSite x₀ ω) (a i) (a j))
    (hcover : ∀ w, Connected d ω x₀ w → x₀ ≠ w →
      ∃ i, Connected d (removeSite x₀ ω) (a i) (fsp_armWitness ω x₀ w))
    {u v : Site d} (hu : Connected d ω x₀ u) (hneu : x₀ ≠ u)
    (hv : Connected d ω x₀ v) (hnev : x₀ ≠ v) :
    stac_colorOf ω x₀ a u = stac_colorOf ω x₀ a v ↔ fsp_sameArm ω x₀ u v := by
  classical
  unfold stac_colorOf fsp_sameArm
  rw [dif_pos (hcover u hu hneu), dif_pos (hcover v hv hnev)]
  set i := (hcover u hu hneu).choose with hi
  set j := (hcover v hv hnev).choose with hj
  have hispec : Connected d (removeSite x₀ ω) (a i) (fsp_armWitness ω x₀ u) :=
    (hcover u hu hneu).choose_spec
  have hjspec : Connected d (removeSite x₀ ω) (a j) (fsp_armWitness ω x₀ v) :=
    (hcover v hv hnev).choose_spec
  constructor
  · intro hij
    rw [← hij] at hjspec
    exact hispec.symm.trans hjspec
  · intro hsame
    by_contra hijne
    exact hsep i j hijne (hispec.trans (hsame.trans hjspec.symm))


end Percolation
end StatMech
