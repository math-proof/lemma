/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerODE
import Def.StatisticalMechanics.Code.SLE.LoewnerProps.Part3
open Complex Set Filter Topology
open scoped NNReal ComplexConjugate


namespace StatMech.SLE

theorem subset_of_monotoneHull {K : ℝ → Set ℂ} (h : MonotoneHullFamily K)
    {s t : ℝ} (hst : s ≤ t) : K s ⊆ K t :=
  h.2 hst


theorem complement_antitone_of_monotoneHull {K : ℝ → Set ℂ}
    (h : MonotoneHullFamily K) :
    Antitone (fun t => upperHalfPlane \ K t) :=
  fun _ _ hst => Set.diff_subset_diff_right (h.2 hst)


theorem isCompactHull_of_monotoneHull {K : ℝ → Set ℂ} (h : MonotoneHullFamily K)
    (t : ℝ) : IsCompactHull (K t) :=
  h.1 t

end StatMech.SLE
