/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInhom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part3
import Def.StatisticalMechanics.Code.Sharpness.BkCriterionInhom
open scoped BigOperators
open Finset


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

variable {E V : Type*}


theorem shk_edgeLaw_nonneg (beta : ℝ) (J : E → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (e : E) (b : Bool) :
    0 ≤ shk_edgeLaw beta J e b := by
  cases b with
  | false => exact (Real.exp_pos _).le
  | true =>
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbeta) (hJ e)))

theorem shk_edgeLaw_sum_one (beta : ℝ) (J : E → ℝ) (e : E) :
    shk_edgeLaw beta J e false + shk_edgeLaw beta J e true = 1 := by
  simp [shk_edgeLaw]


theorem bk_criterion_inhomogeneous [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (J : Sym2 V → ℝ) (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A : Set V) (S : Finset V) (B : Set V) (u : V)
    (huS : u ∈ S) (hBS : ∀ z ∈ B, z ∉ S) :
    wprob (shk_edgeLaw beta J) (connEvent G A u B) ≤
      ∑ q ∈ shk_boundaryPairs G S,
        (1 - Real.exp (-beta * J s(q.1, q.2))) *
          wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) u {q.1}) *
          wprob (shk_edgeLaw beta J) (connEvent G A q.2 B) := by
  let F : V × V → Set (ConfigSpace (Sym2 V)) := fun q =>
    disjointOccurrence (connEvent G (S : Set V) u {q.1})
      (disjointOccurrence (edgeOpenEvent q.1 q.2) (connEvent G A q.2 B))
  have hincl := shk_firstExit_inclusion G A S B u huS hBS
  calc
    wprob (shk_edgeLaw beta J) (connEvent G A u B) ≤
        wprob (shk_edgeLaw beta J) (⋃ q ∈ shk_boundaryPairs G S, F q) :=
      wprob_mono (fun e b => shk_edgeLaw_nonneg beta J hbeta hJ e b) hincl
    _ ≤ ∑ q ∈ shk_boundaryPairs G S, wprob (shk_edgeLaw beta J) (F q) :=
      shk_wprob_biUnion_le (shk_edgeLaw beta J)
        (fun e b => shk_edgeLaw_nonneg beta J hbeta hJ e b) _ F
    _ ≤ ∑ q ∈ shk_boundaryPairs G S,
        wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) u {q.1}) *
          wprob (shk_edgeLaw beta J) (edgeOpenEvent q.1 q.2) *
          wprob (shk_edgeLaw beta J) (connEvent G A q.2 B) := by
      apply Finset.sum_le_sum
      intro q _
      exact shk_bk_triple_inhom (shk_edgeLaw beta J)
        (fun e b => shk_edgeLaw_nonneg beta J hbeta hJ e b)
        (shk_edgeLaw_sum_one beta J)
        (isIncreasing_connEvent G (S : Set V) u {q.1})
        (isIncreasing_edgeOpenEvent q.1 q.2)
        (isIncreasing_connEvent G A q.2 B)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      change _ * wprob (shk_edgeLaw beta J)
        {omega : ConfigSpace (Sym2 V) | omega s(q.1, q.2) = true} * _ = _
      rw [shk_wprob_edgeOpen (shk_edgeLaw beta J) (shk_edgeLaw_sum_one beta J)]
      change _ * (1 - Real.exp (-beta * J s(q.1, q.2))) * _ = _
      ring

end Sharpness
end StatMech
