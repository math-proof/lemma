/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part23
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace BrouwerFixedPoint

open Metric Set Inner

variable {X : Type u} [TopologicalSpace X]

/-- The homology endomorphism induced by `Σf : S^{n+1} → S^{n+1}` agrees, up to the
suspension isomorphism `α : H_n(S^n) ≅ H_{n+1}(S^{n+1})`, with the endomorphism induced by
`f` on `H_n(S^n)`. -/
lemma update_neg_mem_sphere (n : ℕ) (i : Fin (n + 1))
    (x : SphereHomology.Sphere n) :
    (WithLp.equiv 2 _).symm (Function.update (WithLp.equiv 2 _ x.1) i (-(x.1 i))) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  have hx := x.2
  simp only [Metric.mem_sphere, dist_zero_right] at hx ⊢
  simp only [EuclideanSpace.norm_eq] at hx ⊢
  rw [show (∑ j : Fin (n + 1), ‖((WithLp.equiv 2 _).symm
    (Function.update (WithLp.equiv 2 _ x.1) i (-(x.1 i)))).ofLp j‖ ^ 2) =
    (∑ j : Fin (n + 1), ‖x.1.ofLp j‖ ^ 2) from by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i
      · subst h; simp [Function.update_self, norm_neg]
      · simp [Function.update_of_ne h]]
  exact hx

/-- The coordinate reflection map on `ℝ^{n+1}` (negating the `i`-th coordinate) is
continuous. -/
lemma continuous_update_neg (n : ℕ) (i : Fin (n + 1)) :
    Continuous (fun v : EuclideanSpace ℝ (Fin (n + 1)) =>
      (WithLp.equiv 2 _).symm (Function.update (WithLp.equiv 2 _ v) i (-(v i)))) :=
  (PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℝ)).symm.continuous.comp
    (Continuous.update (PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℝ)).continuous i
      (((continuous_apply i).comp
        (PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℝ)).continuous).neg))

end BrouwerFixedPoint
