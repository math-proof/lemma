/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Russo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2


namespace StatMech

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def edgeWeight (p : ℝ) (ω : ConfigSpace E) (e : E) : ℝ :=
  if ω e then p else 1 - p


noncomputable def weightOff (p : ℝ) (e : E) (ω : ConfigSpace E) : ℝ :=
  ∏ j ∈ univ.erase e, edgeWeight p ω j


noncomputable def configWeight (p : ℝ) (ω : ConfigSpace E) : ℝ :=
  ∏ e, edgeWeight p ω e


noncomputable def prob (p : ℝ) (A : Set (ConfigSpace E)) : ℝ :=
  ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * configWeight p ω


noncomputable def pivotalProb (p : ℝ) (A : Set (ConfigSpace E)) (e : E) : ℝ :=
  ∑ ω, (Set.indicator {ω | IsPivotal e A ω} (fun _ => (1 : ℝ)) ω) * configWeight p ω


end StatMech
