/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def openEdgeCount (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∑ e ∈ G.edgeFinset, (if ω e then (1 : ℝ) else 0)


noncomputable def fkMean (p q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), g ω * fkProb G p q ω


noncomputable def fkCov (p q : ℝ) (f g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  fkMean G p q (fun ω => f ω * g ω) - fkMean G p q f * fkMean G p q g


noncomputable def coord (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  if ω e then (1 : ℝ) else 0


end FK
end StatMech
