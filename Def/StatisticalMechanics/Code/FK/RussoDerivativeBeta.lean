/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def edgeProductW (pf : Sym2 V → ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∏ e ∈ G.edgeFinset, (if ω e then pf e else 1 - pf e)


noncomputable def fkWeightW (pf : Sym2 V → ℝ) (q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  edgeProductW G pf ω * q ^ numClusters G ω


noncomputable def fkZW (pf : Sym2 V → ℝ) (q : ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), fkWeightW G pf q ω


noncomputable def fkProbW (pf : Sym2 V → ℝ) (q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  fkWeightW G pf q ω / fkZW G pf q


noncomputable def fkMeanW (pf : Sym2 V → ℝ) (q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), g ω * fkProbW G pf q ω


noncomputable def fkCovW (pf : Sym2 V → ℝ) (q : ℝ)
    (f g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  fkMeanW G pf q (fun ω => f ω * g ω) - fkMeanW G pf q f * fkMeanW G pf q g


noncomputable def coordR (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  if ω e then (1 : ℝ) else 0


end FK
end StatMech
