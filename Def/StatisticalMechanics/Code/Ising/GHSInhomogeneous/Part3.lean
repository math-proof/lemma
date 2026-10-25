/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.Sharpness.GHSConcavity
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part3
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ghsiFibreWeight (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) : ℝ :=
  wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a)

noncomputable def ghsiFibreMass (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q : ConfigSpace V) : ℝ :=
  ∑ a : ConfigSpace V, ghsiFibreWeight G K hf q a

noncomputable def ghsiFibreNumerator (K : Sym2 V → ℝ) (hf : V → ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) (q : ConfigSpace V) : ℝ :=
  ∑ a : ConfigSpace V, ghsiFibreWeight G K hf q a * F a (ghsLMate q a)

noncomputable def ghsiFibreExpectation (K : Sym2 V → ℝ) (hf : V → ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) (q : ConfigSpace V) : ℝ :=
  ghsiFibreNumerator G K hf F q / ghsiFibreMass G K hf q

noncomputable def ghsiAgreementProb (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q : ConfigSpace V) : ℝ :=
  ghsiFibreMass G K hf q / (ZJ G.edgeFinset K hf) ^ 2

end StatMech.Ising
