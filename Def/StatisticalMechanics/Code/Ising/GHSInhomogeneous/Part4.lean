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
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part4
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ghsiFibreUU (K : Sym2 V → ℝ) (hf : V → ℝ)
    (o x : V) (q : ConfigSpace V) : ℝ :=
  ghsiFibreExpectation G K hf (fun a b => uvar a b o * uvar a b x) q

noncomputable def ghsiFibreT (K : Sym2 V → ℝ) (hf : V → ℝ)
    (y : V) (q : ConfigSpace V) : ℝ :=
  ghsiFibreExpectation G K hf (fun a b => tvar a b y) q

noncomputable def ghsiUExpectation (K : Sym2 V → ℝ) (q : ConfigSpace V)
    (F : ConfigSpace V → ℝ) : ℝ :=
  (∑ a : ConfigSpace V, ghsiUWeight G K q a * F a) /
    ∑ a : ConfigSpace V, ghsiUWeight G K q a

noncomputable def ghsiTExpectation (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q : ConfigSpace V) (F : ConfigSpace V → ℝ) : ℝ :=
  (∑ a : ConfigSpace V, ghsiTWeight G K hf q a * F a) /
    ∑ a : ConfigSpace V, ghsiTWeight G K hf q a

end StatMech.Ising
