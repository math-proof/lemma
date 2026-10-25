/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InhomogeneousFKG
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.FK.ActiveEdges
open scoped BigOperators
open Finset


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def activeWeight (pf : Sym2 V → ℝ) (q : ℝ)
    (ω : ConfigSpace G.edgeSet) : ℝ :=
  fkWeightW G pf q (extendActive G ω)


noncomputable def activeZ (pf : Sym2 V → ℝ) (q : ℝ) : ℝ :=
  ∑ ω : ConfigSpace G.edgeSet, activeWeight G pf q ω


noncomputable def activeProb (pf : Sym2 V → ℝ) (q : ℝ)
    (ω : ConfigSpace G.edgeSet) : ℝ :=
  activeWeight G pf q ω / activeZ G pf q


noncomputable def activeMean (pf : Sym2 V → ℝ) (q : ℝ)
    (f : ConfigSpace G.edgeSet → ℝ) : ℝ :=
  ∑ ω, f ω * activeProb G pf q ω


noncomputable def activeCov (pf : Sym2 V → ℝ) (q : ℝ)
    (f g : ConfigSpace G.edgeSet → ℝ) : ℝ :=
  activeMean G pf q (fun ω => f ω * g ω) -
    activeMean G pf q f * activeMean G pf q g


noncomputable def activeNumer (pf : Sym2 V → ℝ) (q : ℝ)
    (f : ConfigSpace G.edgeSet → ℝ) : ℝ :=
  ∑ ω, f ω * activeWeight G pf q ω


noncomputable def activeBetaScore (J : Sym2 V → ℝ) (β : ℝ)
    (ω : ConfigSpace G.edgeSet) : ℝ :=
  ∑ e : G.edgeSet, (J e.1 / betaParams J β e.1) *
    (OSSS.Lindeberg.coord e ω - betaParams J β e.1)


noncomputable def activeProbOf (pf : Sym2 V → ℝ) (q : ℝ)
    (A : Set (ConfigSpace G.edgeSet)) : ℝ :=
  activeMean G pf q (A.indicator (fun _ => (1 : ℝ)))

end FK
end StatMech
