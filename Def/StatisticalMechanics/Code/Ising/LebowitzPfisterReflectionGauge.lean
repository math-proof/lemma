/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterBridgeCalculus.Part3
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


def ghsiCrossExp2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf₁ hf₂ : V -> Real)
    (F : ConfigSpace V -> ConfigSpace V -> Real) : Real :=
  (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
      wJ G.edgeFinset J hf₁ a * wJ G.edgeFinset J hf₂ b * F a b) /
    (ZJ G.edgeFinset J hf₁ * ZJ G.edgeFinset J hf₂)


def replicaCrossBridgeMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf₁ hf₂ : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  ghsiCrossExp2 G J hf₁ hf₂ (fun a b =>
    Real.exp (r * replicaBridgeInteraction sites a b))


def replicaCrossBridgeMean
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf₁ hf₂ : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  ghsiCrossExp2 G J hf₁ hf₂ (fun a b =>
    replicaBridgeInteraction sites a b *
      Real.exp (r * replicaBridgeInteraction sites a b)) /
    replicaCrossBridgeMoment G J hf₁ hf₂ sites r


def replicaCrossBridgeVariance
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf₁ hf₂ : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  ghsiCrossExp2 G J hf₁ hf₂ (fun a b =>
      replicaBridgeInteraction sites a b ^ 2 *
        Real.exp (r * replicaBridgeInteraction sites a b)) /
      replicaCrossBridgeMoment G J hf₁ hf₂ sites r -
    replicaCrossBridgeMean G J hf₁ hf₂ sites r ^ 2

end
end StatMech.Ising
