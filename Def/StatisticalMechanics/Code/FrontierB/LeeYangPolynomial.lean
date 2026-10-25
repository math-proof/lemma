/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LeeYangPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
open scoped BigOperators
open Finset Polynomial


namespace StatMech

namespace FrontierB

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def minusSpinCount (s : ConfigSpace V) : ℕ :=
  (Finset.univ.filter fun x => s x = false).card


noncomputable def zeroFieldInteractionWeight (β : ℝ) (s : ConfigSpace V) : ℝ :=
  Real.exp (β * ∑ e ∈ G.edgeFinset, bond s e)


noncomputable def leeYangPolynomial (β : ℝ) : ℝ[X] :=
  ∑ s : ConfigSpace V,
    Polynomial.C (zeroFieldInteractionWeight G β s) *
      Polynomial.X ^ minusSpinCount s


noncomputable def leeYangComplexPolynomial (β : ℝ) : ℂ[X] :=
  (leeYangPolynomial G β).map (algebraMap ℝ ℂ)

end FrontierB
end StatMech
