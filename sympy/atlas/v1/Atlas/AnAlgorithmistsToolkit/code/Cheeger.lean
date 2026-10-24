/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Cheeger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.InnerProductSpace.Basic

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def edgeCut (S : Finset V) : ℕ :=
  (G.interedges S Sᶜ).card

noncomputable def cutRatio (S : Finset V) : ℚ :=
  (G.edgeCut S : ℚ) / (min S.card Sᶜ.card : ℚ)

noncomputable def edgeExpansion : ℚ :=
  let candidates := (Finset.univ : Finset (Finset V)).filter
    (fun S => S.Nonempty ∧ S ≠ Finset.univ)
  if h : candidates.Nonempty then
    candidates.inf' h (G.cutRatio)
  else
    0

noncomputable def volume (S : Finset V) : ℕ :=
  ∑ v ∈ S, G.degree v

noncomputable def setConductance (S : Finset V) : ℚ :=
  (G.edgeCut S : ℚ) / (min (G.volume S : ℚ) (G.volume Sᶜ : ℚ))

noncomputable def conductance : ℚ :=
  let candidates := (Finset.univ : Finset (Finset V)).filter
    (fun S => S.Nonempty ∧ S ≠ Finset.univ)
  if h : candidates.Nonempty then
    candidates.inf' h (G.setConductance)
  else
    0

end SimpleGraph

namespace Cheeger

variable {n : ℕ}

noncomputable def sqNorm (f : Fin n → ℝ) : ℝ := ∑ i, f i ^ 2

noncomputable def quadForm (edges : Finset (Fin n × Fin n)) (f : Fin n → ℝ) : ℝ :=
  ∑ e ∈ edges, (f e.1 - f e.2) ^ 2

noncomputable def splitQuadForm (crossing : Finset (Fin n × Fin n))
    (f : Fin n → ℝ) (m : Fin n) : ℝ :=
  ∑ e ∈ crossing, ((f e.1 - f m) ^ 2 + (f m - f e.2) ^ 2)

noncomputable def indicatorVec (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then (Sᶜ.card : ℝ) else -(S.card : ℝ)

noncomputable def prefixCutRatio (edges : Finset (Fin n × Fin n)) (i : ℕ) : ℝ :=
  let crossingEdges := edges.filter (fun e =>
    ((e.1 : ℕ) < i ∧ ¬((e.2 : ℕ) < i)) ∨ (¬((e.1 : ℕ) < i) ∧ (e.2 : ℕ) < i))
  (crossingEdges.card : ℝ) / (min (i : ℝ) ((n : ℝ) - (i : ℝ)))

noncomputable def dirEdges (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e : Fin n × Fin n => G.Adj e.1 e.2)
