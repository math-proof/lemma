/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsWired.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.IsingFK.EsWired.Part11
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


theorem esZWired_eq_bcZ {q : ℕ} (b : Fin q) (p : ℝ) (v₀ : V) (hv₀ : bdry v₀)
    (hq : ∀ ω : ConfigSpace (Sym2 V), 1 ≤ numClustersBC G (boundaryCliqueGraph bdry) ω) :
    (q : ℝ) * esZWired G bdry q b p = bcZ G (boundaryCliqueGraph bdry) p (q : ℝ) := by
  unfold esZWired bcZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact esWeightWired_sum_spins_eq_bcWeight G bdry b p ω v₀ hv₀ (hq ω)


theorem esWiredSecondMarginal_eq_bcProb {q : ℕ} (b : Fin q) (p : ℝ) (ω : ConfigSpace (Sym2 V))
    (v₀ : V) (hv₀ : bdry v₀) (hqpos : 0 < q)
    (hq : ∀ ω : ConfigSpace (Sym2 V), 1 ≤ numClustersBC G (boundaryCliqueGraph bdry) ω) :
    esWiredSecondMarginal G bdry q b p ω = bcProb G (boundaryCliqueGraph bdry) p (q : ℝ) ω := by
  unfold esWiredSecondMarginal bcProb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  
  rw [show bcWeight G (boundaryCliqueGraph bdry) p (q : ℝ) ω
        = (q : ℝ) * (∑ σ : V → Fin q, esWeightWired G bdry b p σ ω) from
      (esWeightWired_sum_spins_eq_bcWeight G bdry b p ω v₀ hv₀ (hq ω)).symm,
    show bcZ G (boundaryCliqueGraph bdry) p (q : ℝ) = (q : ℝ) * esZWired G bdry q b p from
      (esZWired_eq_bcZ G bdry b p v₀ hv₀ hq).symm,
    mul_div_mul_left _ _ hqR.ne']

end IsingFK
end StatMech
