/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part4


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


theorem det_finiteTwistedLaplacian_eq_sum_finiteCRSFWitness
    (conductance transport : V -> V -> Complex) :
    (finiteTwistedLaplacian conductance transport).det =
      ∑ X : finiteCRSFWitness V,
        finiteCRSFWitnessTerm conductance transport X := by
  rw [det_finiteTwistedLaplacian_permutation]
  have hSigma :
      (∑ X : finiteCRSFWitness V,
          finiteCRSFWitnessTerm conductance transport X) =
        ∑ sigma : Equiv.Perm V,
          ∑ target : laplacianPermutationFixedPoint sigma -> V,
            finiteCRSFWitnessTerm conductance transport
              ⟨sigma, target⟩ := by
    exact Fintype.sum_sigma _
  rw [hSigma]
  apply Finset.sum_congr rfl
  intro sigma _
  let fixed : Finset V := Finset.univ.filter fun v => sigma v = v
  have hsplit :
      (∏ v : V,
          if sigma v = v then ∑ u, conductance (sigma v) u
          else -conductance (sigma v) v * transport (sigma v) v) =
        (∏ v ∈ fixed, ∑ u, conductance (sigma v) u) *
          ∏ v ∈ (Finset.univ.filter fun v => sigma v ≠ v),
            -conductance (sigma v) v * transport (sigma v) v := by
    simpa [fixed] using
      (Finset.prod_ite
        (s := (Finset.univ : Finset V))
        (p := fun v => sigma v = v)
        (fun v => ∑ u, conductance (sigma v) u)
        (fun v => -conductance (sigma v) v * transport (sigma v) v))
  have hfixed :
      (∏ v ∈ fixed, ∑ u, conductance (sigma v) u) =
        ∑ target : laplacianPermutationFixedPoint sigma -> V,
          ∏ v : laplacianPermutationFixedPoint sigma,
            conductance v (target v) := by
    calc
      (∏ v ∈ fixed, ∑ u, conductance (sigma v) u) =
          ∏ v : laplacianPermutationFixedPoint sigma,
            ∑ u, conductance (sigma v) u := by
        apply Finset.prod_subtype fixed
        · intro v
          simp [fixed]
      _ = ∏ v : laplacianPermutationFixedPoint sigma,
            ∑ u, conductance v u := by
        apply Finset.prod_congr rfl
        intro v _
        rw [v.property]
      _ = ∑ target : laplacianPermutationFixedPoint sigma -> V,
          ∏ v : laplacianPermutationFixedPoint sigma,
            conductance v (target v) := by
        simpa using
          (Fintype.prod_sum
            (fun (v : laplacianPermutationFixedPoint sigma) (u : V) =>
              conductance v u))
  rw [hsplit, hfixed, Finset.sum_mul, smul_sum]
  apply Finset.sum_congr rfl
  intro target _
  rfl


end StatMech.FrontierA
