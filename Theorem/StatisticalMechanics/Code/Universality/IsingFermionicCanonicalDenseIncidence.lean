/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

theorem fkIsingRationalComplex_denseRange :
    DenseRange fkIsingRationalComplex := by
  let realPair : Rat × Rat → Real × Real :=
    Prod.map ((↑) : Rat → Real) ((↑) : Rat → Real)
  let toComplex : Real × Real → Complex := fun p ↦
    p.1 + p.2 * Complex.I
  have hpair : DenseRange realPair :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hsurj : Function.Surjective toComplex := by
    intro z
    refine ⟨(z.re, z.im), ?_⟩
    apply Complex.ext <;> simp [toComplex]
  have hcontinuous : Continuous toComplex := by
    unfold toComplex
    fun_prop
  have hcomp := hsurj.denseRange.comp hpair hcontinuous
  simpa only [Function.comp_def, realPair, toComplex,
    fkIsingRationalComplex, Prod.map_apply] using hcomp


end
end StatMech.Universality
