/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VerifyGoal89.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
import Lemma.Int.WeightLE.of.BruhatLE


example {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) :

    ((∀ w ∈ WeylStabilizerModQ rd wg x,
      ∃ (n : ℕ) (αs : Fin n → Δ.𝔥 →ₗ[R] R),
        (∀ i, αs i ∈ rootsOfStabilizer rd wg rs x) ∧
        w = (List.ofFn (fun i => rs.reflection (αs i))).prod) ∧
    (∀ α, α ∈ rootsOfStabilizer rd wg rs x →
       rs.reflection α ∈ WeylStabilizerModQ rd wg x)) ∧

    IsRootSubsystem rd wg rs (rootsOfStabilizer rd wg rs x) ∧

    (∀ h : Δ.𝔥,
      h ∈ corootsOf rs (rootsOfStabilizer rd wg rs x) ↔
        (h ∈ Submodule.span ℤ (corootsOf rs (rootsOfStabilizer rd wg rs x)) ∧
         h ∈ corootsOf rs (↑rs.allRoots : Set (Δ.𝔥 →ₗ[R] R)))) :=
  proposition_15_12 rd wg rs x


#check @RootSystemWithReflections.stabilizer_gen_by_reflections

