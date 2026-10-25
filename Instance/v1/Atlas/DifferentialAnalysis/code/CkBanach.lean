/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanach.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Normed.Group.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.CkBanach
open scoped ZeroAtInfty
open Filter Topology Finset


noncomputable section

set_option maxRecDepth 4000

namespace TestFunctions

variable {n : ℕ}

/-- The zero element of `ContDiffZeroAtInfty n`: the constant `0`. -/
instance : Zero (ContDiffZeroAtInfty n) where
  zero := ⟨0, contDiff_const, fun j => by
    have : ∀ x, fderiv ℝ (⇑(0 : ZeroAtInftyContinuousMap (EuclideanSpace ℝ (Fin n)) ℂ)) x
        (EuclideanSpace.single j 1) = 0 := by
      intro x
      rw [show (⇑(0 : ZeroAtInftyContinuousMap (EuclideanSpace ℝ (Fin n)) ℂ) :
          EuclideanSpace ℝ (Fin n) → ℂ) = Function.const _ 0 from funext (fun _ => rfl),
        fderiv_const]; rfl
    rw [show (fun x => fderiv ℝ
        (⇑(0 : ZeroAtInftyContinuousMap (EuclideanSpace ℝ (Fin n)) ℂ)) x
        (EuclideanSpace.single j 1)) = fun _ => 0 from funext this]
    exact tendsto_const_nhds⟩

/-- Pointwise addition on `ContDiffZeroAtInfty n`. -/
instance : Add (ContDiffZeroAtInfty n) where
  add u v := ⟨u.1 + v.1, u.contDiff_one.add v.contDiff_one, fun j => by
    apply tendsto_partialDeriv_of_fderiv_eq _ (fun j x =>
        fderiv ℝ (⇑u.1) x (EuclideanSpace.single j 1) +
        fderiv ℝ (⇑v.1) x (EuclideanSpace.single j 1))
    · intro j x
      rw [show (⇑(u.1 + v.1) : _ → ℂ) = ⇑u.1 + ⇑v.1 from funext (fun _ => rfl),
        fderiv_add (u.differentiable x) (v.differentiable x),
        ContinuousLinearMap.add_apply]
    · intro j
      rw [show (0 : ℂ) = 0 + 0 from (add_zero 0).symm]
      exact (u.partialDeriv_zero_at_infty j).add (v.partialDeriv_zero_at_infty j)⟩

/-- Pointwise negation on `ContDiffZeroAtInfty n`. -/
instance : Neg (ContDiffZeroAtInfty n) where
  neg u := ⟨-u.1, u.contDiff_one.neg, fun j => by
    apply tendsto_partialDeriv_of_fderiv_eq _ (fun j x =>
        -(fderiv ℝ (⇑u.1) x (EuclideanSpace.single j 1)))
    · intro j x
      rw [show (⇑(-u.1) : _ → ℂ) = -⇑u.1 from funext (fun _ => rfl),
        fderiv_neg, ContinuousLinearMap.neg_apply]
    · intro j
      rw [show (0 : ℂ) = -(0 : ℂ) from neg_zero.symm]
      exact (u.partialDeriv_zero_at_infty j).neg⟩

/-- Pointwise subtraction on `ContDiffZeroAtInfty n`. -/
instance : Sub (ContDiffZeroAtInfty n) where
  sub u v := ⟨u.1 - v.1, u.contDiff_one.sub v.contDiff_one, fun j => by
    apply tendsto_partialDeriv_of_fderiv_eq _ (fun j x =>
        fderiv ℝ (⇑u.1) x (EuclideanSpace.single j 1) -
        fderiv ℝ (⇑v.1) x (EuclideanSpace.single j 1))
    · intro j x
      rw [show (⇑(u.1 - v.1) : _ → ℂ) = ⇑u.1 - ⇑v.1 from funext (fun _ => rfl),
        fderiv_sub (u.differentiable x) (v.differentiable x),
        ContinuousLinearMap.sub_apply]
    · intro j
      rw [show (0 : ℂ) = 0 - 0 from (sub_self 0).symm]
      exact (u.partialDeriv_zero_at_infty j).sub (v.partialDeriv_zero_at_infty j)⟩

/-- The complex scalar action on `ContDiffZeroAtInfty n` by pointwise
multiplication. -/
instance : SMul ℂ (ContDiffZeroAtInfty n) where
  smul c u := ⟨c • u.1, u.contDiff_one.const_smul c, fun j => by
    apply tendsto_partialDeriv_of_fderiv_eq _ (fun j x =>
        c • (fderiv ℝ (⇑u.1) x (EuclideanSpace.single j 1)))
    · intro j x
      rw [show (⇑(c • u.1) : _ → ℂ) = c • ⇑u.1 from funext (fun _ => rfl),
        fderiv_const_smul (u.differentiable x) c, ContinuousLinearMap.smul_apply]
    · intro j
      rw [show (0 : ℂ) = c • (0 : ℂ) from (smul_zero _).symm]
      exact (u.partialDeriv_zero_at_infty j).const_smul c⟩

/-- The natural-number scalar action on `ContDiffZeroAtInfty n` (repeated
addition), required for the `AddCommGroup` structure. -/
instance : SMul ℕ (ContDiffZeroAtInfty n) where
  smul m u := ⟨m • u.1, u.contDiff_one.const_smul m, fun j => by
    apply tendsto_partialDeriv_of_fderiv_eq _ (fun j x =>
        m • (fderiv ℝ (⇑u.1) x (EuclideanSpace.single j 1)))
    · intro j x
      have hcoe : (⇑(m • u.1) : _ → ℂ) = m • ⇑u.1 := by funext x; simp
      rw [hcoe, fderiv_const_smul (u.differentiable x) m, ContinuousLinearMap.smul_apply]
    · intro j
      rw [show (0 : ℂ) = m • (0 : ℂ) from (smul_zero _).symm]
      exact (u.partialDeriv_zero_at_infty j).const_smul m⟩

/-- The integer scalar action on `ContDiffZeroAtInfty n`, required for the
`AddCommGroup` structure. -/
instance : SMul ℤ (ContDiffZeroAtInfty n) where
  smul m u := ⟨m • u.1, u.contDiff_one.const_smul m, fun j => by
    apply tendsto_partialDeriv_of_fderiv_eq _ (fun j x =>
        m • (fderiv ℝ (⇑u.1) x (EuclideanSpace.single j 1)))
    · intro j x
      have hcoe : (⇑(m • u.1) : _ → ℂ) = m • ⇑u.1 := by funext x; simp
      rw [hcoe, fderiv_const_smul (u.differentiable x) m, ContinuousLinearMap.smul_apply]
    · intro j
      rw [show (0 : ℂ) = m • (0 : ℂ) from (smul_zero _).symm]
      exact (u.partialDeriv_zero_at_infty j).const_smul m⟩

/-- `ContDiffZeroAtInfty n` is an additive commutative group, inherited from
the underlying continuous functions via the injective forgetful map. -/
instance ContDiffZeroAtInfty.instAddCommGroup : AddCommGroup (ContDiffZeroAtInfty n) :=
  ContDiffZeroAtInfty.toC0_injective.addCommGroup _
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- `ContDiffZeroAtInfty n` is a complex vector space, inherited from the
underlying continuous functions via the injective forgetful map. -/
instance ContDiffZeroAtInfty.instModule : Module ℂ (ContDiffZeroAtInfty n) :=
  Function.Injective.module ℂ
    { toFun := ContDiffZeroAtInfty.toZeroAtInftyContinuousMap
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    ContDiffZeroAtInfty.toC0_injective
    (fun _ _ => rfl)

/-- The `C¹` norm on `ContDiffZeroAtInfty n`, defined as the `ckNorm` (sum of
the sup-norm of the function and the sup-norms of its partial derivatives) at
order one. -/
instance ContDiffZeroAtInfty.instNorm : Norm (ContDiffZeroAtInfty n) where
  norm u := ckNorm n 1 ⇑u.toZeroAtInftyContinuousMap

end TestFunctions
end
