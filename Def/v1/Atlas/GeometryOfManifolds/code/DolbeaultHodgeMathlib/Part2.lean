/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DolbeaultHodgeMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Structure.v1.Atlas.GeometryOfManifolds.code.DolbeaultHodgeMathlib
set_option autoImplicit false

open ContinuousAlternatingMap


namespace DolbeaultHodgeMathlib

/-- Mathlib `Inner` instance built from the axiomatic $L^2$ inner product. -/
@[reducible]
def L2InnerProduct.toInner {n : ℕ} (ip : L2InnerProduct n) (k : ℕ) :
    Inner ℝ (DiffForm n k) where
  inner := ip.inner

/-- Build a `PreInnerProductSpace.Core` from an `L2InnerProduct`, giving access to Mathlib's
inner-product-space machinery. -/
@[reducible]
noncomputable def L2InnerProduct.toPreCore {n : ℕ} (ip : L2InnerProduct n) (k : ℕ) :
    PreInnerProductSpace.Core ℝ (DiffForm n k) where
  inner := ip.inner
  conj_inner_symm x y := by
    change ip.inner y x = ip.inner x y
    exact ip.inner_symm y x
  re_inner_nonneg x := by
    change 0 ≤ ip.inner x x
    exact ip.inner_self_nonneg x
  add_left x y z := ip.inner_add_left x y z
  smul_left x y r := by
    change ip.inner (r • x) y = r * ip.inner x y
    exact ip.inner_smul_left r x y

/-- The seminormed group structure on $\Omega^k$ induced by the $L^2$ inner product. -/
@[reducible]
noncomputable def L2InnerProduct.toSeminormedAddCommGroup {n : ℕ}
    (ip : L2InnerProduct n) (k : ℕ) : SeminormedAddCommGroup (DiffForm n k) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℝ (DiffForm n k) _ _ _ (ip.toPreCore k)

/-- The Mathlib `InnerProductSpace` structure on $\Omega^k$ induced by the $L^2$ inner product. -/
@[reducible]
noncomputable def L2InnerProduct.toInnerProductSpace {n : ℕ}
    (ip : L2InnerProduct n) (k : ℕ) :
    @InnerProductSpace ℝ (DiffForm n k) _
      (ip.toSeminormedAddCommGroup k) :=
  @InnerProductSpace.ofCore ℝ (DiffForm n k) _ _ _ (ip.toPreCore k)

end DolbeaultHodgeMathlib
