/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section16
import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section17.Part3


noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- The forward characteristic map $B^k \to \mathbf{RP}^n$ of the $k$-cell: normalize the
auxiliary vector and project to $\mathbf{RP}^n$. -/
def rpnCharMapFwd (n k : ℕ) (hk : k ≤ n) (x : Fin k → ℝ) : RPn n :=
  let v := rpnRawVec n k hk x
  let hv := rpnRawVec_ne_zero n k hk x
  Quotient.mk (antipodalSetoid n)
    ⟨(‖v‖⁻¹ : ℝ) • v, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)⟩

/-- The inverse to the characteristic map on the open cell: extracts the first $k$ coordinates
of the representative, with a sign and normalisation depending on the $k$th coordinate. -/
def rpnCharMapInv (n k : ℕ) (hk : k ≤ n) (q : RPn n) : Fin k → ℝ :=
  Quotient.lift (fun p : Sphere n =>
    let pv := (p : EuclideanSpace ℝ (Fin (n + 1)))
    let pk := pv ⟨k, by omega⟩
    let firstK : Fin k → ℝ := fun i => pv ⟨i.val, by omega⟩
    let M := ‖firstK‖
    let denom := |pk| + M
    fun i : Fin k => pk.sign * pv ⟨i.val, by omega⟩ / denom
  ) (by
    intro a b hab
    have hab' : (a : EuclideanSpace ℝ (Fin (n + 1))) = b ∨
        (a : EuclideanSpace ℝ (Fin (n + 1))) = -↑b := by
      exact hab
    funext i
    rcases hab' with h | h
    ·
      have : (a : EuclideanSpace ℝ (Fin (n + 1))) = (b : EuclideanSpace ℝ (Fin (n + 1))) := h
      simp [this]
    ·

      have ha : (a : EuclideanSpace ℝ (Fin (n + 1))) = -↑b := h
      have hab_eq : a = sphereNeg n b := Subtype.ext (by simp [sphereNeg_val, ha])
      subst hab_eq
      simp [sphereNeg, Real.sign_neg, abs_neg]
      congr 1
      congr 1
      exact norm_neg _
  ) q

/-- The open $k$-cell in $\mathbf{RP}^n$: points representable by a sphere element whose
coordinates above index $k$ vanish and whose coordinate at index $k$ is nonzero. -/
def rpnOpenCell (n k : ℕ) (hk : k ≤ n) : Set (RPn n) :=
  {q : RPn n | ∃ p : Sphere n, Quotient.mk (antipodalSetoid n) p = q ∧
    (∀ j : Fin (n + 1), k < (j : ℕ) → (p : EuclideanSpace ℝ (Fin (n + 1))) j = 0) ∧
    (p : EuclideanSpace ℝ (Fin (n + 1))) ⟨k, by omega⟩ ≠ 0}

end RealProjectiveSpace
end
