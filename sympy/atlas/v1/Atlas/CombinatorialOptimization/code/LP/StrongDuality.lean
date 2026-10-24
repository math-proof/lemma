/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/LP/StrongDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.LP.Farkas
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.LP.WeakDualityStandard

open Matrix Finset

noncomputable def sdAugMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ := fun i j =>
  Fin.lastCases
    (Fin.lastCases (1 : ℝ) (fun j' => -(c j')))
    (fun i' => Fin.lastCases (0 : ℝ) (fun j' => A i' j'))
    i j

noncomputable def sdAugRhs {m : ℕ} (b : Fin m → ℝ) (v : ℝ) : Fin (m + 1) → ℝ := fun i =>
  Fin.lastCases (-v) (fun i' => b i') i

noncomputable def dualAugMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Matrix (Fin (n + 1)) (Fin (m + (m + (n + 1)))) ℝ := fun row col =>
  Fin.addCases
    (fun i => Fin.lastCases (-(b i)) (fun j => A i j) row)
    (fun col' => Fin.addCases
      (fun i => Fin.lastCases (b i) (fun j => -(A i j)) row)
      (fun col'' => Fin.lastCases
          (Fin.lastCases (-1 : ℝ) (fun _ => (0 : ℝ)) row)
          (fun j' => Fin.lastCases (0 : ℝ) (fun j => if j = j' then -1 else 0) row)
          col'')
      col')
    col

noncomputable def dualAugRhs {n : ℕ} (c : Fin n → ℝ) (v : ℝ) : Fin (n + 1) → ℝ := fun row =>
  Fin.lastCases (-v) (fun j => c j) row
