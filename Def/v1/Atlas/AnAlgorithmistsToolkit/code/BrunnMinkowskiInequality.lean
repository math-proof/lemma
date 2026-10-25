/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/BrunnMinkowskiInequality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AnAlgorithmistsToolkit.code.BrunnMinkowski
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.BrunnMinkowski
import Mathlib.Analysis.InnerProductSpace.PiL2


namespace BrunnMinkowskiInequality

open MeasureTheory Measure Pointwise


end BrunnMinkowskiInequality

namespace BrunnsTheorem

open MeasureTheory Set Pointwise

open scoped ENNReal NNReal

def parallelSlice {n : ℕ} (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) : Set (Fin n → ℝ) :=
  {y : Fin n → ℝ | Fin.cons t y ∈ K}

noncomputable def sliceVolume {n : ℕ} (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) : ℝ≥0∞ :=
  volume (parallelSlice K t)

noncomputable def brunnFunction (n : ℕ) (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) : ℝ :=
  (sliceVolume K t).toReal ^ ((1 : ℝ) / (n : ℝ))

end BrunnsTheorem
