/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.HilbertSpace
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
import Class.v1.Atlas.DifferentialAnalysis.code.HilbertSpace
import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part7
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Theorem.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert


noncomputable section

open MeasureTheory

namespace SobolevHilbert

/-- The zero element of `SobolevSpace n m`. -/
instance sobolevSpaceZero (n m : ℕ) : Zero (SobolevEmbedding.SobolevSpace n m) :=
  ⟨⟨0, contDiff_const, fun j _ => by
    have : (fun x => iteratedFDeriv ℝ j (0 : EuclideanSpace ℝ (Fin n) → ℂ) x) = 0 := by
      ext x; simp
    rw [this]; exact MemLp.zero⟩⟩

/-- Negation on `SobolevSpace n m`, obtained by negating the underlying function. -/
instance sobolevSpaceNeg (n m : ℕ) : Neg (SobolevEmbedding.SobolevSpace n m) :=
  ⟨fun u => ⟨-u.toFun, u.contDiff_toFun.neg, fun j hj => by
    simp only [iteratedFDeriv_neg]; exact (u.iteratedFDeriv_memLp j hj).neg⟩⟩

/-- Addition on `SobolevSpace n m`, obtained pointwise on the underlying functions. -/
instance sobolevSpaceAdd (n m : ℕ) : Add (SobolevEmbedding.SobolevSpace n m) :=
  ⟨fun u v => ⟨u.toFun + v.toFun, u.contDiff_toFun.add v.contDiff_toFun,
    fun j hj => sobolevSpace_add_memLp u v j hj⟩⟩

end SobolevHilbert
end
