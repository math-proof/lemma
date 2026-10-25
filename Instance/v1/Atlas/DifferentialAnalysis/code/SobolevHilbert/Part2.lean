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
import Theorem.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert.Part2


noncomputable section

open MeasureTheory

namespace SobolevHilbert

/-- The additive commutative group structure on `SobolevSpace n m`. -/
instance sobolevSpace_addCommGroup' (n m : ℕ) :
    AddCommGroup (SobolevEmbedding.SobolevSpace n m) :=
  { add_assoc := fun a b c =>
      SobolevEmbedding.SobolevSpace.ext' (add_assoc a.toFun b.toFun c.toFun)
    zero_add := fun a => SobolevEmbedding.SobolevSpace.ext' (zero_add a.toFun)
    add_zero := fun a => SobolevEmbedding.SobolevSpace.ext' (add_zero a.toFun)
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := fun a =>
      SobolevEmbedding.SobolevSpace.ext' (neg_add_cancel a.toFun)
    add_comm := fun a b =>
      SobolevEmbedding.SobolevSpace.ext' (add_comm a.toFun b.toFun) }

end SobolevHilbert
end
