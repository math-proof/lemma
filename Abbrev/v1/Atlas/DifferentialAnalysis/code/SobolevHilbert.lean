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
import Theorem.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert.Part3


noncomputable section

open MeasureTheory

namespace SobolevHilbert

/-- The normed additive commutative group structure on `SobolevSpace n m` from the Sobolev norm. -/
abbrev sobolevSpace_nacg (n m : ℕ) :
    NormedAddCommGroup (SobolevEmbedding.SobolevSpace n m) :=
  @AddGroupNorm.toNormedAddCommGroup _ (sobolevSpace_addCommGroup' n m)
    { toFun := sobolevNorm
      map_zero' := sobolevNorm_zero' n m
      add_le' := fun u v => sobolevSpace_norm_triangle u v
      neg' := fun u => sobolevNorm_neg' u
      eq_zero_of_map_eq_zero' := fun u h => sobolevNorm_eq_zero_iff u h }


end SobolevHilbert
end
