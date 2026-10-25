/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzRepresentation
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzRepresentation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Analysis.Fourier.LpSpace
import Theorem.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part5
open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap


noncomputable section

namespace FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Isomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {n : ℕ}

/-- The set-level bijection `Hs n s ≃ L²(ℝⁿ; ℂ)` provided by the witness
function construction. -/
noncomputable def Hs.equivLp (s : ℝ) :
    Hs n s ≃ MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  toFun := Hs.witnessL2 n s
  invFun := Hs.fromL2 n s
  left_inv := Hs.witnessL2_fromL2 n s
  right_inv := Hs.fromL2_witnessL2 n s


/-- Transport the `NormedAddCommGroup` structure from `L²(ℝⁿ; ℂ)` to
`Hs n s` along the bijection `Hs.equivLp`. -/
@[reducible]
noncomputable def Hs.instNormedAddCommGroup (s : ℝ) : NormedAddCommGroup (Hs n s) :=
  (Hs.equivLp n s).normedAddCommGroup

attribute [instance] Hs.instNormedAddCommGroup


/-- Transport the complex inner-product-space structure from `L²(ℝⁿ; ℂ)` to
`Hs n s` along the bijection `Hs.equivLp`. The inner product on `H^s` is
`⟨u, v⟩_{H^s} := ⟨witnessL2 u, witnessL2 v⟩_{L²}`. -/
@[reducible]
noncomputable def Hs.instInnerProductSpace (s : ℝ) : InnerProductSpace ℂ (Hs n s) := by
  letI := Hs.instNormedAddCommGroup n s
  letI : NormedSpace ℂ (Hs n s) := Equiv.normedSpace ℂ (Hs.equivLp n s)
  letI : Inner ℂ (Hs n s) :=
    ⟨fun x y => (inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s y) : ℂ)⟩
  exact {
    norm_sq_eq_re_inner := fun x => by
      show ‖x‖ ^ 2 = RCLike.re (inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s x))
      have h : ‖x‖ = ‖Hs.equivLp n s x‖ := rfl
      rw [h]
      exact InnerProductSpace.norm_sq_eq_re_inner (Hs.equivLp n s x)
    conj_inner_symm := fun x y => by
      show starRingEnd ℂ (inner (𝕜 := ℂ) (Hs.equivLp n s y) (Hs.equivLp n s x)) =
           inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s y)
      exact InnerProductSpace.conj_inner_symm (Hs.equivLp n s x) (Hs.equivLp n s y)
    add_left := fun x y z => by
      show inner (𝕜 := ℂ) (Hs.equivLp n s (x + y)) (Hs.equivLp n s z) =
           inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s z) +
           inner (𝕜 := ℂ) (Hs.equivLp n s y) (Hs.equivLp n s z)
      have hadd : (Hs.equivLp n s) (x + y) = (Hs.equivLp n s) x + (Hs.equivLp n s) y := by
        simp [show (x + y : Hs n s) = (Hs.equivLp n s).symm
          ((Hs.equivLp n s) x + (Hs.equivLp n s) y) from rfl]
      rw [hadd]
      exact inner_add_left _ _ _
    smul_left := fun x y r => by
      show inner (𝕜 := ℂ) (Hs.equivLp n s (r • x)) (Hs.equivLp n s y) =
           starRingEnd ℂ r * inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s y)
      have hsmul : (Hs.equivLp n s) (r • x) = r • (Hs.equivLp n s) x := by
        simp [show (r • x : Hs n s) = (Hs.equivLp n s).symm
          (r • (Hs.equivLp n s) x) from rfl]
      rw [hsmul]
      exact inner_smul_left _ _ _
  }

end Isomorphism
end FourierInversion
end
