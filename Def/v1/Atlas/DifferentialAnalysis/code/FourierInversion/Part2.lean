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
import Theorem.v1.Atlas.DifferentialAnalysis.code.FourierInversion
open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap


noncomputable section

namespace FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Isomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {n : ℕ}

/-- The `k`-fold iterated distributional derivative in the `j`-th coordinate
direction, applied to a tempered distribution `u`. -/
def iterDistribDerivCoord (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (fun v => ∂_{EuclideanSpace.single j (1 : ℝ)} v)^[k] u

/-- The mixed iterated distributional derivative `∂^α u` indexed by a
multi-index `α : Fin n → ℕ`, defined by composing the per-coordinate iterated
derivatives over all coordinates. -/
def iterDistribDeriv (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j v => iterDistribDerivCoord j (α j) v) u

/-- The `k`-fold iterated operation of multiplication by `2πi·ξ_j` on a
tempered distribution, which is the Fourier-side counterpart of the iterated
derivative in the `j`-th coordinate. -/
def iterCoordMulFourier (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (fun v => (2 * ↑Real.pi * Complex.I) •
    smulLeftCLM ℂ (fun ξ => ↑(@inner ℝ _ _ ξ (EuclideanSpace.single j 1))) v)^[k] u

/-- The multi-index iterated multiplication operation `(2πi)^|α| ξ^α u` on a
tempered distribution, Fourier-dual to the multi-index derivative `∂^α`. -/
def iterMulFourier (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j v => iterCoordMulFourier j (α j) v) u

/-- The `k`-fold iterated operation of multiplication by `-2πi·x_j` on a
tempered distribution, used to express the iterated coordinate derivative on
the Fourier side after inversion. -/
def iterCoordNegMulDistrib (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (fun v => -(2 * ↑Real.pi * Complex.I) •
    smulLeftCLM ℂ (fun x => ↑(@inner ℝ _ _ x (EuclideanSpace.single j 1))) v)^[k] u

/-- The multi-index iterated multiplication `(-2πi)^|α| x^α u` on a tempered
distribution, packaged via a fold over coordinates. -/
def iterNegMulDistrib (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j v => iterCoordNegMulDistrib j (α j) v) u

/-- The Sobolev weight `⟨ξ⟩^s = (1 + ‖ξ‖²)^{s/2}`, written using the
Japanese bracket. This is the standard symbol whose `L²`-decay determines
the Sobolev exponent `s`. -/
def sobolevWeight (s : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (japaneseBracket n ξ) ^ s

end Isomorphism
end FourierInversion
end
