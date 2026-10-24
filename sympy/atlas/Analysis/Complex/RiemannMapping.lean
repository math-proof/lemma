/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/RiemannMapping.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.RootsOfUnity.Complex
import sympy.atlas.Analysis.Complex.Hurwitz
import Lemma.Complex.Hurwitz
import Lemma.Set.IsLocallyUniformlyBoundedOn.of.All_All_LeNorm.Ge_0.IsOpen
import sympy.atlas.Analysis.Complex.NormalFamilies
namespace MathlibExt.Analysis.Complex.RiemannMappingWanted

open Filter Metric Set
open scoped Topology

/-- The disc automorphism `w ↦ (w - a) / (1 - ā w)`. -/
private noncomputable def rmap_mob (a w : ℂ) : ℂ := (w - a) / (1 - starRingEnd ℂ a * w)

/-- The extremal family: holomorphic injective maps `U → ball 0 1` sending `z₀` to `0`. -/
private def rmap_Fam (U : Set ℂ) (z₀ : ℂ) : Set (ℂ → ℂ) :=
  {f | DifferentiableOn ℂ f U ∧ Set.InjOn f U ∧ Set.MapsTo f U (ball 0 1) ∧ f z₀ = 0}
end MathlibExt.Analysis.Complex.RiemannMappingWanted
