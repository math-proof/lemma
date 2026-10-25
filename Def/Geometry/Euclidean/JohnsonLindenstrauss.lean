/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JohnsonLindenstrauss.lean -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.UniformSpace.Uniformizable
open scoped RealInnerProductSpace
open ProbabilityTheory MeasureTheory


section ProjectionRows

noncomputable def rowProjection {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (anchor : E) : (Fin d → E) → (Fin d → ℝ) :=
  fun rows i => (innerSL ℝ anchor) (rows i)

def projectionFailure {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (ε : ℝ) (anchor : E) : Set (Fin d → E) :=
  {rows | (∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2) ≤
      (d : ℝ) * (1 - ε)} ∪
    {rows | (d : ℝ) * (1 + ε) ≤
      ∑ i, ((innerSL ℝ anchor) (rows i)) ^ 2}

noncomputable def pairFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (ε : ℝ) (x y : E) : Set (Fin d → E) := by
  classical
  exact if x = y then ∅
    else projectionFailure d ε (‖x - y‖⁻¹ • (x - y))

noncomputable def anyPairFailure
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (ε : ℝ) (X : Finset E) : Set (Fin d → E) :=
  ⋃ x ∈ X, ⋃ y ∈ X, pairFailure d ε x y

noncomputable def gaussianMap
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (rows : Fin d → E) : E → EuclideanSpace ℝ (Fin d) :=
  fun x => WithLp.toLp 2 (fun i => (Real.sqrt (d : ℝ))⁻¹ *
    (innerSL ℝ x) (rows i))

end ProjectionRows
