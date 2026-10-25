/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/DeFinetti.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith


section

open MeasureTheory Set

namespace MathlibExt.Probability.DeFinettiWanted

/-!
# Binary de Finetti representation theorem

The binary de Finetti representation of exchangeable
`ℕ → Bool` laws as mixtures of i.i.d. Bernoulli laws.
-/

/-- Cylinder set: `ω (p s) = β s` for all `s`. -/
def dfbCyl {ι : Type*} [Fintype ι] (p : ι → ℕ) (β : ι → Bool) : Set (ℕ → Bool) :=
  {ω : ℕ → Bool | ∀ s, ω (p s) = β s}

/-- Pattern: true on left, false on right. -/
def dfbPattern (a b : ℕ) : Fin a ⊕ Fin b → Bool :=
  Sum.elim (fun _ => true) (fun _ => false)

/-- Count of ones among first `N` coordinates, as a real. -/
noncomputable def dfbCount (N : ℕ) (ω : ℕ → Bool) : ℝ :=
  ∑ i : Fin N, (if ω (i : ℕ) = true then (1 : ℝ) else 0)

/-- Empirical frequency, projected into `[0,1]`. -/
noncomputable def dfbFreq (N : ℕ) (ω : ℕ → Bool) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 (by simp) (dfbCount N ω / (N : ℝ))

/-- Moment monomial as bounded continuous function on `[0,1]`. -/
noncomputable def dfbMoment (a b : ℕ) : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨(fun p : Set.Icc (0 : ℝ) 1 => (p.val : ℝ) ^ a * (1 - (p.val : ℝ)) ^ b),
     by fun_prop⟩

noncomputable def dfbQ (A B : Finset ℕ) : Fin A.card ⊕ Fin B.card → ℕ :=
  Sum.elim ⇑(Finset.orderEmbOfFin A rfl) ⇑(Finset.orderEmbOfFin B rfl)

end MathlibExt.Probability.DeFinettiWanted
end
