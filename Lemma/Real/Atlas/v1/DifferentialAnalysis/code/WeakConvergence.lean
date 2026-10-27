import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.WeakConvergence
open TemperedDistribution MvPolynomial Filter Topology DifferentialOperators
open scoped SchwartzMap


namespace DifferentialOperators

/--
[prop_11_2_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeakConvergence.lean)
-/
@[path]
lemma prop_11_2_smul
  {n : ℕ}
  {p : Filter ι}
  {u : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {u₀ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {c : ℂ}
-- given
  (hu : Tendsto u p (𝓝 u₀)) :
-- imply
  Tendsto (fun j => c • u j) p (𝓝 (c • u₀)) :=
-- proof
  ((continuous_const_smul c).tendsto _).comp hu

end DifferentialOperators

namespace DifferentialOperators

/--
[prop_11_2_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeakConvergence.lean)
-/
@[path]
lemma prop_11_2_add
  {n : ℕ}
  {p : Filter ι}
  {u u' : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {u₀ u₀' : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hu : Tendsto u p (𝓝 u₀))
  (hu' : Tendsto u' p (𝓝 u₀')) :
-- imply
  Tendsto (fun j => u j + u' j) p (𝓝 (u₀ + u₀')) :=
-- proof
  hu.add hu'

end DifferentialOperators

namespace DifferentialOperators

/--
[prop_11_2_diffOp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeakConvergence.lean)
-/
@[path]
lemma prop_11_2_diffOp
  {n : ℕ}
  {p : Filter ι}
  {u : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {u₀ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {P : MvPolynomial (Fin n) ℂ}
-- given
  (hu : Tendsto u p (𝓝 u₀)) :
-- imply
  Tendsto (fun j => constCoeffDiffOp n P (u j)) p (𝓝 (constCoeffDiffOp n P u₀)) :=
-- proof
  ((constCoeffDiffOp n P).continuous.tendsto _).comp hu

end DifferentialOperators

namespace DifferentialOperators

/--
[prop_11_2_smulLeft](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeakConvergence.lean)
-/
@[path]
lemma prop_11_2_smulLeft
  {n : ℕ}
  {p : Filter ι}
  {u : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {u₀ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hu : Tendsto u p (𝓝 u₀)) :
-- imply
  Tendsto (fun j => TemperedDistribution.smulLeftCLM ℂ g (u j)) p (𝓝 (TemperedDistribution.smulLeftCLM ℂ g u₀)) :=
-- proof
  ((TemperedDistribution.smulLeftCLM ℂ g).continuous.tendsto _).comp hu

end DifferentialOperators

namespace DifferentialOperators

/--
[proposition_11_2_combined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeakConvergence.lean)
-/
@[path]
lemma proposition_11_2_combined
  {n : ℕ}
  {p : Filter ι}
  {u u' : ι → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {u₀ u₀' : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {c : ℂ}
  {P : MvPolynomial (Fin n) ℂ}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hu : Tendsto u p (𝓝 u₀))
  (hu' : Tendsto u' p (𝓝 u₀')) :
-- imply
  Tendsto (fun j => c • u j) p (𝓝 (c • u₀)) ∧ Tendsto (fun j => u j + u' j) p (𝓝 (u₀ + u₀')) ∧ Tendsto (fun j => constCoeffDiffOp n P (u j)) p (𝓝 (constCoeffDiffOp n P u₀)) ∧ Tendsto (fun j => TemperedDistribution.smulLeftCLM ℂ g (u j)) p (𝓝 (TemperedDistribution.smulLeftCLM ℂ g u₀)) :=
-- proof
  ⟨prop_11_2_smul hu c, prop_11_2_add hu hu', prop_11_2_diffOp hu P, prop_11_2_smulLeft hu g⟩
end DifferentialOperators



-- created on 2026-10-23
