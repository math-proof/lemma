import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianTreeDiagramAlgebra
open Finset StatMech StatMech.FrontierA


/--
[finiteIntegratedTreeDiagram_eq_susceptibility_pow_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTreeDiagramAlgebra.lean)
-/
@[path]
private lemma finiteIntegratedTreeDiagram_eq_susceptibility_pow_four_eq
  [Fintype X]
  [AddCommGroup X]
-- given
  (G : X -> Real) :
-- imply
  finiteIntegratedTreeDiagram G = finiteSusceptibility G ^ 4 := by
-- proof
  apply StatMech.FrontierA.finiteIntegratedTreeDiagram_eq_susceptibility_pow_four G

/--
[finiteIntegratedFourthCumulant_treeDiagram_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTreeDiagramAlgebra.lean)
-/
@[path]
private lemma finiteIntegratedFourthCumulant_treeDiagram_bound_eq
  [Fintype X]
  [AddCommGroup X]
-- given
  (G : X -> Real)
  (U : X -> X -> X -> Real)
  (htree : ∀ x₂ x₃ x₄, 0 <= -U x₂ x₃ x₄ ∧ -U x₂ x₃ x₄ <= 2 * ∑ y : X, G y * G (y - x₂) * G (y - x₃) * G (y - x₄)) :
-- imply
  0 <= -finiteIntegratedFourthCumulant U ∧ -finiteIntegratedFourthCumulant U <= 2 * finiteSusceptibility G ^ 4 := by
-- proof
  apply StatMech.FrontierA.finiteIntegratedFourthCumulant_treeDiagram_bound G U htree


-- created on 2026-10-23
