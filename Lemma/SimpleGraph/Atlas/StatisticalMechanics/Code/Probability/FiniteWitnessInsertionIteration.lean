import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.FiniteWitnessInsertionIteration
open StatMech StatMech.Probability


/--
[finiteEventMass_le_pow_erase_of_insert_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FiniteWitnessInsertionIteration.lean)
-/
@[path]
private lemma finiteEventMass_le_pow_erase_of_insert_step_eq
  [Fintype Omega]
  [Fintype I]
  {mu : Omega → Real}
  {a : Real}
  {S : Finset I}
  {first : I}
-- given
  (hmu : ∀ omega, 0 ≤ mu omega)
  (hsum : ∑ omega, mu omega = 1)
  (Witness : Finset I → Omega → Prop)
  (ha : 0 ≤ a)
  (step : ∀ (T : Finset I) (first : I), first ∈ T → ∀ (x : I), x ∉ T → finiteEventMass mu {omega | Witness (insert x T) omega} ≤ a * finiteEventMass mu {omega | Witness T omega})
  (hfirst : first ∈ S) :
-- imply
  finiteEventMass mu {omega | Witness S omega} ≤ a ^ (S.erase first).card := by
-- proof
  apply StatMech.Probability.finiteEventMass_le_pow_erase_of_insert_step mu hmu hsum Witness ha step S first hfirst


-- created on 2026-10-23
