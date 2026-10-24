import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.FiniteTargetMassTransport
open MeasureTheory Set StatMech StatMech.FrontierA


/--
[finiteTarget_massTransport_origin_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteTargetMassTransport.lean)
-/
@[path]
private lemma finiteTarget_massTransport_origin_null_eq
  {d : ℕ}
  [MulAction (Multiplicative (Site d)) E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {C : ConfigSpace E → Set (Site d)}
  {N : ConfigSpace E → Finset (Site d)}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
  (hmeas : ∀ x y, Measurable (fun omega => finiteTargetTransport (C omega) (N omega) x y))
  (hdiag : IsDiagonallyInvariantTransport (fun x y omega => finiteTargetTransport (C omega) (N omega) x y)) :
-- imply
  mu {omega | (C omega).Infinite ∧ (N omega).Nonempty ∧ (0 : Site d) ∈ N omega} = 0 := by
-- proof
  apply StatMech.FrontierA.finiteTarget_massTransport_origin_null mu hinv C N hmeas hdiag


-- created on 2026-10-23
