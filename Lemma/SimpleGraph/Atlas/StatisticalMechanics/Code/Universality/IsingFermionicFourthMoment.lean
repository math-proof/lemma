import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFourthMoment
open Finset StatMech StatMech.Universality


/--
[isingLineStoppedMean_centeredFourth_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFourthMoment.lean)
-/
@[path]
private lemma isingLineStoppedMean_centeredFourth_le_eq
  {m t : Nat}
  {p : IsingLineBox (2 * m)} :
-- imply
  isingLineStoppedMean (2 * m) t (isingLineCenteredFourth m) p <= ((p.1 : Real) - (m : Real)) ^ 4 + 6 * (t : Real) * ((p.1 : Real) - (m : Real)) ^ 2 + 3 * (t : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLineStoppedMean_centeredFourth_le m t p

/--
[isingLineStoppedKernel_center_boundary_le_fourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFourthMoment.lean)
-/
@[path]
private lemma isingLineStoppedKernel_center_boundary_le_fourth_eq
  {m t : Nat}
-- given
  (hm : 0 < m) :
-- imply
  isingLineStoppedKernel (2 * m) t ⟨m, by omega⟩ ⟨0, by omega⟩ + isingLineStoppedKernel (2 * m) t ⟨m, by omega⟩ ⟨2 * m, by omega⟩ <= 3 * (t : Real) ^ 2 / (m : Real) ^ 4 := by
-- proof
  apply StatMech.Universality.isingLineStoppedKernel_center_boundary_le_fourth m t hm


-- created on 2026-10-23
