import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusExtremeFinal
open StatMech StatMech.Ising


/--
[ipx_plusState_isInvariantExtremePoint_of_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusExtremeFinal.lean)
-/
@[path]
private lemma ipx_plusState_isInvariantExtremePoint_of_homogeneous_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hhom : ∀ g : Multiplicative (Lattice.Site d), iti_PlusMultiHomogeneous β h g) :
-- imply
  StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Lattice.Site d)) (plusState d β h : Measure (ConfigSpace (Lattice.Site d))) := by
-- proof
  apply StatMech.Ising.ipx_plusState_isInvariantExtremePoint_of_homogeneous hd hβ hh hhom

/--
[ipx_plusState_isErgodic_of_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusExtremeFinal.lean)
-/
@[path]
private lemma ipx_plusState_isErgodic_of_homogeneous_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hhom : ∀ g : Multiplicative (Lattice.Site d), iti_PlusMultiHomogeneous β h g) :
-- imply
  IsErgodic (G := Multiplicative (Lattice.Site d)) (plusState d β h : Measure (ConfigSpace (Lattice.Site d))) := by
-- proof
  apply StatMech.Ising.ipx_plusState_isErgodic_of_homogeneous hd hβ hh hhom


-- created on 2026-10-23
