import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
open Finset Set SimpleGraph Function StatMech StatMech.Lattice


/--
[exitDart_headSameComponent_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExitDartsOrbit.lean)
-/
@[path]
private lemma exitDart_headSameComponent_def_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  exitDart_headSameComponent ω hfin ↔ ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable ⟨(exitDart (ω := ω) hfin).head, (exitDart_isBoundaryDart (ω := ω) hfin).2⟩ ⟨(leftExitDart (ω := ω) hfin).head, (leftExitDart_isBoundaryDart (ω := ω) hfin).2⟩ := by
-- proof
  apply StatMech.Lattice.exitDart_headSameComponent_def hfin

/--
[exitDart_sameOrbit_imp_headSameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExitDartsOrbit.lean)
-/
@[path]
private lemma exitDart_sameOrbit_imp_headSameComponent_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : ExitDartsSameOrbit ω hfin) :
-- imply
  exitDart_headSameComponent ω hfin := by
-- proof
  apply StatMech.Lattice.exitDart_sameOrbit_imp_headSameComponent hfin h

/--
[exitDart_sameOrbit_of_headSameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExitDartsOrbit.lean)
-/
@[path]
private lemma exitDart_sameOrbit_of_headSameComponent_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
  (hcomp : exitDart_headSameComponent ω hfin) :
-- imply
  ExitDartsSameOrbit ω hfin := by
-- proof
  apply StatMech.Lattice.exitDart_sameOrbit_of_headSameComponent hfin hInt hcomp

/--
[exitDart_sameOrbit_iff_headSameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExitDartsOrbit.lean)
-/
@[path]
private lemma exitDart_sameOrbit_iff_headSameComponent_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hInt : InterfaceConnected (cluster 2 ω (origin 2))) :
-- imply
  ExitDartsSameOrbit ω hfin ↔ exitDart_headSameComponent ω hfin := by
-- proof
  apply StatMech.Lattice.exitDart_sameOrbit_iff_headSameComponent hfin hInt

/--
[exitDart_headSameComponent_of_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExitDartsOrbit.lean)
-/
@[path]
private lemma exitDart_headSameComponent_of_far_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
  (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
  (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
-- imply
  exitDart_headSameComponent ω hfin := by
-- proof
  apply StatMech.Lattice.exitDart_headSameComponent_of_far hfin R hR hr hl

/--
[exitDart_sameOrbit_of_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExitDartsOrbit.lean)
-/
@[path]
private lemma exitDart_sameOrbit_of_far_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
  (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
  (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
-- imply
  ExitDartsSameOrbit ω hfin := by
-- proof
  apply StatMech.Lattice.exitDart_sameOrbit_of_far hfin hInt R hR hr hl


-- created on 2026-10-23
