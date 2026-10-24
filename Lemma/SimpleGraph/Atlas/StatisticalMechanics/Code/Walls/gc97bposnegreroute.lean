import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc97bposnegreroute
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc97b_pcount_innerReroute_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc97bposnegreroute.lean)
-/
@[path]
private lemma gc97b_pcount_innerReroute_eq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A B : Finset W}
  {u v : W}
  {P : Finset ι}
-- given
  (huv : u ≠ v)
  (hPm : P ⊆ m)
  (hPsrc : sources ends P = {u, v}) :
-- imply
  #((m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B ∆ {u, v})) = #((m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B)) := by
-- proof
  apply StatMech.Walls.gc97b_pcount_innerReroute_eq ends m A B huv P hPm hPsrc

/--
[gc97b_cogxg_reroute_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc97bposnegreroute.lean)
-/
@[path]
private lemma gc97b_cogxg_reroute_eq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x g : W}
  {P : Finset ι}
-- given
  (hog : o ≠ g)
  (hPm : P ⊆ m)
  (hPsrc : sources ends P = {o, g}) :
-- imply
  #((m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P ∧ sources ends KK.1 = {o, g} ∧ sources ends KK.2 = ({x, g} : Finset W) ∆ {o, g})) = #((m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P ∧ sources ends KK.1 = {o, g} ∧ sources ends KK.2 = ({x, g} : Finset W))) := by
-- proof
  apply StatMech.Walls.gc97b_cogxg_reroute_eq ends m o x g hog P hPm hPsrc

/--
[gc97b_reroute_iff_posLeNeg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc97bposnegreroute.lean)
-/
@[path]
private lemma gc97b_reroute_iff_posLeNeg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc97b_PosNegReroute ends m o x y g ↔ gc96b_signedPos ends m o x y g ≤ gc96b_signedNeg ends m o x y g := by
-- proof
  apply StatMech.Walls.gc97b_reroute_iff_posLeNeg ends m o x y g

/--
[gc97b_reroute_iff_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc97bposnegreroute.lean)
-/
@[path]
private lemma gc97b_reroute_iff_bijection_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc97b_PosNegReroute ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc97b_reroute_iff_bijection ends m o x y g

/--
[gc97b_threeGapCount_nonpos_of_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc97bposnegreroute.lean)
-/
@[path]
private lemma gc97b_threeGapCount_nonpos_of_reroute_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (h : gc97b_PosNegReroute ends m o x y g) :
-- imply
  gc85b_threeGapCount ends m o x y g ≤ 0 := by
-- proof
  apply StatMech.Walls.gc97b_threeGapCount_nonpos_of_reroute ends m o x y g h

/--
[gc97b_reroute_closes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc97bposnegreroute.lean)
-/
@[path]
private lemma gc97b_reroute_closes_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (h : gc97b_PosNegReroute ends m o x y g) :
-- imply
  gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc97b_reroute_closes ends m o x y g h

/--
[gc97b_wred_reroute_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc97bposnegreroute.lean)
-/
@[path]
private lemma gc97b_wred_reroute_exists_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc97b_PosNegReroute gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc97b_wred_reroute_exists

/--
[gc97b_star_reroute_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc97bposnegreroute.lean)
-/
@[path]
private lemma gc97b_star_reroute_exists_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc97b_PosNegReroute gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3 ∧ gc96b_signedPos gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3 = 1 := by
-- proof
  apply StatMech.Walls.gc97b_star_reroute_exists

/--
[gc97b_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc97bposnegreroute.lean)
-/
@[path]
private lemma gc97b_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  (gc97b_PosNegReroute ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g) ∧ (gc97b_PosNegReroute ends m o x y g → gc85b_threeGapCount ends m o x y g ≤ 0) ∧ gc97b_PosNegReroute gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc97b_status ends m o x y g

/--
[gc97b_machine_findings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc97bposnegreroute.lean)
-/
@[path]
private lemma gc97b_machine_findings_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gc97b_machine_findings


-- created on 2026-10-23
