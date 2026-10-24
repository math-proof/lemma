import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FreeIVErgodicClose
open MeasureTheory Filter Topology Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[fie_freeIV_isErgodic_of_eq_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeIVErgodicClose.lean)
-/
@[path]
private lemma fie_freeIV_isErgodic_of_eq_wired_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (heq : (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fie_freeIV_isErgodic_of_eq_wired hd hp hp1 heq

/--
[fie_agree_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeIVErgodicClose.lean)
-/
@[path]
private lemma fie_agree_of_eq_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (heq : (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  fie_FreeWiredAgree (d := d) hp hp1 := by
-- proof
  apply StatMech.FK.fie_agree_of_eq hp hp1 heq

/--
[fie_freeWiredAgree_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeIVErgodicClose.lean)
-/
@[path]
private lemma fie_freeWiredAgree_satisfiable_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (heq : (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  fie_FreeWiredAgree (d := d) hp hp1 := by
-- proof
  apply StatMech.FK.fie_freeWiredAgree_satisfiable hp hp1 heq

/--
[fie_freeUpperDecay_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeIVErgodicClose.lean)
-/
@[path]
private lemma fie_freeUpperDecay_of_agree_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hagree : fie_FreeWiredAgree (d := d) hp hp1) :
-- imply
  fmu_UpperDecay (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fie_freeUpperDecay_of_agree hd hp hp1 hagree

/--
[fie_freeIV_isErgodic_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeIVErgodicClose.lean)
-/
@[path]
private lemma fie_freeIV_isErgodic_of_agree_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hagree : fie_FreeWiredAgree (d := d) hp hp1) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fie_freeIV_isErgodic_of_agree hd hp hp1 hagree

/--
[fie_freeIV_isErgodic_of_eq_wired'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeIVErgodicClose.lean)
-/
@[path]
private lemma fie_freeIV_isErgodic_of_eq_wired'_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (heq : (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fie_freeIV_isErgodic_of_eq_wired' hd hp hp1 heq


-- created on 2026-10-23
