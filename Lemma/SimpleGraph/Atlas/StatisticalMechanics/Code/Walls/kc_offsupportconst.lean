import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc_offsupportconst
open Set SimpleGraph StatMech StatMech.Walls


/--
[kc_offsupport_rayParity_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_offsupportconst.lean)
-/
@[path]
private lemma kc_offsupport_rayParity_const_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
-- imply
  (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount y Vc)) := by
-- proof
  apply StatMech.Walls.kc_offsupport_rayParity_const Vc p hp

/--
[kc_offsupport_leftRegion_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_offsupportconst.lean)
-/
@[path]
private lemma kc_offsupport_leftRegion_const_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
-- imply
  (x ∈ jec_leftRegion Vc ↔ y ∈ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Walls.kc_offsupport_leftRegion_const Vc p hp

/--
[kc_offsupport_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_offsupportconst.lean)
-/
@[path]
private lemma kc_offsupport_mem_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ w ∈ p.support, w ∉ Vc.support)
  (hx : x ∈ jec_leftRegion Vc) :
-- imply
  y ∈ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc_offsupport_mem_leftRegion Vc p hp hx

/--
[kc_offsupport_notMem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_offsupportconst.lean)
-/
@[path]
private lemma kc_offsupport_notMem_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ w ∈ p.support, w ∉ Vc.support)
  (hx : x ∉ jec_leftRegion Vc) :
-- imply
  y ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc_offsupport_notMem_leftRegion Vc p hp hx

/--
[kc_offsupport_rayParity_const_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_offsupportconst.lean)
-/
@[path]
private lemma kc_offsupport_rayParity_const_all_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
-- imply
  ∀ w ∈ p.support, (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount w Vc)) := by
-- proof
  apply StatMech.Walls.kc_offsupport_rayParity_const_all Vc p hp

/--
[kc_offsupport_leftRegion_const_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_offsupportconst.lean)
-/
@[path]
private lemma kc_offsupport_leftRegion_const_all_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
-- imply
  ∀ w ∈ p.support, (x ∈ jec_leftRegion Vc ↔ w ∈ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Walls.kc_offsupport_leftRegion_const_all Vc p hp


-- created on 2026-10-23
