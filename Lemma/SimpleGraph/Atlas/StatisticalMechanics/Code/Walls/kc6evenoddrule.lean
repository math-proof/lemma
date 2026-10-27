import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc6evenoddrule
open Set SimpleGraph Function StatMech.Lattice StatMech StatMech.Walls


/--
[kc6_mem_leftRegion_iff_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6evenoddrule.lean)
-/
@[path]
private lemma kc6_mem_leftRegion_iff_odd_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2} :
-- imply
  z ∈ jec_leftRegion Vc ↔ Odd (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc6_mem_leftRegion_iff_odd Vc z

/--
[kc6_odd_rayCount_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6evenoddrule.lean)
-/
@[path]
private lemma kc6_odd_rayCount_of_mem_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∈ jec_leftRegion Vc) :
-- imply
  Odd (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc6_odd_rayCount_of_mem Vc hz

/--
[kc6_mem_of_odd_rayCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6evenoddrule.lean)
-/
@[path]
private lemma kc6_mem_of_odd_rayCount_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : Odd (jec_rayCount z Vc)) :
-- imply
  z ∈ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc6_mem_of_odd_rayCount Vc hz

/--
[kc6_notMem_leftRegion_iff_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6evenoddrule.lean)
-/
@[path]
private lemma kc6_notMem_leftRegion_iff_even_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2} :
-- imply
  z ∉ jec_leftRegion Vc ↔ Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc6_notMem_leftRegion_iff_even Vc z

/--
[kc6_mem_compl_leftRegion_iff_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6evenoddrule.lean)
-/
@[path]
private lemma kc6_mem_compl_leftRegion_iff_even_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2} :
-- imply
  z ∈ (jec_leftRegion Vc)ᶜ ↔ Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc6_mem_compl_leftRegion_iff_even Vc z

/--
[kc6_even_rayCount_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6evenoddrule.lean)
-/
@[path]
private lemma kc6_even_rayCount_of_notMem_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∉ jec_leftRegion Vc) :
-- imply
  Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc6_even_rayCount_of_notMem Vc hz

/--
[kc6_notMem_of_even_rayCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6evenoddrule.lean)
-/
@[path]
private lemma kc6_notMem_of_even_rayCount_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : Even (jec_rayCount z Vc)) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc6_notMem_of_even_rayCount Vc hz

/--
[kc6_leftRegion_eq_setOf_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6evenoddrule.lean)
-/
@[path]
private lemma kc6_leftRegion_eq_setOf_odd_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  jec_leftRegion Vc = {z : Site 2 | Odd (jec_rayCount z Vc)} := by
-- proof
  apply StatMech.Walls.kc6_leftRegion_eq_setOf_odd Vc

/--
[kc6_farLeft_notMem_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6evenoddrule.lean)
-/
@[path]
private lemma kc6_farLeft_notMem_of_even_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {t : Site 2}
-- given
  (ht : Even (jec_rayCount t Vc)) :
-- imply
  t ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc6_farLeft_notMem_of_even Vc ht

/--
[kc6_evenOddRule_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6evenoddrule.lean)
-/
@[path]
private lemma kc6_evenOddRule_node_eq :
-- imply
  ∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2), z ∈ jec_leftRegion Vc ↔ Odd (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc6_evenOddRule_node


-- created on 2026-10-23
