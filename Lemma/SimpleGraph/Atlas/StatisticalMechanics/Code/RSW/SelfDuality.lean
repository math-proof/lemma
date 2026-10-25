import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
open SimpleGraph Real StatMech StatMech.RSW


/--
[selfDualPoint_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma selfDualPoint_mem_Ioo_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  selfDualPoint q ∈ Set.Ioo (0 : ℝ) 1 := by
-- proof
  apply StatMech.RSW.selfDualPoint_mem_Ioo hq

/--
[selfDualPoint_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma selfDualPoint_pos_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  0 < selfDualPoint q := by
-- proof
  apply StatMech.RSW.selfDualPoint_pos hq

/--
[selfDualPoint_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma selfDualPoint_lt_one_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  selfDualPoint q < 1 := by
-- proof
  apply StatMech.RSW.selfDualPoint_lt_one hq

/--
[dualParam_selfDualPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma dualParam_selfDualPoint_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  dualParam (selfDualPoint q) q (selfDualPoint q) := by
-- proof
  apply StatMech.RSW.dualParam_selfDualPoint hq

/--
[dualParam_self_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma dualParam_self_iff_eq
  {q : ℝ}
  {p : ℝ}
-- given
  (hq : 0 < q)
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  dualParam p q p ↔ p = selfDualPoint q := by
-- proof
  apply StatMech.RSW.dualParam_self_iff hq hp0 hp1

/--
[dualBC_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma dualBC_free_eq :
-- imply
  dualBC .free = .wired := by
-- proof
  apply StatMech.RSW.dualBC_free

/--
[dualBC_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma dualBC_wired_eq :
-- imply
  dualBC .wired = .free := by
-- proof
  apply StatMech.RSW.dualBC_wired

/--
[dualBC_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma dualBC_periodic_eq :
-- imply
  dualBC .periodic = .periodic := by
-- proof
  apply StatMech.RSW.dualBC_periodic

/--
[dualBC_dualBC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma dualBC_dualBC_eq
  {bc : BoundaryCondition} :
-- imply
  dualBC (dualBC bc) = bc := by
-- proof
  apply StatMech.RSW.dualBC_dualBC bc

/--
[isOpen_iff_not_dualCross_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma isOpen_iff_not_dualCross_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  ω e = true ↔ ¬ dualConfig ω (crossEdge e) = true := by
-- proof
  apply StatMech.RSW.isOpen_iff_not_dualCross_open ω e

/--
[dualCross_open_iff_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma dualCross_open_iff_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  dualConfig ω (crossEdge e) = true ↔ ω e = false := by
-- proof
  apply StatMech.RSW.dualCross_open_iff_closed ω e

/--
[crossingPair_incompatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma crossingPair_incompatible_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  ¬ (ω e = true ∧ dualConfig ω (crossEdge e) = true) := by
-- proof
  apply StatMech.RSW.crossingPair_incompatible ω e

/--
[ConfigSpace.edge_of_mem_openWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma edge_of_mem_openWalk_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {w : (openSubgraph 2 ω).Walk x y}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ w.edges) :
-- imply
  ω e = true := by
-- proof
  apply StatMech.RSW.ConfigSpace.edge_of_mem_openWalk w he

/--
[openWalk_blocks_dualWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma openWalk_blocks_dualWalk_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {w : (openSubgraph 2 ω).Walk x y}
  {x' y' : Site 2}
  {w' : (openSubgraph 2 (dualConfig ω)).Walk x' y'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ w.edges)
  (he' : crossEdge e ∈ w'.edges) :
-- imply
  False := by
-- proof
  apply StatMech.RSW.openWalk_blocks_dualWalk ω w w' e he he'

/--
[dualConfig_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDuality.lean)
-/
@[path]
private lemma dualConfig_involutive_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  dualConfig (dualConfig ω) e = ω (crossEdge.symm (crossEdge.symm e)) := by
-- proof
  apply StatMech.RSW.dualConfig_involutive ω e


-- created on 2026-10-23
