import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.ClusterAdaptiveProjection
open SimpleGraph StatMech StatMech.FK


/--
[mem_clusterAdaptiveInsideEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma mem_clusterAdaptiveInsideEdges_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {rho : ConfigSpace (Sym2 V)}
  {e : Sym2 V} :
-- imply
  e ∈ clusterAdaptiveInsideEdges G roots rho ↔ ∃ x y : V, e = s(x, y) ∧ ¬ ClusterExploredVertex G rho roots x ∧ ¬ ClusterExploredVertex G rho roots y := by
-- proof
  apply StatMech.FK.mem_clusterAdaptiveInsideEdges_iff G roots rho e

/--
[clusterAdaptiveProjection_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterAdaptiveProjection_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {rho : ConfigSpace (Sym2 V)} :
-- imply
  clusterAdaptiveProjection G roots rho ≤ rho := by
-- proof
  apply StatMech.FK.clusterAdaptiveProjection_le G roots rho

/--
[clusterAdaptiveProjection_eq_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterAdaptiveProjection_eq_of_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {rho : ConfigSpace (Sym2 V)}
  {e : Sym2 V}
-- given
  (he : e ∉ clusterAdaptiveInsideEdges G roots rho) :
-- imply
  clusterAdaptiveProjection G roots rho e = rho e := by
-- proof
  apply StatMech.FK.clusterAdaptiveProjection_eq_of_not_mem G roots rho he

/--
[not_mem_clusterAdaptiveInsideEdges_of_explored_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma not_mem_clusterAdaptiveInsideEdges_of_explored_left_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {rho : ConfigSpace (Sym2 V)}
  {x y : V}
-- given
  (hx : ClusterExploredVertex G rho roots x) :
-- imply
  s(x, y) ∉ clusterAdaptiveInsideEdges G roots rho := by
-- proof
  apply StatMech.FK.not_mem_clusterAdaptiveInsideEdges_of_explored_left G roots rho hx

/--
[clusterAdaptiveProjection_openAdj_of_explored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterAdaptiveProjection_openAdj_of_explored_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {rho : ConfigSpace (Sym2 V)}
  {x y : V}
-- given
  (hx : ClusterExploredVertex G rho roots x)
  (hxy : (openSub G rho).Adj x y) :
-- imply
  (openSub G (clusterAdaptiveProjection G roots rho)).Adj x y := by
-- proof
  apply StatMech.FK.clusterAdaptiveProjection_openAdj_of_explored G roots rho hx hxy

/--
[clusterExploredVertex_projection_of_explored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterExploredVertex_projection_of_explored_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {rho : ConfigSpace (Sym2 V)}
  {v : V}
-- given
  (hv : ClusterExploredVertex G rho roots v) :
-- imply
  ClusterExploredVertex G (clusterAdaptiveProjection G roots rho) roots v := by
-- proof
  apply StatMech.FK.clusterExploredVertex_projection_of_explored G roots rho hv

/--
[clusterExploredVertex_of_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterExploredVertex_of_projection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {rho : ConfigSpace (Sym2 V)}
  {v : V}
-- given
  (hv : ClusterExploredVertex G (clusterAdaptiveProjection G roots rho) roots v) :
-- imply
  ClusterExploredVertex G rho roots v := by
-- proof
  apply StatMech.FK.clusterExploredVertex_of_projection G roots rho hv

/--
[clusterExploredVertex_projection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterExploredVertex_projection_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {rho : ConfigSpace (Sym2 V)}
  {v : V} :
-- imply
  ClusterExploredVertex G (clusterAdaptiveProjection G roots rho) roots v ↔ ClusterExploredVertex G rho roots v := by
-- proof
  apply StatMech.FK.clusterExploredVertex_projection_iff G roots rho v

/--
[clusterRootReachable_projection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterRootReachable_projection_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {rho : ConfigSpace (Sym2 V)}
  {r : V}
  {v : V}
-- given
  (hr : r ∈ roots) :
-- imply
  (openSub G (clusterAdaptiveProjection G roots rho)).Reachable r v ↔ (openSub G rho).Reachable r v := by
-- proof
  apply StatMech.FK.clusterRootReachable_projection_iff G roots rho hr v

/--
[clusterAdaptiveInsideEdges_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterAdaptiveInsideEdges_projection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {rho : ConfigSpace (Sym2 V)} :
-- imply
  clusterAdaptiveInsideEdges G roots (clusterAdaptiveProjection G roots rho) = clusterAdaptiveInsideEdges G roots rho := by
-- proof
  apply StatMech.FK.clusterAdaptiveInsideEdges_projection G roots rho

/--
[clusterAdaptiveProjection_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterAdaptiveProjection_idem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {rho : ConfigSpace (Sym2 V)} :
-- imply
  clusterAdaptiveProjection G roots (clusterAdaptiveProjection G roots rho) = clusterAdaptiveProjection G roots rho := by
-- proof
  apply StatMech.FK.clusterAdaptiveProjection_idem G roots rho

/--
[clusterRootReachable_agreesOff_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterRootReachable_agreesOff_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {psi rho : ConfigSpace (Sym2 V)}
  {r : V}
  {v : V}
-- given
  (hagree : AgreesOff (clusterAdaptiveInsideEdges G roots psi) psi rho)
  (hr : r ∈ roots) :
-- imply
  (openSub G psi).Reachable r v ↔ (openSub G rho).Reachable r v := by
-- proof
  apply StatMech.FK.clusterRootReachable_agreesOff_iff G roots psi rho hagree hr v

/--
[clusterExploredVertex_agreesOff_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterExploredVertex_agreesOff_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {psi rho : ConfigSpace (Sym2 V)}
  {v : V}
-- given
  (hagree : AgreesOff (clusterAdaptiveInsideEdges G roots psi) psi rho) :
-- imply
  ClusterExploredVertex G psi roots v ↔ ClusterExploredVertex G rho roots v := by
-- proof
  apply StatMech.FK.clusterExploredVertex_agreesOff_iff G roots psi rho hagree v

/--
[clusterAdaptiveInsideEdges_eq_of_agreesOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterAdaptiveInsideEdges_eq_of_agreesOff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {psi rho : ConfigSpace (Sym2 V)}
-- given
  (hagree : AgreesOff (clusterAdaptiveInsideEdges G roots psi) psi rho) :
-- imply
  clusterAdaptiveInsideEdges G roots rho = clusterAdaptiveInsideEdges G roots psi := by
-- proof
  apply StatMech.FK.clusterAdaptiveInsideEdges_eq_of_agreesOff G roots psi rho hagree

/--
[clusterAdaptiveProjection_filter_eq_condFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean)
-/
@[path]
private lemma clusterAdaptiveProjection_filter_eq_condFibre_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {roots : Finset V}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (hpsi : clusterAdaptiveProjection G roots psi = psi) :
-- imply
  Finset.univ.filter (fun rho => clusterAdaptiveProjection G roots rho = psi) = condFibre (clusterAdaptiveInsideEdges G roots psi) psi := by
-- proof
  apply StatMech.FK.clusterAdaptiveProjection_filter_eq_condFibre G roots psi hpsi


-- created on 2026-10-23
