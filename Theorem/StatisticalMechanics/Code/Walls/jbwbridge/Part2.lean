/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jbwbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
import Def.StatisticalMechanics.Code.Walls.jbwbridge.Part2
open SimpleGraph Set


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

attribute [local instance] Classical.propDecidable


theorem jbw_vertexCut_not_even :
    ¬ Even (jce_degree (jbw_bdEdgeSet jbw_singleton) ![(1 : ℤ), 0]) := by
  classical
  have hdeg : jce_degree (jbw_bdEdgeSet jbw_singleton) ![(1 : ℤ), 0] = 1 := by
    rw [jce_degree]
    have hset : (Finset.univ.filter
        (fun i : Fin 4 => s(![(1 : ℤ), 0], jce_nbr ![(1 : ℤ), 0] i)
          ∈ jbw_bdEdgeSet jbw_singleton)) = {1} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        jbw_mem_bdEdgeSet, bdEdge_mk, jbw_singleton, Set.mem_singleton_iff, jce_nbr,
        origin_eq_zerozero]
      fin_cases i <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, site2_eq, Fin.isValue,
          Fin.ext_iff, Fin.val_one] <;> first | omega | tauto
    rw [hset]; rfl
  rw [hdeg]; decide


theorem jbw_jed_reachability (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite)
    (p q f0 g0 : Site 2) (hpq : (hypercubicLattice 2).Adj p q) (hnpq : s(p, q) ∉ H.edgeSet)
    (hfg : (hypercubicLattice 2).Adj f0 g0) (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
    H.Reachable p q :=
  jed_reachable_of_separated H hfin p q f0 g0 hpq hnpq hfg hshared hsep


theorem jbw_easyHalf {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd


end Walls
end StatMech
