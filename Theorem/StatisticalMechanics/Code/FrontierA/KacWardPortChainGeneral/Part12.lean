/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part12
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwOrderedPortForestCode_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    Function.Injective (kwOrderedPortForestCode G order) := by
  intro p q hpq
  let block := Fintype.card (KWDartPort G) + 1
  have hpbound : kwOrderedPortRank order p < block := by
    have hp := (order p.1 p.2).isLt
    have hc := kwOutgoingDart_card_le_port_card G p.1
    dsimp only [block]
    exact (lt_of_lt_of_le hp hc).trans (Nat.lt_succ_self _)
  have hqbound : kwOrderedPortRank order q < block := by
    have hp := (order q.1 q.2).isLt
    have hc := kwOutgoingDart_card_le_port_card G q.1
    dsimp only [block]
    exact (lt_of_lt_of_le hp hc).trans (Nat.lt_succ_self _)
  have hval := congrArg Fin.val hpq
  change (Fintype.equivFin V p.1).val * block +
      kwOrderedPortRank order p =
    (Fintype.equivFin V q.1).val * block +
      kwOrderedPortRank order q at hval
  have hvertex : (Fintype.equivFin V p.1).val =
      (Fintype.equivFin V q.1).val := by
    have hdiv := congrArg (fun z : ℕ ↦ z / block) hval
    have hpdiv : ((Fintype.equivFin V p.1).val * block +
        kwOrderedPortRank order p) / block =
        (Fintype.equivFin V p.1).val := by
      rw [Nat.mul_comm (Fintype.equivFin V p.1).val block,
        Nat.mul_add_div (m := block) (by omega),
        Nat.div_eq_of_lt hpbound, add_zero]
    have hqdiv : ((Fintype.equivFin V q.1).val * block +
        kwOrderedPortRank order q) / block =
        (Fintype.equivFin V q.1).val := by
      rw [Nat.mul_comm (Fintype.equivFin V q.1).val block,
        Nat.mul_add_div (m := block) (by omega),
        Nat.div_eq_of_lt hqbound, add_zero]
    exact hpdiv.symm.trans (hdiv.trans hqdiv)
  have hpfirst : p.1 = q.1 := by
    apply (Fintype.equivFin V).injective
    exact Fin.ext hvertex
  have hrank : kwOrderedPortRank order p = kwOrderedPortRank order q := by
    have hmod := congrArg (fun z : ℕ ↦ z % block) hval
    have hpmod : ((Fintype.equivFin V p.1).val * block +
        kwOrderedPortRank order p) % block =
        kwOrderedPortRank order p := by
      rw [Nat.add_comm,
        Nat.mul_comm (Fintype.equivFin V p.1).val block,
        Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hpbound]
    have hqmod : ((Fintype.equivFin V q.1).val * block +
        kwOrderedPortRank order q) % block =
        kwOrderedPortRank order q := by
      rw [Nat.add_comm,
        Nat.mul_comm (Fintype.equivFin V q.1).val block,
        Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hqbound]
    exact hpmod.symm.trans (hmod.trans hqmod)
  rcases p with ⟨v, i⟩
  rcases q with ⟨w, j⟩
  dsimp only at hpfirst hrank
  subst w
  have hij : order v i = order v j := Fin.ext hrank
  have : i = j := (order v).injective hij
  subst j
  rfl

end StatMech.FrontierA
