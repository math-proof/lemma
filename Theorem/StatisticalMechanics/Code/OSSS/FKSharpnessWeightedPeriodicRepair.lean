/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPeriodicRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPeriodic.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain.Part5
open scoped BigOperators Classical
open Finset Set


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPeriodicRepair

open Lattice FK RevealmentConstruction RevealmentTranslation

open WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre

open FKSharpnessWeightedPeriodic FKSharpnessWeightedDomain

section Relabel

variable {V W : Type*} [Fintype V] [DecidableEq V]

variable [Fintype W] [DecidableEq W]


theorem edgeProductW_reCfgIso
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (sigma : V ≃ W)
    (hsigma : forall x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (pfV : Sym2 V -> Real) (pfW : Sym2 W -> Real)
    (hpf : forall e, pfW (Sym2.map sigma e) = pfV e)
    (omega : ConfigSpace (Sym2 W)) :
    edgeProductW G pfV (reCfgIso sigma omega) = edgeProductW H pfW omega := by
  unfold edgeProductW reCfgIso
  symm
  apply Finset.prod_bij'
      (i := fun e _ => Sym2.map sigma.symm e)
      (j := fun e _ => Sym2.map sigma e)
  · intro e he
    exact fvs_mem_edgeFinset_map_symm G H sigma hsigma he
  · intro e he
    exact fvs_mem_edgeFinset_map G H sigma hsigma he
  · intro e he
    rw [Sym2.map_map]
    simp
  · intro e he
    rw [Sym2.map_map]
    simp
  · intro e he
    rw [Sym2.map_map]
    have hmap : Sym2.map (sigma ∘ sigma.symm) e = e := by
      rw [show (sigma ∘ sigma.symm : W -> W) = id by
        funext w
        exact sigma.apply_symm_apply w]
      exact congrFun Sym2.map_id e
    rw [hmap]
    have hpfe := hpf (Sym2.map sigma.symm e)
    rw [Sym2.map_map, hmap] at hpfe
    rw [hpfe]


theorem bcWeightW_boundaryClique_reCfgIso
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (bdryV : V -> Prop) [DecidablePred bdryV]
    (bdryW : W -> Prop) [DecidablePred bdryW]
    (sigma : V ≃ W)
    (hsigma : forall x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (hbdry : forall x, bdryV x ↔ bdryW (sigma x))
    (pfV : Sym2 V -> Real) (pfW : Sym2 W -> Real)
    (hpf : forall e, pfW (Sym2.map sigma e) = pfV e)
    (q : Real) (omega : ConfigSpace (Sym2 W)) :
    bcWeightW G (boundaryCliqueGraph bdryV) pfV q (reCfgIso sigma omega) =
      bcWeightW H (boundaryCliqueGraph bdryW) pfW q omega := by
  unfold bcWeightW
  rw [edgeProductW_reCfgIso G H sigma hsigma pfV pfW hpf omega,
    numClustersBC_boundaryClique, numClustersBC_boundaryClique,
    fvs_numClustersWired_reCfgIso G H bdryV bdryW sigma hsigma hbdry omega]


theorem bcProbW_boundaryClique_reCfgIso
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (bdryV : V -> Prop) [DecidablePred bdryV]
    (bdryW : W -> Prop) [DecidablePred bdryW]
    (sigma : V ≃ W)
    (hsigma : forall x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (hbdry : forall x, bdryV x ↔ bdryW (sigma x))
    (pfV : Sym2 V -> Real) (pfW : Sym2 W -> Real)
    (hpf : forall e, pfW (Sym2.map sigma e) = pfV e)
    (q : Real) (omega : ConfigSpace (Sym2 W)) :
    bcProbW G (boundaryCliqueGraph bdryV) pfV q (reCfgIso sigma omega) =
      bcProbW H (boundaryCliqueGraph bdryW) pfW q omega := by
  have hZ : bcZW G (boundaryCliqueGraph bdryV) pfV q =
      bcZW H (boundaryCliqueGraph bdryW) pfW q := by
    unfold bcZW
    rw [← Equiv.sum_comp (reCfgIsoEquiv sigma)
      (fun eta => bcWeightW G (boundaryCliqueGraph bdryV) pfV q eta)]
    apply Finset.sum_congr rfl
    intro eta heta
    exact bcWeightW_boundaryClique_reCfgIso G H bdryV bdryW sigma
      hsigma hbdry pfV pfW hpf q eta
  unfold bcProbW
  rw [bcWeightW_boundaryClique_reCfgIso G H bdryV bdryW sigma
    hsigma hbdry pfV pfW hpf q omega, hZ]

end Relabel
end FKSharpnessWeightedPeriodicRepair
end OSSS
end StatMech
