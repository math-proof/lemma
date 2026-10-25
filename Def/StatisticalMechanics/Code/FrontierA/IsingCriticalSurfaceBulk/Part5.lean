/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk.Part5
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

noncomputable def unequalReplicaBridgeInteraction
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (a : ConfigSpace V) (b : ConfigSpace W) : Real :=
  ∑ e ∈ StatMech.FK.fis_interface G H K,
    bond (isingSumConfigEquiv.symm (a, b)) e


noncomputable def unequalReplicaExp2
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (F : ConfigSpace V -> ConfigSpace W -> Real) : Real :=
  (∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
      wJ G.edgeFinset (fun _ => J) hf a *
        wJ H.edgeFinset (fun _ => J) hg b * F a b) /
    (ZJ G.edgeFinset (fun _ => J) hf *
      ZJ H.edgeFinset (fun _ => J) hg)


noncomputable def unequalReplicaBridgeMoment
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) : Real :=
  (∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
      wJ G.edgeFinset (fun _ => J) hf a *
        wJ H.edgeFinset (fun _ => J) hg b *
        Real.exp (r * unequalReplicaBridgeInteraction G H K a b)) /
    (ZJ G.edgeFinset (fun _ => J) hf *
      ZJ H.edgeFinset (fun _ => J) hg)

noncomputable def unequalReplicaBridgeFreeEnergy
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) : Real :=
  Real.log (unequalReplicaBridgeMoment G H K J hf hg r) -
    Real.log (unequalReplicaBridgeMoment G H K J hf hg (-r))


noncomputable def unequalReplicaBridgeMean
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) : Real :=
  ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
      wJ G.edgeFinset (fun _ => J) hf a *
        wJ H.edgeFinset (fun _ => J) hg b *
        (unequalReplicaBridgeInteraction G H K a b *
          Real.exp (r * unequalReplicaBridgeInteraction G H K a b))) /
      (ZJ G.edgeFinset (fun _ => J) hf *
        ZJ H.edgeFinset (fun _ => J) hg)) /
    unequalReplicaBridgeMoment G H K J hf hg r


noncomputable def unequalReplicaBridgeVariance
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) : Real :=
  ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
      wJ G.edgeFinset (fun _ => J) hf a *
        wJ H.edgeFinset (fun _ => J) hg b *
        (unequalReplicaBridgeInteraction G H K a b ^ 2 *
          Real.exp (r * unequalReplicaBridgeInteraction G H K a b))) /
      (ZJ G.edgeFinset (fun _ => J) hf *
        ZJ H.edgeFinset (fun _ => J) hg)) /
      unequalReplicaBridgeMoment G H K J hf hg r -
    unequalReplicaBridgeMean G H K J hf hg r ^ 2

end
end StatMech.FrontierA
