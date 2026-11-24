module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairReconnectionWitness
public import Mathlib.Data.Fintype.EquivFin
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part3
open Finset Matrix Polynomial


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexMarkedDecoratedPairEqualTotalC
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (source : SixVertexMarkedDecoratedPair T lower upper k)
    (target : SixVertexMarkedDecoratedPair T middle middle k) : Prop :=
  sixVertexMarkedDecoratedPairTotalC source =
    sixVertexMarkedDecoratedPairTotalC target


def SixVertexMarkedDecoratedPairTotalCFiberDominates
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1))
    (k : Nat) : Prop :=
  forall total : Nat,
    Fintype.card
        {source : SixVertexMarkedDecoratedPair T lower upper k //
          sixVertexMarkedDecoratedPairTotalC source = total} <=
      Fintype.card
        {target : SixVertexMarkedDecoratedPair T middle middle k //
          sixVertexMarkedDecoratedPairTotalC target = total}


def SixVertexConfigurationPairTotalCFiberDominates
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  forall total : Nat,
    Fintype.card
        {source : SixVertexMarkedPairSource T lower upper //
          sixVertexConfigurationPairTotalC source = total} <=
      Fintype.card
        {target : SixVertexMarkedPairTarget T middle //
          sixVertexConfigurationPairTotalC target = total}


def SixVertexConfigurationPairTotalCReconnection
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  exists matching : SixVertexMarkedPairSource T lower upper ->
      SixVertexMarkedPairTarget T middle,
    Function.Injective matching /\
      forall source,
        sixVertexConfigurationPairTotalC source =
          sixVertexConfigurationPairTotalC (matching source)

end
end StatMech.FrontierD
