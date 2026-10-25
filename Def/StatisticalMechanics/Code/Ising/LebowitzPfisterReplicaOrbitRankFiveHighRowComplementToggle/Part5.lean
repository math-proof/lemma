/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFivePairedHall.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.Part5
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def embeddingSumOfDisjointImages {A B C : Type*}
    (f : A ↪ C) (g : B ↪ C) (hdisjoint : ∀ a b, f a ≠ g b) :
    A ⊕ B ↪ C where
  toFun
    | Sum.inl a => f a
    | Sum.inr b => g b
  inj' := by
    intro x y hxy
    cases x with
    | inl a =>
        cases y with
        | inl a' => exact congrArg Sum.inl (f.injective hxy)
        | inr b => exact (hdisjoint a b hxy).elim
    | inr b =>
        cases y with
        | inl a => exact (hdisjoint a b hxy.symm).elim
        | inr b' => exact congrArg Sum.inr (g.injective hxy)


noncomputable def
    lpReplicaAggregateRankFiveCombinedEmbeddingOfNonstrictEmbedding
    {S : Type*} (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (handled : S ↪ LPReplicaAggregateDecoratedTarget G sites q)
    (hnonstrict : ∀ s, ¬
      LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites q (handled s)) :
    S ⊕ LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q := by
  let strict := lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding
    G sites hsite q hcard
  apply embeddingSumOfDisjointImages handled strict.toEmbedding
  intro s z hcollision
  apply hnonstrict s
  rw [hcollision]
  exact lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding_strict
    G sites hsite q hcard z


noncomputable def lpReplicaOffdiagRankFiveOutputCollisionClass
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y)).filter
    fun z => output z = y


end
end StatMech.Ising
