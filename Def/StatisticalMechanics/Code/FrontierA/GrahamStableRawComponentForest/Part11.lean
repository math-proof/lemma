/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part10
open Finset


namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


attribute [instance]
  FiniteRelationMinimalTightProblem.stateFintype
  FiniteRelationMinimalTightProblem.stateDecidableEq
  FiniteRelationMinimalTightProblem.tokenFintype
  FiniteRelationMinimalTightProblem.tokenDecidableEq

noncomputable def FiniteRelationCrossingContinuation.initialMatching
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    StatMech.FrontierA.RelationPartialMatching continuation.incident where
  toFun
    | Sum.inl index =>
        if index = continuation.index then none else some index
    | Sum.inr _ => some continuation.index
  related := by
    intro state token htoken
    cases state with
    | inl index =>
        simp only at htoken
        split at htoken
        next _ => contradiction
        next _ =>
          have : index = token := Option.some.inj htoken
          subst token
          exact continuation.aligned index
    | inr _ =>
        simp only [Option.some.injEq] at htoken
        subst token
        exact continuation.crossing
  injective_some := by
    intro first second token hfirst hsecond
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            simp only at hfirst hsecond
            split at hfirst
            next _ => contradiction
            next _ =>
              split at hsecond
              next _ => contradiction
              next _ => exact congrArg Sum.inl (Option.some.inj
                (hfirst.trans hsecond.symm))
        | inr _ =>
            simp only at hfirst hsecond
            split at hfirst
            next _ => contradiction
            next hne =>
              have heq : first = continuation.index := Option.some.inj
                (hfirst.trans hsecond.symm)
              exact False.elim (hne heq)
    | inr first =>
        cases second with
        | inl second =>
            simp only at hfirst hsecond
            split at hsecond
            next _ => contradiction
            next hne =>
              have heq : second = continuation.index := Option.some.inj
                (hsecond.trans hfirst.symm)
              exact False.elim (hne heq)
        | inr second =>
            exact congrArg Sum.inr (Subsingleton.elim first second)

end StatMech.GrahamGHS.FourColor
