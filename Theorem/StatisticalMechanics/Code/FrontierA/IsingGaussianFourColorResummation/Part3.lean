/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorFamilies.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourCurrentTree
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorEdgecopyBridge
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneResummation
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneCardBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorResummation.Part3
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem finiteTreeMixedFourMass_le_sum_separated_of_cardBound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l)
    (hcard : FiniteTreeColoringCardBound G i j k l) :
    finiteTreeMixedFourMass G beta J i j k l <=
      ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y := by
  let fm : (G.edgeFinset -> Nat) -> Real := fun total =>
    (#(finiteTreeMixedColorings (endsM G total)
        Finset.univ i j k l) : Real) *
      weight G beta J (ofEdgeFun G total)
  let fs : V -> (G.edgeFinset -> Nat) -> Real := fun y total =>
    (#(finiteTreeSeparatedBranchColorings (endsM G total)
        Finset.univ i j k l y) : Real) *
      weight G beta J (ofEdgeFun G total)
  have hmix := finiteTreeMixedFourMass_eq_card_tsum
    G beta J hbeta hJ hij hkl
  have hsep (y : V) := finiteTreeSeparatedFourMass_eq_card_tsum
    G beta J hbeta hJ hij hkl y
  have hmixSum : Summable fm := by simpa only [fm] using hmix.1
  have hsepSum : ∀ y, Summable (fs y) := by
    intro y
    simpa only [fs] using (hsep y).1
  have hsepOuter : Summable (fun total => ∑ y : V, fs y total) := by
    let S : Finset V := Finset.univ
    have hfinite : ∀ T : Finset V,
        Summable (fun total => ∑ y ∈ T, fs y total) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simpa using
          (summable_zero : Summable
            (fun _ : G.edgeFinset -> Nat => (0 : Real)))
      | @insert y T hyT ih =>
          simpa [Finset.sum_insert hyT] using (hsepSum y).add ih
    simpa [S] using hfinite S
  have hpoint : ∀ total, fm total <= ∑ y : V, fs y total := by
    intro total
    dsimp only [fm, fs]
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hcard total
    · exact StatMech.Ising.acw_weight_nonneg G beta J hbeta hJ _
  calc
    finiteTreeMixedFourMass G beta J i j k l = ∑' total, fm total := by
      simpa only [fm] using hmix.2
    _ <= ∑' total, ∑ y : V, fs y total :=
      hmixSum.tsum_le_tsum hpoint hsepOuter
    _ = ∑ y : V, ∑' total, fs y total := by
      exact Summable.tsum_finsetSum (s := (Finset.univ : Finset V))
        (fun y _ => hsepSum y)
    _ = ∑ y : V, finiteTreeSeparatedFourMass G beta J i j k l y := by
      apply Finset.sum_congr rfl
      intro y hy
      simpa only [fs] using (hsep y).2.symm

end StatMech.FrontierA
