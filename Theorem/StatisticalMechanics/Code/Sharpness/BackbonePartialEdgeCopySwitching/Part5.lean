/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part8
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneLabeledSwitching

open FluxEdgeCopy

open RandomCurrent

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem rawPairFiberMass_tsum_eq_mul
    (beta : Real) (J : Sym2 V -> Real)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R] :
    (∑' p : G.edgeFinset -> Nat,
        if Q p then weight G beta J (ofEdgeFun G p) else 0) *
      (∑' q : G.edgeFinset -> Nat,
        if R q then weight G beta J (ofEdgeFun G q) else 0) =
      ∑' m : G.edgeFinset -> Nat,
        rawPairFiberMass G beta J m Q R := by
  classical
  let f : (G.edgeFinset -> Nat) -> Real := fun p =>
    if Q p then weight G beta J (ofEdgeFun G p) else 0
  let g : (G.edgeFinset -> Nat) -> Real := fun q =>
    if R q then weight G beta J (ofEdgeFun G q) else 0
  have hfnorm : Summable (fun p => ‖f p‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => ?_) (summable_norm_weight_ofEdgeFun G beta J)
    by_cases hp : Q p <;> simp [f, hp]
  have hgnorm : Summable (fun q => ‖g q‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => ?_) (summable_norm_weight_ofEdgeFun G beta J)
    by_cases hq : R q <;> simp [g, hq]
  have hfg : Summable (fun z : (G.edgeFinset -> Nat) ×
      (G.edgeFinset -> Nat) => f z.1 * g z.2) :=
    summable_mul_of_summable_norm hfnorm hgnorm
  let F : (Σ m : (G.edgeFinset -> Nat),
      {p : G.edgeFinset -> Nat // p <= m}) -> Real := fun s =>
    f s.2.1 * g (fun e => s.1 e - s.2.1 e)
  have hcomp : ∀ z : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat),
      f z.1 * g z.2 = F (pairEquivSigma z) := by
    rintro ⟨p, q⟩
    simp only [F, pairEquivSigma, Equiv.coe_fn_mk]
    have hsub : (fun e => p e + q e - p e) = q := by
      ext e
      simp
    rw [hsub]
  have hsumF : Summable F := by
    rw [← (pairEquivSigma (E := G.edgeFinset)).summable_iff]
    exact hfg.congr hcomp
  change (∑' p, f p) * (∑' q, g q) = _
  rw [show (∑' p, f p) * (∑' q, g q) =
      ∑' z : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat),
        f z.1 * g z.2 by
    exact Summable.tsum_mul_tsum hfnorm.of_norm hgnorm.of_norm hfg]
  rw [tsum_congr hcomp, (pairEquivSigma (E := G.edgeFinset)).tsum_eq F,
    Summable.tsum_sigma hsumF]
  apply tsum_congr
  intro m
  rw [tsum_fintype]
  unfold rawPairFiberMass
  apply Finset.sum_congr rfl
  intro K _
  simp only [F]
  unfold f g rawSplitWeight
  by_cases hQ : Q K.1 <;>
    by_cases hR : R (fun e => m e - K.1 e) <;>
    simp [hQ, hR]


theorem rawFiberMass_eq_rawPairFiberMass
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q] :
    rawFiberMass G beta J m A Q =
      rawPairFiberMass G beta J m
        (fun p => sources G (ofEdgeFun G p) = A ∧ Q p) (fun _ => True) := by
  classical
  unfold rawFiberMass rawPairFiberMass
  apply Finset.sum_congr rfl
  intro K _
  simp


theorem tsum_rawFiberMass_eq_mul_unrestricted
    (beta : Real) (J : Sym2 V -> Real) (A : Finset V)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q] :
    (∑' m : G.edgeFinset -> Nat, rawFiberMass G beta J m A Q) =
      (∑' p : G.edgeFinset -> Nat,
        if sources G (ofEdgeFun G p) = A ∧ Q p then
          weight G beta J (ofEdgeFun G p) else 0) *
      (∑' q : G.edgeFinset -> Nat, weight G beta J (ofEdgeFun G q)) := by
  classical
  rw [show (∑' m : G.edgeFinset -> Nat, rawFiberMass G beta J m A Q) =
      ∑' m : G.edgeFinset -> Nat,
        rawPairFiberMass G beta J m
          (fun p => sources G (ofEdgeFun G p) = A ∧ Q p)
          (fun _ => True) by
    apply tsum_congr
    intro m
    exact rawFiberMass_eq_rawPairFiberMass G beta J m A Q]
  rw [← rawPairFiberMass_tsum_eq_mul G beta J
    (fun p => sources G (ofEdgeFun G p) = A ∧ Q p) (fun _ => True)]
  congr 1


theorem rawPredicateMass_eq_labeled
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q] :
    (∑ K : {p : G.edgeFinset -> Nat // p <= m},
      if Q K.1 then rawSplitWeight G beta J m K else 0) =
      ∑ S : Finset (FluxEdgeCopy.Copy G m),
        if Q (profileFlux G m S) then
          labeledWeight G beta J m S else 0 := by
  classical
  have hstep : ∀ K : {p : G.edgeFinset -> Nat // p <= m},
      (if Q K.1 then rawSplitWeight G beta J m K else 0) =
        (∏ e : G.edgeFinset, (m e).choose (K.1 e)) •
          (if Q K.1 then weight G beta J (ofEdgeFun G m) else 0) := by
    intro K
    by_cases hQ : Q K.1
    · rw [if_pos hQ, if_pos hQ, rawSplitWeight,
        weight_split_eq_binom G beta J m K.1 K.2,
        nsmul_eq_mul, Nat.cast_prod]
      have hprod :
          (∏ e ∈ G.edgeFinset,
              (Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1) e) : Real)) =
            ∏ e : G.edgeFinset, ((m e).choose (K.1 e) : Real) := by
        rw [← Finset.prod_attach G.edgeFinset
          (fun e =>
            (Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1) e) : Real))]
        apply Finset.prod_congr rfl
        intro e _
        unfold ofEdgeFun
        rw [dif_pos e.2, dif_pos e.2]
      rw [hprod]
    · simp [hQ]
  simp_rw [hstep]
  rw [FluxEdgeCopy.flux_edgecopy_bridge G m
    (fun k => if Q k then weight G beta J (ofEdgeFun G m) else 0)]
  rfl


end BackboneLabeledSwitching
end
end StatMech.Sharpness
