/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ideles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part10
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Adeles
import Theorem.v1.Atlas.NumberTheoryI.code.Ideles


noncomputable section

open NumberField IsDedekindDomain

namespace Ideles

section IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

def adelicNorm : IdeleGroup K →* ℝ where
  toFun a := NumberField.Adeles.adelicAbsVal (a : NumberField.AdeleRing (𝓞 K) K)
  map_one' := by
    show NumberField.Adeles.adelicAbsVal
      ((1 : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K) = 1
    rw [Units.val_one]
    unfold NumberField.Adeles.adelicAbsVal
    have h1 : ∀ w : InfinitePlace K,
        ‖(1 : NumberField.AdeleRing (𝓞 K) K).1 w‖ = 1 := by
      intro w
      show ‖(1 : InfiniteAdeleRing K) w‖ = 1
      have : (1 : InfiniteAdeleRing K) w = 1 := Pi.one_apply w
      rw [this]; exact IsAbsoluteValue.abv_one' norm
    have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖(1 : NumberField.AdeleRing (𝓞 K) K).2 v‖ = 1 := by
      intro v
      show ‖(1 : FiniteAdeleRing (𝓞 K) K) v‖ = 1
      have : (1 : FiniteAdeleRing (𝓞 K) K) v = 1 := RestrictedProduct.one_apply _ v
      rw [this, norm_one]
    have hinf : (∏ w : InfinitePlace K,
        ‖(1 : NumberField.AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) = 1 := by
      apply Finset.prod_eq_one; intro w _; rw [h1 w, one_pow]
    have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖(1 : NumberField.AdeleRing (𝓞 K) K).2 v‖) = 1 := by
      rw [show (fun v => ‖(1 : NumberField.AdeleRing (𝓞 K) K).2 v‖) =
        (fun _ => (1 : ℝ)) from funext h2]
      exact finprod_one
    rw [hinf, hfin, mul_one]

  map_mul' a b := by
    show NumberField.Adeles.adelicAbsVal _ = NumberField.Adeles.adelicAbsVal _ *
      NumberField.Adeles.adelicAbsVal _
    unfold NumberField.Adeles.adelicAbsVal
    have hinf : (∏ w : InfinitePlace K,
        ‖((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) =
        (∏ w, ‖(a : NumberField.AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) *
        (∏ w, ‖(b : NumberField.AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro w _
      have hmul : ((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).1 w =
                  (a : NumberField.AdeleRing (𝓞 K) K).1 w *
                  (b : NumberField.AdeleRing (𝓞 K) K).1 w := by
        show ((↑a * ↑b : NumberField.AdeleRing (𝓞 K) K)).1 w = _; rfl
      rw [hmul]
      have hn : ‖(a : NumberField.AdeleRing (𝓞 K) K).1 w *
                  (b : NumberField.AdeleRing (𝓞 K) K).1 w‖ =
                ‖(a : NumberField.AdeleRing (𝓞 K) K).1 w‖ *
                ‖(b : NumberField.AdeleRing (𝓞 K) K).1 w‖ :=
        NormedField.norm_mul _ _
      erw [hn, mul_pow]
    have hfmul : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 v‖ =
        ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ *
        ‖(b : NumberField.AdeleRing (𝓞 K) K).2 v‖ := by
      intro v
      have : ((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 v =
             (a : NumberField.AdeleRing (𝓞 K) K).2 v *
             (b : NumberField.AdeleRing (𝓞 K) K).2 v := by
        show ((↑a * ↑b : NumberField.AdeleRing (𝓞 K) K)).2 v = _; rfl
      rw [this, norm_mul]
    have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 v‖) =
        (∏ᶠ v, ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖) *
        (∏ᶠ v, ‖(b : NumberField.AdeleRing (𝓞 K) K).2 v‖) := by
      rw [show (fun v => ‖((a * b : IdeleGroup K) :
            NumberField.AdeleRing (𝓞 K) K).2 v‖) =
          (fun v => ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ *
            ‖(b : NumberField.AdeleRing (𝓞 K) K).2 v‖) from funext hfmul]
      exact finprod_mul_distrib
        (adeleRing_unit_fin_norm_finMulSupport K a)
        (adeleRing_unit_fin_norm_finMulSupport K b)
    rw [hinf, hfin]; ring

def OneIdeleGroup : Subgroup (IdeleGroup K) :=
  (adelicNorm K).ker

end IdeleGroup
end Ideles
end
