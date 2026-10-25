/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisPlaceHelper
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisPlaceHelper
import Def.v1.Atlas.ArithmeticGeometry.code.Heights


noncomputable section

open Height MvPolynomial

namespace AbsoluteHeight

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Empty.Finite ι]

theorem NumberField.FinitePlace.isFinitePlace_comp_galois {K : Type*} [Field K] [NumberField K]
    (σ : K ≃ₐ[ℚ] K) (v : NumberField.FinitePlace K) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      place (NumberField.FinitePlace.embedding w) =
        v.val.comp (f := (σ.symm : K →+* K)) σ.symm.injective := by
  let p := v.maximalIdeal
  let e : (NumberField.RingOfIntegers K) ≃+* (NumberField.RingOfIntegers K) :=
    NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv
  let w := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e p

  have habsN : Ideal.absNorm w.asIdeal = Ideal.absNorm p.asIdeal := by
    have hasideal : w.asIdeal =
        Ideal.comap (e.symm : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
          p.asIdeal := by
      show (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = _
      rw [IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv_apply,
          IsDedekindDomain.HeightOneSpectrum.comap_asIdeal]
    rw [hasideal, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot, Submodule.cardQuot]
    have h : p.asIdeal =
        (Ideal.comap (e.symm : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
          p.asIdeal).map
          (e.symm : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K) :=
      (Ideal.map_comap_of_surjective
        (e.symm : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K)
        e.symm.surjective p.asIdeal).symm
    exact Nat.card_congr (Ideal.quotientEquiv _ p.asIdeal e.symm h).toEquiv
  use w
  apply AbsoluteValue.ext; intro x
  show ‖NumberField.FinitePlace.embedding w x‖ = v.val (σ.symm x)
  have hv : v = NumberField.FinitePlace.mk p :=
    (NumberField.FinitePlace.mk_maximalIdeal v).symm
  conv_rhs => rw [hv]
  show ‖NumberField.FinitePlace.embedding w x‖ =
    ‖NumberField.FinitePlace.embedding p (σ.symm x)‖
  rw [NumberField.FinitePlace.norm_embedding', NumberField.FinitePlace.norm_embedding']

  have hval : w.valuation K x = p.valuation K (σ.symm x) := by
    obtain ⟨a, b, hb, rfl⟩ :=
      IsFractionRing.div_surjective (NumberField.RingOfIntegers K) x
    simp only [map_div₀]
    congr 1 <;> {
      rw [show σ.symm (algebraMap (NumberField.RingOfIntegers K) K _) =
            algebraMap (NumberField.RingOfIntegers K) K (e.symm _) from by
        change σ.symm (_ : K) =
          ((NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm _ : K)
        rw [NumberField.RingOfIntegers.mapRingEquiv_symm_apply]; rfl,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact (intValuation_equivOfRingEquiv e p _).symm }
  rw [hval]
  simp only [habsN]

end AbsoluteHeight
end
