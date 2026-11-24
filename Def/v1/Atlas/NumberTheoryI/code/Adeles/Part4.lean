module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.Topology.Algebra.Group.Compact
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
public import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
public import Instance.v1.Atlas.NumberTheoryI.code.Adeles.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open NumberField IsDedekindDomain

open scoped TensorProduct

namespace NumberField.Adeles

variable {K : Type*} [Field K] [NumberField K]

section RestrictedProductDirectLimit

open Filter Set Topology

attribute [local instance] WithAbs.algebraLeft

noncomputable def primeBelow (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))
  isPrime := Ideal.IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))
  ne_bot := by intro h; exact w.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)

noncomputable def localBaseChangeMap (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L)) :
    WithVal (HeightOneSpectrum.valuation K (primeBelow K L w)) →+*
      w.adicCompletion L :=
  (UniformSpace.Completion.coeRingHom (α := WithVal (HeightOneSpectrum.valuation L w))).comp
    ((WithVal.equiv (HeightOneSpectrum.valuation L w)).symm.toRingHom.comp
      ((algebraMap K L).comp
        (WithVal.equiv (HeightOneSpectrum.valuation K (primeBelow K L w))).toRingHom))

end RestrictedProductDirectLimit
end NumberField.Adeles
end
