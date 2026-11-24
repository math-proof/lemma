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
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
public import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
public import Def.v1.Atlas.NumberTheoryI.code.Adeles


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

instance adeleRing_isTopologicalRing : IsTopologicalRing (adeleRing (K := K)) :=
  inferInstance

instance infiniteAdeleRing_t2Space : T2Space (InfiniteAdeleRing K) := Pi.t2Space

instance finiteAdeleRing_t2Space : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite))

instance adeleRing_t2Space : T2Space (adeleRing (K := K)) :=
  Prod.t2Space

instance finiteAdeleRing_locallyCompactSpace :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := by


  letI wlcs : WeaklyLocallyCompactSpace (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite) :=
    RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite
      (fun v => by convert Valued.isOpen_integer (v.adicCompletion K) using 1)
      (Filter.Eventually.of_forall (fun v => isCompact_adicCompletionIntegers v))

  letI : WeaklyLocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := wlcs

  infer_instance

instance adeleRing_locallyCompactSpace : LocallyCompactSpace (adeleRing (K := K)) :=
  Prod.locallyCompactSpace _ _

end RestrictedProductDirectLimit
end NumberField.Adeles
end
