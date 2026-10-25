/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section34.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section31
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part7
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Order.Directed
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Sets.Opens
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Def.v1.Atlas.AlgebraicTopologyI.code.Section34.Part7
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


noncomputable section

namespace CapProduct

variable (R : Type) [CommRing R]

/-- **Abstract cap-product pairing** (Section 34).  A bundled
specification of a cap-product: three `R`-modules (`CohomGrp`, the
"cohomology group" acting; and two "relative homology groups" `RelHomGrpN`
and `RelHomGrpQ`) together with a bilinear pairing
`cap : CohomGrp →ₗ[R] RelHomGrpN →ₗ[R] RelHomGrpQ`.  This abstracts the
algebraic structure of the cap product `H^p(Y; R) ⊗ H_{p+q}(Y, A) → H_q(Y, A)`
so that the projection-and-excision proof of Lemma 34.3 works at the level
of an axiomatic interface, free of singular-cohomology specifics. -/
structure CapProductPairing (R : Type) [CommRing R] where
  CohomGrp : Type
  [instCohomACG : AddCommGroup CohomGrp]
  [instCohomMod : Module R CohomGrp]
  RelHomGrpN : Type
  [instRelHomNACG : AddCommGroup RelHomGrpN]
  [instRelHomNMod : Module R RelHomGrpN]
  RelHomGrpQ : Type
  [instRelHomQACG : AddCommGroup RelHomGrpQ]
  [instRelHomQMod : Module R RelHomGrpQ]
  cap : CohomGrp →ₗ[R] RelHomGrpN →ₗ[R] RelHomGrpQ

attribute [instance] CapProductPairing.instCohomACG CapProductPairing.instCohomMod
  CapProductPairing.instRelHomNACG CapProductPairing.instRelHomNMod
  CapProductPairing.instRelHomQACG CapProductPairing.instRelHomQMod

/-- **Geometrically situated cap-product pairing.**  A
`CapProductPairing` tagged with the data of an open set `Y` and a subset
`K ⊆ Y` in some ambient space `X`; this provides the geometric context
(open set, compact subset, etc.) needed for the excision-and-projection
argument used in Lemma 34.3. -/
structure CapProductPairingOf (R : Type) [CommRing R]
    {X : Type*} [TopologicalSpace X] (Y K : Set X) (hY : IsOpen Y) (hK : K ⊆ Y)
    extends CapProductPairing R

/-- **Abstract excision data.**  When `V ⊆ U` are two open subsets both
containing `K`, the inclusion-induced relative-homology maps
`H_*(V, V \ K) → H_*(U, U \ K)` are isomorphisms (excision); the
`ExcisionData` bundles the *inverse* linear maps as opaque morphisms,
without yet requiring them to be specific singular-homology
isomorphisms.  This is what lets the abstract Lemma 34.3 talk about
excision without proving it. -/
structure ExcisionData (R : Type) [CommRing R]
    {X : Type*} [TopologicalSpace X] {K U V : Set X}
    (hK : IsClosed K) (hVU : V ⊆ U)
    (pairU : CapProductPairing R) (pairV : CapProductPairing R) where
  excInvN : pairU.RelHomGrpN →ₗ[R] pairV.RelHomGrpN
  excInvQ : pairU.RelHomGrpQ →ₗ[R] pairV.RelHomGrpQ

/-- **Abstract projection formula.**  For two cap-product pairings
`pairY, pairZ` representing the cap products on a "smaller" space `Y` and
a "larger" space `Z`, this structure bundles a pullback on cohomology
together with pushforwards on the two relative-homology groups, such that
the diagram `f_*(f^*b ⌢ x) = b ⌢ f_*x` commutes.  This is the algebraic
content of the projection (naturality) formula for the cap product. -/
structure ProjectionFormula (R : Type) [CommRing R]
    (pairY pairZ : CapProductPairing R) where
  pullback : pairZ.CohomGrp →ₗ[R] pairY.CohomGrp
  pushforwardN : pairY.RelHomGrpN →ₗ[R] pairZ.RelHomGrpN
  pushforwardQ : pairY.RelHomGrpQ →ₗ[R] pairZ.RelHomGrpQ
  formula : ∀ (b : pairZ.CohomGrp) (x : pairY.RelHomGrpN),
    pushforwardQ (pairY.cap (pullback b) x) = pairZ.cap b (pushforwardN x)

end CapProduct
end
