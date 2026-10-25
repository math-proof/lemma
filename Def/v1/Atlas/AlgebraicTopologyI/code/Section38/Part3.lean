/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section38.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section17.Part6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section17
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section37
import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section37.Part3
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section38


noncomputable section

open Metric Set

open Manifold CategoryTheory

namespace PoincareDuality

variable (R : Type) [CommRing R]

/-- Bridge equivalence between the relative cohomology against the empty pair and the
absolute singular cohomology object used elsewhere in the library. -/
noncomputable def fundamentalClass
    (R : Type) [CommRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M] :
    singularHomologyType R M n :=
  (fundamentalClass_of_isROrientable R n M (IsROriented.isROrientable (R := R))).choose

/-- The Kronecker pairing kills torsion on the cohomology side: torsion classes in
`H^p(M; R)` lie in the left kernel of the Kronecker pairing. -/
noncomputable def poincareDuality_modTorsion_equiv
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsROriented R n M]
    (p q : ℕ) (hpq : p + q = n) :
    (singularCohomologyType R M q ⧸
      Submodule.torsion R (singularCohomologyType R M q)) ≃ₗ[R]
    (singularHomologyType R M p ⧸
      Submodule.torsion R (singularHomologyType R M p)) :=
  let e := (poincareDualityIso R n M q p (by linarith)).toLinearEquiv
  Submodule.Quotient.equiv
    (Submodule.torsion R (singularCohomologyType R M q))
    (Submodule.torsion R (singularHomologyType R M p))
    e
    (by
      ext x
      simp only [Submodule.mem_map, Submodule.mem_torsion'_iff]
      constructor
      · rintro ⟨y, ⟨a, ha⟩, rfl⟩
        exact ⟨a, by
          show (a : R) • e y = 0
          rw [← e.map_smul]
          show e ((a : R) • y) = 0
          have : (a : R) • y = 0 := ha
          rw [this, map_zero]⟩
      · intro ⟨a, ha⟩
        refine ⟨e.symm x, ⟨a, ?_⟩, e.apply_symm_apply x⟩
        show (a : R) • e.symm x = 0
        rw [← e.symm.map_smul]
        show e.symm ((a : R) • x) = 0
        have : (a : R) • x = 0 := ha
        rw [this, map_zero])


/-- Compatibility of the Poincaré duality isomorphism with the cohomology/homology
bridge equivalences: applying the bridge map after Poincaré duality equals capping
with the (transported) fundamental class. -/

end PoincareDuality

namespace AlexanderDuality

open PoincareDuality

/-- The reduced singular homology `\widetilde H_{-1}(Kᶜ; R)` — interpreted via natural
subtraction `0 - 1 = 0` and the augmentation kernel definition — is trivial. -/

end AlexanderDuality

open CategoryTheory AlgebraicTopology Limits TopCat

namespace AlgebraicTopologyI

/-- A knot is a topological embedding `S¹ ↪ S³`. -/
def IsKnot (f : (𝕊 1 : TopCat.{0}) ⟶ (𝕊 3 : TopCat.{0})) : Prop :=
  Topology.IsEmbedding f

/-- The complement `S³ \ f(S¹)` of a knot `f : S¹ ↪ S³`, packaged as a topological
space. -/
def knotComplement (f : (𝕊 1 : TopCat.{0}) ⟶ (𝕊 3 : TopCat.{0})) : TopCat.{0} :=
  TopCat.of { x : (𝕊 3 : TopCat.{0}) | x ∉ Set.range f }

/-- A space `X` is a homology circle if its singular homology agrees with that of the
circle `S¹` in every degree and over every commutative ring `R`. -/
def IsHomologyCircle (X : TopCat.{0}) : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ),
    Nonempty (SingularCohomology.singularHomologyModule R X n ≅
              SingularCohomology.singularHomologyModule R (𝕊 1 : TopCat.{0}) n)

end AlgebraicTopologyI
end
