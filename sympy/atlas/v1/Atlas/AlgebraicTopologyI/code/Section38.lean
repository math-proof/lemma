/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section38.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section17
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section17
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section37
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section26
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section34
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section37
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

noncomputable section

open Metric Set

namespace BorsukUlam

/-- The `k`-th singular cohomology of real projective `n`-space `ℝPⁿ` with coefficients in
`𝔽₂ = ZMod 2`, packaged as a plain `Type`. Used to set up the Borsuk–Ulam proof via the
mod-2 cohomology ring of `ℝPⁿ`. -/
def F2CohomRPn (n k : ℕ) : Type :=
  (SingularCohomology.singularCohomology (ZMod 2)
    (TopCat.of (RealProjectiveSpace.RPn n))
    (ModuleCat.of (ZMod 2) (ZMod 2)) k : Type)

/-- The additive commutative group structure on `F2CohomRPn n k` inherited from its
`ModuleCat` representation. -/
@[reducible] def F2CohomRPn.instAddCommGroup (n k : ℕ) : AddCommGroup (F2CohomRPn n k) :=
  ModuleCat.isAddCommGroup
    (SingularCohomology.singularCohomology (ZMod 2)
      (TopCat.of (RealProjectiveSpace.RPn n))
      (ModuleCat.of (ZMod 2) (ZMod 2)) k)
attribute [instance] F2CohomRPn.instAddCommGroup

/-- The cup product `H^p(ℝPⁿ; 𝔽₂) ⊗ H^q(ℝPⁿ; 𝔽₂) → H^{p+q}(ℝPⁿ; 𝔽₂)` on mod-2 cohomology
of `ℝPⁿ`, exposed as a binary function on the underlying types. -/
noncomputable def F2CohomRPn.cupProduct (n p q : ℕ) :
    F2CohomRPn n p → F2CohomRPn n q → F2CohomRPn n (p + q) :=
  fun a b => (SingularCohomology.cupProduct (ZMod 2)
    (TopCat.of (RealProjectiveSpace.RPn n)) p q) (a ⊗ₜ[ZMod 2] b)

/-- The `ZMod 2`-module structure on `F2CohomRPn n k`, inherited from the underlying
`ModuleCat` object. -/
noncomputable instance F2CohomRPn.instModule (n k : ℕ) : Module (ZMod 2) (F2CohomRPn n k) :=
  ModuleCat.isModule
    (SingularCohomology.singularCohomology (ZMod 2)
      (TopCat.of (RealProjectiveSpace.RPn n))
      (ModuleCat.of (ZMod 2) (ZMod 2)) k)

/-- For `1 ≤ n` and `k ≤ n`, the mod-2 cohomology group `H^k(ℝPⁿ; 𝔽₂)` is one-dimensional
over `𝔽₂`. This encodes the standard fact that `H^*(ℝPⁿ; 𝔽₂) ≅ 𝔽₂[x]/(x^{n+1})`. -/
noncomputable def F2CohomRPn.cohomologyPullback
    {n₁ n₂ : ℕ}
    (f : C(RealProjectiveSpace.RPn n₁, RealProjectiveSpace.RPn n₂))
    (k : ℕ) : F2CohomRPn n₂ k →+ F2CohomRPn n₁ k :=
  (SingularCohomology.singularCohomologyMap (ZMod 2)
    (TopCat.ofHom f) k).hom.toAddMonoidHom

/-- An antipodal-preserving continuous map `g : Sᵐ → Sᵐ⁻¹` descends to the quotient by the
antipodal action to yield a continuous map `ℝPᵐ → ℝPᵐ⁻¹`. Defined for `m ≥ 2`. -/
noncomputable def F2CohomRPn.descendedMap : (m : ℕ) → (hm : m ≥ 2) →
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin m)) 1))) →
    (hg : ∀ x, g (-x) = -g x) →
    C(RealProjectiveSpace.RPn m, RealProjectiveSpace.RPn (m - 1))
  | n + 2, _, g, hg =>
    ⟨Quotient.lift
      (fun x : RealProjectiveSpace.Sphere (n + 2) =>
        @Quotient.mk' (RealProjectiveSpace.Sphere (n + 1))
          (RealProjectiveSpace.antipodalSetoid (n + 1)) (g x))
      (fun a b hab => by
        rcases hab with hab | hab
        · congr 1; exact Subtype.ext hab
        · apply Quotient.sound
          show (↑(g a) : EuclideanSpace ℝ (Fin (n + 2))) = ↑(g b) ∨
               (↑(g a) : EuclideanSpace ℝ (Fin (n + 2))) = -↑(g b)
          right
          have heq : a = -b := Subtype.ext hab
          have := hg b; rw [← heq] at this
          exact congrArg Subtype.val this),
      (continuous_quotient_mk' (s := RealProjectiveSpace.antipodalSetoid (n + 1))).comp
        g.continuous |>.quotient_lift _⟩
  | 0, hm, _, _ => absurd hm (by omega)
  | 1, hm, _, _ => absurd hm (by omega)

/-- The cohomology pullback `H^k(ℝPᵐ⁻¹; 𝔽₂) → H^k(ℝPᵐ; 𝔽₂)` induced by an odd map
`g : Sᵐ → Sᵐ⁻¹` via its descent `ℝPᵐ → ℝPᵐ⁻¹`. -/
noncomputable def F2CohomRPn.pullback (m : ℕ) (hm : m ≥ 2)
    (g : C(↥(sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
          ↥(sphere (0 : EuclideanSpace ℝ (Fin m)) 1)))
    (hg : ∀ x, g (-x) = -g x)
    (k : ℕ) : F2CohomRPn (m - 1) k →+ F2CohomRPn m k :=
  F2CohomRPn.cohomologyPullback (F2CohomRPn.descendedMap m hm g hg) k

/-- The descended map of an odd `g : Sᵐ → Sᵐ⁻¹` pulls the canonical degree-1 mod-2
cohomology generator of `ℝPᵐ⁻¹` back to the canonical degree-1 generator of `ℝPᵐ`. -/
end BorsukUlam

open Manifold CategoryTheory

namespace PoincareDuality

variable (R : Type) [CommRing R]

/-- Poincaré–Lefschetz duality (Theorem 38.1) for an `R`-oriented `d`-manifold along a
compact set `K`: capping with the fundamental class `[M]_K` gives an isomorphism
`Ȟ^p(K; R) ≅ H_q(M, M\K; R)` whenever `p + q = d`. -/
noncomputable def capProduct_cechCohomology_iso
    (d : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
    (K : Set M) (hK : IsCompact K)
    [hOr : IsROrientedAlong R d M K]
    (p q : ℕ) (hpq : p + q = d) :
    cechCohomology R M K ∅ p ≅ relativeSingularHomology R M Kᶜ q :=
  poincareDualityCompact R d M K hK p q hpq

/-- Corollary 38.2: for `K` a compact subset of an `R`-oriented `d`-manifold and `p > d`,
the Čech cohomology `Ȟ^p(K; R)` vanishes. -/
def ReducedSingularHomology
    (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (q : ℕ) : Type :=
  match q with
  | 0 => ↥(LinearMap.ker (augmentationH0 R (TopCat.of X)).hom)
  | n + 1 => (SingularCohomology.singularHomologyModule R (TopCat.of X) (n + 1) : Type)


/-- The additive commutative group structure on reduced singular homology, inherited
from the augmentation kernel (degree 0) or from singular homology (higher degrees). -/
instance ReducedSingularHomology.instAddCommGroup
    (X : Type) [TopologicalSpace X] (q : ℕ) :
    AddCommGroup (ReducedSingularHomology R X q) := by
  unfold ReducedSingularHomology
  match q with
  | 0 => exact Submodule.addCommGroup _
  | n + 1 => exact (SingularCohomology.singularHomologyModule R (TopCat.of X) (n + 1)).isAddCommGroup

/-- The `R`-module structure on reduced singular homology. -/
instance ReducedSingularHomology.instModule
    (X : Type) [TopologicalSpace X] (q : ℕ) :
    Module R (ReducedSingularHomology R X q) := by
  unfold ReducedSingularHomology
  match q with
  | 0 => exact Submodule.module _
  | n + 1 => exact (SingularCohomology.singularHomologyModule R (TopCat.of X) (n + 1)).isModule

/-- Convenient abbreviation for the unit sphere `Sⁿ ⊂ ℝⁿ⁺¹` viewed as a subtype. -/
abbrev SphereType (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- Alexander duality on the sphere: for `K` compact in `Sⁿ` and `1 ≤ q ≤ n - 1`,
the Čech cohomology `Ȟ^q(K; R)` is isomorphic to the reduced singular homology
`\widetilde H_{n-q-1}(Sⁿ \ K; R)`. -/
abbrev singularCohomologyType
    (M : Type) [TopologicalSpace M] (p : ℕ) : Type :=
  (relativeSingularCohomology R M ∅ p : Type)

/-- Convenient `Type` view of singular homology `H_q(M; R)`, defined here as the
relative homology against the empty pair. -/
abbrev singularHomologyType (R : Type) [CommRing R]
    (M : Type) [TopologicalSpace M] (q : ℕ) : Type :=
  (relativeSingularHomology R M ∅ q : Type)

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

/-- Corollary 38.6: the complement of a knot in `S³` is a homology circle. -/
end AlgebraicTopologyI

end
