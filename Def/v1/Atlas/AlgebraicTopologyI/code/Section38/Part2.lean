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
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section38


noncomputable section

open Metric Set

namespace BorsukUlam

attribute [instance] F2CohomRPn.instAddCommGroup

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


end PoincareDuality
end
