import Mathlib
import Instance.CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option autoImplicit false

open scoped MatrixGroups Topology

namespace CerednikDrinfeld
namespace Omega

section Moebius

variable (K₀ : Type*) [Field K₀] (K : Type*) [Field K] [Algebra K₀ K]


def moebius (g : GL (Fin 2) K₀) (z : K) : K :=
  (algebraMap K₀ K (g 0 0) * z + algebraMap K₀ K (g 0 1)) / (algebraMap K₀ K (g 1 0) * z + algebraMap K₀ K (g 1 1))

variable {K} in

def toAffine (x : OnePoint K) : K := OnePoint.elim x 0 id


variable {K} in

noncomputable def pmoebius [DecidableEq K] (g : PGL(2, K₀)) (z : K) : K := toAffine (g • (z : OnePoint K))

end Moebius

def upperHalfPlane (K₀ : Type*) [Field K₀] (K : Type*) [Field K] [Algebra K₀ K] : Set K :=
  (Set.range (algebraMap K₀ K))ᶜ


section Theta

variable {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] {G : Type*} [Group G]

def crossRatio (z z₀ x y : K) : K := ((z - x) * (z₀ - y)) / ((z - y) * (z₀ - x))

noncomputable def thetaFactor [DecidableEq K] (ρ : G →* PGL(2, K₀)) (a b z₀ z : K) (γ : G) : K :=
  crossRatio z z₀ (pmoebius K₀ (ρ γ) a) (pmoebius K₀ (ρ γ) b)

noncomputable def theta [DecidableEq K] [TopologicalSpace K] (ρ : G →* PGL(2, K₀)) (a b z₀ : K) (z : K) : K :=
  ∏' γ : G, thetaFactor ρ a b z₀ z γ

def ThetaMultipliable [DecidableEq K] [TopologicalSpace K] (ρ : G →* PGL(2, K₀)) (a b z₀ z : K) : Prop :=
  Multipliable (thetaFactor ρ a b z₀ z)

def IsAutomorphicWithMultiplier [DecidableEq K] (ρ : G →* PGL(2, K₀)) (Ω : Set K) (f : K → K) (c : G →* Kˣ) : Prop :=
  ∀ γ : G, ∀ z ∈ Ω, f (pmoebius K₀ (ρ γ) z) = (c γ : K) * f z

def IsInvariant [DecidableEq K] (ρ : G →* PGL(2, K₀)) (Ω : Set K) (f : K → K) : Prop :=
  IsAutomorphicWithMultiplier ρ Ω f 1

noncomputable def period [DecidableEq K] [TopologicalSpace K] (ρ : G →* PGL(2, K₀)) (a z₀ : K) (α β : G) : K :=
  theta ρ a (pmoebius K₀ (ρ α) a) z₀ (pmoebius K₀ (ρ β) z₀)

end Theta

end Omega

end CerednikDrinfeld
