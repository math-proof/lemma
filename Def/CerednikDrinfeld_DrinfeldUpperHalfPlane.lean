import Mathlib

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

noncomputable scoped instance (priority := low) glAction [DecidableEq K] :
    MulAction (GL (Fin 2) K₀) (OnePoint K) :=
  MulAction.compHom (OnePoint K) (Matrix.GeneralLinearGroup.map (algebraMap K₀ K))

theorem gl_smul_def [DecidableEq K] (g : GL (Fin 2) K₀) (x : OnePoint K) :
    g • x = (Matrix.GeneralLinearGroup.map (algebraMap K₀ K) g) • x := rfl

theorem scalar_smul_eq [DecidableEq K] (u : K₀ˣ) (x : OnePoint K) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀) • x = x := by
  have h10 : (Matrix.GeneralLinearGroup.map (algebraMap K₀ K)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀)) 1 0 = 0 := by
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [Matrix.GeneralLinearGroup.scalar]
  have h00 : (Matrix.GeneralLinearGroup.map (algebraMap K₀ K)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀)) 0 0 = algebraMap K₀ K (u : K₀) := by
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [Matrix.GeneralLinearGroup.scalar]
  have h11 : (Matrix.GeneralLinearGroup.map (algebraMap K₀ K)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀)) 1 1 = algebraMap K₀ K (u : K₀) := by
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [Matrix.GeneralLinearGroup.scalar]
  have h01 : (Matrix.GeneralLinearGroup.map (algebraMap K₀ K)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) K₀)) 0 1 = 0 := by
    rw [Matrix.GeneralLinearGroup.map_apply]
    simp [Matrix.GeneralLinearGroup.scalar]
  have hu : algebraMap K₀ K (u : K₀) ≠ 0 := by
    simp
  induction x using OnePoint.rec with
  | infty => rw [gl_smul_def, OnePoint.smul_infty_eq_ite, if_pos h10]
  | coe k =>
    rw [gl_smul_def, OnePoint.smul_some_eq_ite, h10, h11, h00, h01, zero_mul, zero_add, if_neg hu, add_zero,
      mul_div_cancel_left₀ _ hu]

noncomputable scoped instance (priority := low) pglAction [DecidableEq K] :
    MulAction PGL(2, K₀) (OnePoint K) :=
  Matrix.ProjGenLinGroup.mulActionOfGL (fun u x => scalar_smul_eq K₀ K u x)

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
