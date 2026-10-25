import Mathlib
import Instance.AlgebraicCurve_PlaceCompletion

@[simps!]
def Units.mapₜ {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (f : M →ₜ* N) : Mˣ →ₜ* Nˣ :=
  ⟨Units.map f,
  continuous_induced_rng.mpr (continuous_prodMk.mpr ⟨f.2.comp Units.continuous_val,
    MulOpposite.continuous_op.comp (f.2.comp Units.continuous_coe_inv)⟩)⟩

@[simps!]
def ContinuousAlgHom.mapMatrix
    {R A B n : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B)
    [Fintype n] [DecidableEq n] :
    Matrix n n A →A[R] Matrix n n B :=
  ⟨f.1.mapMatrix, Continuous.matrix_map continuous_id' f.2⟩

def ContinuousAlgHom.toContinuousMonoidHom
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B) : A →ₜ* B :=
  ⟨f.1.toMonoidHom, f.2⟩


def AlgebraicClosure.map {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    AlgebraicClosure K →+* AlgebraicClosure L :=
  letI := f.toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toRingHom


def Module.endSelf {A : Type*} [CommSemiring A] : Module.End A A ≃ₐ[A] A :=
  AlgEquiv.ofLinearEquiv (LinearMap.ringLmapEquivSelf A A A) (by simp) (by simp)

@[simps!]
def ContinuousMonoidHom.toHomUnits {G M : Type*} [Group G] [Monoid M] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace M] (f : G →ₜ* M) : G →ₜ* Mˣ :=
  ⟨MonoidHom.toHomUnits f, continuous_induced_rng.mpr (continuous_prodMk.mpr ⟨f.continuous, by
    exact MulOpposite.continuous_op.comp (f.continuous.comp continuous_inv)⟩)⟩

@[simps!]
def Units.coeHomₜ (M : Type*) [Monoid M] [TopologicalSpace M] : Mˣ →ₜ* M :=
  ⟨coeHom M, Units.continuous_val⟩


def ContinuousAlgEquiv.ofIsModuleTopology {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace R] [IsModuleTopology R A] [IsModuleTopology R B] (e : A ≃ₐ[R] B) :
    A ≃A[R] B where
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd R B
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd R A
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
