import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Module.Projective

set_option autoImplicit false

noncomputable section

universe u v w w'

namespace TwoChartCech

namespace KerCoprod

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable {P : Type w'} [AddCommGroup P] [Module R P]
variable (d : C0 →ₗ[R] C1) (g : P →ₗ[R] C1)

abbrev K0 : Submodule R (C0 × P) := LinearMap.ker (d.coprod g)

theorem mem_K0_iff (z : C0 × P) : z ∈ K0 d g ↔ d z.1 + g z.2 = 0 := by
  rw [LinearMap.mem_ker, LinearMap.coprod_apply]

def dK : K0 d g →ₗ[R] P := (LinearMap.snd R C0 P) ∘ₗ (K0 d g).subtype

def ι0 : K0 d g →ₗ[R] C0 := (LinearMap.fst R C0 P) ∘ₗ (K0 d g).subtype

def ι1 : P →ₗ[R] C1 := -g

@[simp] theorem dK_apply (z : K0 d g) : dK d g z = (z : C0 × P).2 := rfl
@[simp] theorem ι0_apply (z : K0 d g) : ι0 d g z = (z : C0 × P).1 := rfl
@[simp] theorem ι1_apply (p : P) : ι1 g p = -g p := rfl
theorem ι1_eq : ι1 g = -g := rfl

theorem comm : d ∘ₗ ι0 d g = ι1 g ∘ₗ dK d g := by
  ext z
  have hz : d (z : C0 × P).1 + g (z : C0 × P).2 = 0 := (mem_K0_iff d g _).mp z.2
  simp only [LinearMap.comp_apply, ι0_apply, dK_apply, ι1_apply, eq_neg_iff_add_eq_zero]
  exact hz

theorem ι0_prod_dK : (ι0 d g).prod (dK d g) = (K0 d g).subtype := by
  ext z <;> rfl

end KerCoprod

namespace Mumford

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

def rank : ℕ := (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose

def quot : (Fin (rank d) → R) →ₗ[R] (C1 ⧸ LinearMap.range d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose

theorem quot_surjective : Function.Surjective (quot d) :=
  (Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)).choose_spec.choose_spec

def lift : (Fin (rank d) → R) →ₗ[R] C1 :=
  (Module.projective_lifting_property (LinearMap.range d).mkQ (quot d)
    (LinearMap.range d).mkQ_surjective).choose

theorem mkQ_comp_lift : (LinearMap.range d).mkQ ∘ₗ lift d = quot d :=
  (Module.projective_lifting_property (LinearMap.range d).mkQ (quot d)
    (LinearMap.range d).mkQ_surjective).choose_spec

theorem mkQ_lift_apply (v : Fin (rank d) → R) : (LinearMap.range d).mkQ (lift d v) = quot d v := by
  rw [← LinearMap.comp_apply, mkQ_comp_lift]

theorem surjective_coprod : Function.Surjective (d.coprod (lift d)) := by
  intro y
  obtain ⟨v, hv⟩ := quot_surjective d ((LinearMap.range d).mkQ y)
  have hy : y - lift d v ∈ LinearMap.range d := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, ← hv, mkQ_lift_apply, sub_self]
  obtain ⟨x, hx⟩ := hy
  exact ⟨(x, v), by simp only [LinearMap.coprod_apply, hx, sub_add_cancel]⟩

abbrev K0 : Submodule R (C0 × (Fin (rank d) → R)) := KerCoprod.K0 d (lift d)

theorem mem_K0_iff (z : C0 × (Fin (rank d) → R)) : z ∈ K0 d ↔ d z.1 + lift d z.2 = 0 :=
  KerCoprod.mem_K0_iff d (lift d) z

abbrev dK : K0 d →ₗ[R] (Fin (rank d) → R) := KerCoprod.dK d (lift d)

abbrev ι0 : K0 d →ₗ[R] C0 := KerCoprod.ι0 d (lift d)

abbrev ι1 : (Fin (rank d) → R) →ₗ[R] C1 := KerCoprod.ι1 (lift d)

@[simp] theorem dK_apply (z : K0 d) : dK d z = (z : C0 × (Fin (rank d) → R)).2 := rfl
@[simp] theorem ι0_apply (z : K0 d) : ι0 d z = (z : C0 × (Fin (rank d) → R)).1 := rfl
@[simp] theorem ι1_apply (v : Fin (rank d) → R) : ι1 d v = -lift d v := rfl
theorem ι1_eq : ι1 d = -lift d := rfl

theorem comm : d ∘ₗ ι0 d = ι1 d ∘ₗ dK d := KerCoprod.comm d (lift d)

theorem ι0_prod_dK : (ι0 d).prod (dK d) = (K0 d).subtype := KerCoprod.ι0_prod_dK d (lift d)

end Mumford

section Gates

example (x : ℤ) (v : Fin (Mumford.rank (0 : ℤ →ₗ[ℤ] ℤ)) → ℤ) :
    (x, v) ∈ Mumford.K0 (0 : ℤ →ₗ[ℤ] ℤ) ↔ Mumford.lift (0 : ℤ →ₗ[ℤ] ℤ) v = 0 := by
  rw [Mumford.mem_K0_iff, LinearMap.zero_apply, zero_add]

example (v : Fin (Mumford.rank (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) → ℤ) :
    (-(Mumford.lift (LinearMap.id : ℤ →ₗ[ℤ] ℤ) v), v) ∈ Mumford.K0 (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  rw [Mumford.mem_K0_iff, LinearMap.id_apply, neg_add_cancel]

example (R : Type u) [CommRing R] :
    (0 : R →ₗ[R] R) ∘ₗ Mumford.ι0 (0 : R →ₗ[R] R) = Mumford.ι1 (0 : R →ₗ[R] R) ∘ₗ Mumford.dK (0 : R →ₗ[R] R) :=
  Mumford.comm 0

example (R : Type u) [CommRing R] (d : R →ₗ[R] R) (x : R) (p : PUnit.{u + 1}) :
    (x, p) ∈ KerCoprod.K0 d (0 : PUnit →ₗ[R] R) ↔ d x = 0 := by
  rw [KerCoprod.mem_K0_iff, LinearMap.zero_apply, add_zero]

end Gates

end TwoChartCech

end
