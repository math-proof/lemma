import Mathlib
import sympy.Basic
open TensorProduct


universe u v w

private lemma exists_forall_pow_smul_eq_zero_of_isNoetherian
  {B : Type u} [CommRing B] [IsNoetherianRing B]
  {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
  {t : B} :
-- imply
  ∃ e : ℕ, ∀ x : M, (∃ k : ℕ, t ^ k • x = 0) → t ^ e • x = 0 := by
-- proof
  let hN : _root_.IsNoetherian B M := isNoetherian_of_isNoetherianRing_of_finite B M
  let F : OrderHom ℕ (Submodule B M) :=
    { toFun := fun k => Submodule.torsionBy B M (t ^ k)
      monotone' := fun k l hkl x hx => by
        rw [Submodule.mem_torsionBy_iff] at hx ⊢
        rw [← Nat.sub_add_cancel hkl, pow_add, mul_smul, hx, smul_zero] }
  obtain ⟨e, he⟩ := (monotone_stabilizes_iff_noetherian.2 hN) F
  refine ⟨e, fun x ⟨k, hk⟩ => ?_⟩
  have hx : x ∈ F (max k e) := F.monotone (le_max_left k e) ((Submodule.mem_torsionBy_iff _ _).2 hk)
  rw [← he (max k e) (le_max_right k e)] at hx
  apply (Submodule.mem_torsionBy_iff _ _).1 hx

/--
[AlgebraicGeometry_AdmissibleAlgebra_exists_forall_cocycle_pow_smul_eq_coboundary](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_cocycle_pow_smul_eq_coboundary.lean)
-/
@[path]
private lemma main
  {B : Type u} [CommRing B] [IsNoetherianRing B]
  {R : Type v} [CommRing R] [Algebra B R] [Module.Finite B R]
  {G : Type w} [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G B R]
  {t : B} :
-- imply
  ∃ e : ℕ, ∀ y : G → R, (∀ g h : G, y (g * h) = g • y h + y g) →
    (∃ (k : ℕ) (z : R), ∀ g : G, t ^ k • y g = g • z - z) → ∃ z : R, ∀ g : G, t ^ e • y g = g • z - z := by
-- proof
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let d : R →ₗ[B] (G → R) :=
    { toFun := fun z g => g • z - z
      map_add' := fun z z' => funext fun g => by
        show g • (z + z') - (z + z') = (g • z - z) + (g • z' - z')
        rw [smul_add]; abel
      map_smul' := fun b z => funext fun g => by
        show g • (b • z) - b • z = b • (g • z - z)
        rw [smul_sub, smul_comm] }
  obtain ⟨e, he⟩ := exists_forall_pow_smul_eq_zero_of_isNoetherian (M := (G → R) ⧸ LinearMap.range d) (t := t)
  refine ⟨e, fun y _ ⟨k, z, hz⟩ => ?_⟩
  have hk : t ^ k • Submodule.Quotient.mk (p := LinearMap.range d) y = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    apply LinearMap.mem_range.2 ⟨z, funext fun g => by show g • z - z = t ^ k • y g; exact (hz g).symm⟩
  have := he _ ⟨k, hk⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  obtain ⟨z', hz'⟩ := LinearMap.mem_range.1 this
  exact ⟨z', fun g => by have := congrFun hz' g; exact this.symm⟩


-- created on 2026-10-20
