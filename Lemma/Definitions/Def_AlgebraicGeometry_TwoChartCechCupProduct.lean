import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option autoImplicit false

noncomputable section

universe u v w

namespace TwoChartCech

namespace Sections

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} (S : Sections.{u, v, w} 𝒰)

theorem smul_r0_mem_range_cechDiff (x : S.H0) {f : 𝒰.A01}
    (hf : f ∈ LinearMap.range 𝒰.structureSheaf.cechDiff) :
    f • S.r0 x.val.1 ∈ LinearMap.range S.cechDiff := by
  obtain ⟨s, rfl⟩ := hf
  have hx : S.r0 x.val.1 = S.r1 x.val.2 := (S.mem_H0_iff _).mp x.2
  refine ⟨(s.1 • x.val.1, s.2 • x.val.2), ?_⟩
  rw [Sections.cechDiff_apply, Sections.cechDiff_apply, S.r0_smul, S.r1_smul, hx,
    Cover.lineBundle_r1_apply, Cover.lineBundle_r0_apply, Units.val_one, one_mul, sub_smul]

def cupProductFun (x : S.H0) : 𝒰.structureSheaf.H1 →ₗ[R] S.H1 :=
  (LinearMap.range 𝒰.structureSheaf.cechDiff).liftQ
    ((LinearMap.range S.cechDiff).mkQ ∘ₗ
      (LinearMap.toSpanSingleton 𝒰.A01 S.M01 (S.r0 x.val.1)).restrictScalars R)
    (fun f hf => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact S.smul_r0_mem_range_cechDiff x hf)

theorem cupProductFun_mk (x : S.H0) (f : 𝒰.A01) :
    S.cupProductFun x (Submodule.Quotient.mk f) = Submodule.Quotient.mk (f • S.r0 x.val.1) := rfl

def cupProduct : S.H0 →ₗ[R] 𝒰.structureSheaf.H1 →ₗ[R] S.H1 where
  toFun := S.cupProductFun
  map_add' x y := by
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H f =>
      rw [LinearMap.add_apply, cupProductFun_mk, cupProductFun_mk, cupProductFun_mk, Submodule.coe_add,
        Prod.fst_add, map_add, smul_add, Submodule.Quotient.mk_add]
  map_smul' r x := by
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H f =>
      rw [LinearMap.smul_apply, RingHom.id_apply, cupProductFun_mk, cupProductFun_mk, Submodule.coe_smul,
        Prod.smul_fst, LinearMap.map_smul, smul_comm (f : 𝒰.A01) r, Submodule.Quotient.mk_smul]

@[simp] theorem cupProduct_apply_mk (x : S.H0) (f : 𝒰.A01) :
    S.cupProduct x (Submodule.Quotient.mk f) = Submodule.Quotient.mk (f • S.r0 x.val.1) := rfl

theorem cupProduct_apply_mk' (x : S.H0) (f : 𝒰.A01) :
    S.cupProduct x (Submodule.Quotient.mk f) = Submodule.Quotient.mk (f • S.r1 x.val.2) := by
  rw [cupProduct_apply_mk, (S.mem_H0_iff _).mp x.2]

def traceForm (t : S.M01 →ₗ[R] R) (ht : LinearMap.range S.cechDiff ≤ LinearMap.ker t) : S.H1 →ₗ[R] R :=
  (LinearMap.range S.cechDiff).liftQ t ht

@[simp] theorem traceForm_mk (t : S.M01 →ₗ[R] R) (ht : LinearMap.range S.cechDiff ≤ LinearMap.ker t)
    (m : S.M01) : S.traceForm t ht (Submodule.Quotient.mk m) = t m := rfl

def tracePairing (t : S.M01 →ₗ[R] R) (ht : LinearMap.range S.cechDiff ≤ LinearMap.ker t) :
    S.H0 →ₗ[R] 𝒰.structureSheaf.H1 →ₗ[R] R :=
  S.cupProduct.compr₂ (S.traceForm t ht)

@[simp] theorem tracePairing_apply_mk (t : S.M01 →ₗ[R] R) (ht : LinearMap.range S.cechDiff ≤ LinearMap.ker t)
    (x : S.H0) (f : 𝒰.A01) :
    S.tracePairing t ht x (Submodule.Quotient.mk f) = t (f • S.r0 x.val.1) := rfl

end Sections

end TwoChartCech

end
