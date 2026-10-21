import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

private lemma rangeRestrict_comp_ker_subtype
  {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N) :
  -- imply
  f.rangeRestrict.comp (LinearMap.ker f).subtype = 0 := by
  -- proof
  refine LinearMap.ext fun x => Subtype.ext ?_
  change f x = 0
  apply x.2

private lemma subtype_comp_rangeRestrict
  {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N) :
  -- imply
  (LinearMap.range f).subtype.comp f.rangeRestrict = f :=
  LinearMap.ext fun _ => rfl

private lemma lTensor_subtype_range_injective
  {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  (A : Type*) [CommRing A] [Algebra R A]
  (f : M →ₗ[R] N)
  -- given
  (h : LinearMap.ker (f.baseChange A) ≤ LinearMap.range ((LinearMap.ker f).subtype.baseChange A)) :
  -- imply
  Function.Injective ((LinearMap.range f).subtype.lTensor A) := by
  -- proof
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have hsurj : Function.Surjective (f.rangeRestrict.lTensor A) :=
    LinearMap.lTensor_surjective A (LinearMap.surjective_rangeRestrict f)
  obtain ⟨y, rfl⟩ := hsurj x
  have hy : y ∈ LinearMap.ker (f.baseChange A) := by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, subtype_comp_rangeRestrict] at hx
    apply hx
  obtain ⟨z, hz⟩ := h hy
  rw [Submodule.mem_bot, ← hz]
  change f.rangeRestrict.lTensor A ((LinearMap.ker f).subtype.lTensor A z) = 0
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, rangeRestrict_comp_ker_subtype,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

private lemma free_quotient_range
  {R : Type u} [CommRing R] [IsLocalRing R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
  {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N]
  (f : M →ₗ[R] N)
  -- given
  (h : LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R)) ≤
    LinearMap.range ((LinearMap.ker f).subtype.baseChange (IsLocalRing.ResidueField R))) :
  -- imply
  Module.Free R (N ⧸ LinearMap.range f) :=
  Module.free_of_lTensor_residueField_injective (LinearMap.range f).subtype
    (LinearMap.range f).mkQ (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
    (lTensor_subtype_range_injective (IsLocalRing.ResidueField R) f h)

/--
[Module_free_quotient_range_of_ker_baseChange_residueField_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_free_quotient_range_of_ker_baseChange_residueField_le.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsLocalRing R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
  {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N]
  (f : M →ₗ[R] N)
  -- given
  (h : LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R)) ≤
    LinearMap.range ((LinearMap.ker f).subtype.baseChange (IsLocalRing.ResidueField R))) :
  -- imply
  Module.Free R (N ⧸ LinearMap.range f) :=
  free_quotient_range f h


-- created on 2026-10-20
