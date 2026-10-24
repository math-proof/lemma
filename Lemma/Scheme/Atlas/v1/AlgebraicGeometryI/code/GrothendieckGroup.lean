import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.GrothendieckGroup
open CategoryTheory DegreeAdditivity


namespace DegreeAdditivity

/--
[GrothendieckGroupK0.ses_relation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckGroup.lean)
-/
@[path]
lemma GrothendieckGroupK0.ses_relation
  {R : Type u}
  [Ring R]
  {A B C : ModuleCat.{u} R}
  {f : A →ₗ[R] B}
  {g : B →ₗ[R] C}
-- given
  (hf : Function.Injective f)
  (hg : Function.Surjective g)
  (hex : Function.Exact f g) :
-- imply
  GrothendieckGroupK0.classOf R B = GrothendieckGroupK0.classOf R A + GrothendieckGroupK0.classOf R C := by
-- proof
  unfold GrothendieckGroupK0.classOf
  rw [← QuotientAddGroup.mk_add]
  apply QuotientAddGroup.eq.mpr
  have hmem : FreeAbelianGroup.of B - FreeAbelianGroup.of A -
    FreeAbelianGroup.of C ∈ K0SESRelSubgroup R :=
    AddSubgroup.subset_closure ⟨A, B, C, f, g, hf, hg, hex, rfl⟩
  have : -FreeAbelianGroup.of B + (FreeAbelianGroup.of A + FreeAbelianGroup.of C) =
    -(FreeAbelianGroup.of B - FreeAbelianGroup.of A - FreeAbelianGroup.of C) := by
    simp [sub_eq_add_neg]; abel
  rw [this]
  exact (K0SESRelSubgroup R).neg_mem hmem

end DegreeAdditivity

namespace DegreeAdditivity

/--
[GrothendieckGroupK0.classOf_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckGroup.lean)
-/
@[path]
lemma GrothendieckGroupK0.classOf_zero
  {R : Type u}
  [Ring R] :
-- imply
  GrothendieckGroupK0.classOf R (ModuleCat.of R PUnit.{u+1}) = 0 := by
-- proof
  set a := GrothendieckGroupK0.classOf R (ModuleCat.of R PUnit.{u+1})
  have hses : a = a + a :=
    GrothendieckGroupK0.ses_relation R
      (0 : PUnit.{u+1} →ₗ[R] PUnit.{u+1}) (0 : PUnit.{u+1} →ₗ[R] PUnit.{u+1})
      (fun ⟨⟩ ⟨⟩ _ => rfl) (fun ⟨⟩ => ⟨PUnit.unit, rfl⟩) (by intro x; simp)
  rwa [eq_comm, add_eq_left] at hses

end DegreeAdditivity

namespace DegreeAdditivity

/--
[GrothendieckGroupK0.classOf_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckGroup.lean)
-/
@[path]
lemma GrothendieckGroupK0.classOf_prod
  {R : Type u}
  [Ring R]
  {M N : ModuleCat.{u} R} :
-- imply
  GrothendieckGroupK0.classOf R (ModuleCat.of R (M × N)) = GrothendieckGroupK0.classOf R M + GrothendieckGroupK0.classOf R N :=
-- proof
  GrothendieckGroupK0.ses_relation R
    (LinearMap.inl R M N) (LinearMap.snd R M N)
    LinearMap.inl_injective LinearMap.snd_surjective Function.Exact.inl_snd

end DegreeAdditivity

namespace DegreeAdditivity

/--
[GrothendieckGroupK0.classOf_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckGroup.lean)
-/
@[path]
lemma GrothendieckGroupK0.classOf_iso
  {R : Type u}
  [Ring R]
  {M N : ModuleCat.{u} R}
  {e : M ≃ₗ[R] N} :
-- imply
  GrothendieckGroupK0.classOf R M = GrothendieckGroupK0.classOf R N := by
-- proof
  have h := GrothendieckGroupK0.ses_relation R (C := ModuleCat.of R PUnit.{u+1})
    (e : M →ₗ[R] N) (0 : N →ₗ[R] PUnit.{u+1})
    e.injective (fun ⟨⟩ => ⟨0, rfl⟩) (by intro x; simp)
  rwa [GrothendieckGroupK0.classOf_zero R, add_zero] at h

end DegreeAdditivity

namespace DegreeAdditivity

/--
[GrothendieckGroupK0.lift_classOf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckGroup.lean)
-/
@[path]
lemma GrothendieckGroupK0.lift_classOf
  {R : Type u}
  [Ring R]
  [AddCommGroup G]
  {φ : ModuleCat.{u} R → G}
  {M : ModuleCat.{u} R}
-- given
  (hφ : IsSESAdditive R φ) :
-- imply
  GrothendieckGroupK0.lift R φ hφ (GrothendieckGroupK0.classOf R M) = φ M := by
-- proof
  unfold GrothendieckGroupK0.lift GrothendieckGroupK0.classOf
  rw [QuotientAddGroup.lift_mk', FreeAbelianGroup.lift_apply_of]

end DegreeAdditivity

namespace DegreeAdditivity

/--
[GrothendieckGroupK0.lift_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckGroup.lean)
-/
@[path]
lemma GrothendieckGroupK0.lift_unique
  {R : Type u}
  [Ring R]
  [AddCommGroup G]
  {ψ₁ ψ₂ : GrothendieckGroupK0 R →+ G}
-- given
  (h : ∀ M : ModuleCat.{u} R, ψ₁ (GrothendieckGroupK0.classOf R M) = ψ₂ (GrothendieckGroupK0.classOf R M)) :
-- imply
  ψ₁ = ψ₂ := by
-- proof
  have hsuff : ψ₁.comp (QuotientAddGroup.mk' (K0SESRelSubgroup R)) =
    ψ₂.comp (QuotientAddGroup.mk' (K0SESRelSubgroup R)) := by
    rw [← FreeAbelianGroup.lift.apply_symm_apply (ψ₁.comp (QuotientAddGroup.mk' _)),
      ← FreeAbelianGroup.lift.apply_symm_apply (ψ₂.comp (QuotientAddGroup.mk' _))]
    congr 1
    ext M
    have h1 := FreeAbelianGroup.lift_apply_of
      (FreeAbelianGroup.lift.symm (ψ₁.comp (QuotientAddGroup.mk' (K0SESRelSubgroup R)))) M
    have h2 := FreeAbelianGroup.lift_apply_of
      (FreeAbelianGroup.lift.symm (ψ₂.comp (QuotientAddGroup.mk' (K0SESRelSubgroup R)))) M
    rw [Equiv.apply_symm_apply] at h1 h2
    simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply] at h1 h2
    rw [← h1, ← h2]
    exact h M
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (K0SESRelSubgroup R) x
  exact DFunLike.congr_fun hsuff y
end DegreeAdditivity


/--
[K0SESRelSubgroup_le_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckGroup.lean)
-/
@[path]
private lemma K0SESRelSubgroup_le_ker_eq
  {R : Type u}
  [Ring R]
  [AddCommGroup G]
  {φ : ModuleCat.{u} R → G}
-- given
  (hφ : IsSESAdditive R φ) :
-- imply
  K0SESRelSubgroup R ≤ (FreeAbelianGroup.lift φ).ker := by
-- proof
  apply DegreeAdditivity.K0SESRelSubgroup_le_ker R φ hφ


-- created on 2026-10-23
