import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_FLTPrelim_GaloisRep
import Lemma.Int.P2MUtil
open Int
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point


/-- ported from external source -/
@[path]
private lemma main
  [Field F] [Field K] [Algebra F K] [DecidableEq K]
  {E₁ E₂ : WeierstrassCurve F}
  {n : ℕ}
-- given
  (e : (E₁⁄K).Point ≃+ (E₂⁄K).Point)
  (he : ∀ (σ : K ≃ₐ[F] K) (P : (E₁⁄K).Point), e (σ • P) = σ • e P) :
-- imply
  ∃ φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n,
    (∀ x : Submodule.torsionBy ℤ (E₁⁄K).Point n, (φ x : (E₂⁄K).Point) = e x) ∧
      ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n), φ (σ • x) = σ • φ x := by
-- proof
  let torsionByMap (f : (E₁⁄K).Point →+ (E₂⁄K).Point) :
      Submodule.torsionBy ℤ (E₁⁄K).Point n →+ Submodule.torsionBy ℤ (E₂⁄K).Point n :=
    { toFun := fun x => ⟨f x, by
        rw [Submodule.mem_torsionBy_iff, ← f.map_zsmul, (Submodule.mem_torsionBy_iff _ _).mp x.2,
          f.map_zero]⟩
      map_zero' := Subtype.ext f.map_zero
      map_add' := fun x y => Subtype.ext (f.map_add x y) }
  let torsionByMap_symm (f : (E₂⁄K).Point →+ (E₁⁄K).Point) :
      Submodule.torsionBy ℤ (E₂⁄K).Point n →+ Submodule.torsionBy ℤ (E₁⁄K).Point n :=
    { toFun := fun x => ⟨f x, by
        rw [Submodule.mem_torsionBy_iff, ← f.map_zsmul, (Submodule.mem_torsionBy_iff _ _).mp x.2,
          f.map_zero]⟩
      map_zero' := Subtype.ext f.map_zero
      map_add' := fun x y => Subtype.ext (f.map_add x y) }
  let φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n :=
    LinearEquiv.mk ((torsionByMap e.toAddMonoidHom).toZModLinearMap n)
      (torsionByMap_symm e.symm.toAddMonoidHom)
      (fun x => Subtype.ext (e.symm_apply_apply x))
      (fun y => Subtype.ext (e.apply_symm_apply y))
  refine ⟨φ, ?_, ?_⟩
  ·
    intro x
    rfl
  ·
    intro σ x
    exact Subtype.ext (he σ x)


-- created on 2026-10-24
