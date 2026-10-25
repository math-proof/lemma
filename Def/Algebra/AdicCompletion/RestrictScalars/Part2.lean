import Mathlib.RingTheory.AdicCompletion.Algebra
import Theorem.Algebra.AdicCompletion.RestrictScalars.Part2
universe u₁ u₂


namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

noncomputable def restrictScalarsEquiv :
    AdicCompletion (𝔭.map (algebraMap A B)) B ≃ₗ[A] AdicCompletion 𝔭 B where
  toFun x := ⟨fun n => levelRestrictScalarsEquiv B 𝔭 n (x.val n), fun {m n} hmn => by
    show transitionMap 𝔭 B hmn (levelRestrictScalarsEquiv B 𝔭 n (x.val n)) =
      levelRestrictScalarsEquiv B 𝔭 m (x.val m)
    rw [← x.prop hmn]
    exact transitionMap_levelRestrictScalarsEquiv B 𝔭 hmn (x.val n)⟩
  invFun y := ⟨fun n => (levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n), fun {m n} hmn => by
    show transitionMap (𝔭.map (algebraMap A B)) B hmn
        ((levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n)) =
      (levelRestrictScalarsEquiv B 𝔭 m).symm (y.val m)
    rw [← y.prop hmn, LinearEquiv.eq_symm_apply,
      ← transitionMap_levelRestrictScalarsEquiv B 𝔭 hmn
        ((levelRestrictScalarsEquiv B 𝔭 n).symm (y.val n)),
      LinearEquiv.apply_symm_apply]⟩
  map_add' x y := by
    ext n
    exact map_add (levelRestrictScalarsEquiv B 𝔭 n) _ _
  map_smul' a x := by
    ext n
    exact map_smul (levelRestrictScalarsEquiv B 𝔭 n) a _
  left_inv x := by
    ext n
    exact (levelRestrictScalarsEquiv B 𝔭 n).symm_apply_apply _
  right_inv y := by
    ext n
    exact (levelRestrictScalarsEquiv B 𝔭 n).apply_symm_apply _

end AdicCompletion
