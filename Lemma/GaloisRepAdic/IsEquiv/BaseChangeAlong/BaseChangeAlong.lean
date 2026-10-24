import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GaloisRep_Adic
import Lemma.Int.P2MUtil

open scoped TensorProduct

/--
[GaloisRepAdic_isEquiv_baseChangeAlong_baseChangeAlong](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_isEquiv_baseChangeAlong_baseChangeAlong.lean)
-/

private lemma  aux
    {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : C ⊗[B] (B ⊗[A] ρ.V)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
        (LinearMap.baseChange C (LinearMap.baseChange B (ρ.ρ σ)) x) =
      LinearMap.baseChange C (ρ.ρ σ) (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a y =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | tmul b v =>
      simp only [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
@[path]
private lemma main
  [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
  {f : A →+* B}
  {g : B →+* C}
  {ρ : GaloisRepAdic A}
-- given
  (hf : IsLocalHom f)
  (hg : IsLocalHom g) :
-- imply
  ((ρ.baseChangeAlong f hf).baseChangeAlong g hg).IsEquiv
      (ρ.baseChangeAlong (g.comp f) (RingHom.isLocalHom_comp g f)) := by
-- proof
  classical
    let : Algebra A B := f.toAlgebra
    let : Algebra B C := g.toAlgebra
    let : Algebra A C := (g.comp f).toAlgebra
    have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    refine ⟨{ toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
              map_apply := ?_ }⟩
    intro σ x
    exact aux ρ σ x


-- created on 2026-10-23
