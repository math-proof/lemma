import Mathlib
import sympy.Basic

open AlgHom

/--
[AlgHom_eq_of_forall_comp_eq_of_injective_lift_pi](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_eq_of_forall_comp_eq_of_injective_lift_pi.lean)
-/

private lemma lift_includeRight
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  {A : Type*}
  [CommRing A]
  [Algebra K A]
  {P : Type*}
  (pt : P → AlgHom K A L)
  (a : A) :
  (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (AlgHom.pi (fun p : P => pt p))
      (fun _ _ => Commute.all _ _)) (Algebra.TensorProduct.includeRight a) = fun p => pt p a := by
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

private lemma eq_of_forall_apply_eq
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  {A : Type*}
  [CommRing A]
  [Algebra K A]
  {P : Type*}
  (pt : P → AlgHom K A L)
  (hinj : Function.Injective (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (AlgHom.pi (fun p : P => pt p)) (fun _ _ => Commute.all _ _)))
  {a a' : A}
  (h : ∀ p : P, pt p a = pt p a') :
  a = a' := by
  apply Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  apply hinj
  rw [lift_includeRight, lift_includeRight]
  funext p
  exact h p

@[path]
private lemma main
  {K L : Type} [Field K] [Field L] [Algebra K L]
  {A : Type} [CommRing A] [Algebra K A]
  {P B : Type} [Semiring B] [Algebra K B]
  {pt : P → AlgHom K A L}
  {u u' : AlgHom K B A}
-- given
  (hinj : Function.Injective (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (AlgHom.pi (fun p : P => pt p)) (fun _ _ => Commute.all _ _)))
  (h : ∀ p : P, (pt p).comp u = (pt p).comp u') :
-- imply
  u = u' := by
-- proof
  apply AlgHom.ext
  intro b
  exact eq_of_forall_apply_eq pt hinj fun p => DFunLike.congr_fun (h p) b


-- created on 2026-10-09
