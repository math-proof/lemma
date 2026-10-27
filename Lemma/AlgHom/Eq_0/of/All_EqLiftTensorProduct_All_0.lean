import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


/--
[Algebra_TensorProduct_eq_zero_of_forall_lift_apply_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_eq_zero_of_forall_lift_apply_eq_zero.lean)
-/
@[path]
private lemma main
  [Field K] [Field L] [Algebra K L]
  [CommRing A] [Algebra K A] [Module.Finite K A]
  {pt : P → (A →ₐ[K] L)}
  {x : A ⊗[K] A}
-- given
  (hinj : Function.Injective
    (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (AlgHom.pi fun p : P => pt p)
      (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
  (hx : ∀ p q : P, Algebra.TensorProduct.lift (pt p) (pt q) (fun _ _ => Commute.all _ _) x = 0) :
-- imply
  x = 0 := by
-- proof
  classical
  set ev := (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (AlgHom.pi fun p : P => pt p)
    (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)) with hev
  let b := Module.Free.chooseBasis K A
  let f : Module.Free.ChooseBasisIndex K A → (P → L) := fun i p => pt p (b i)
  have hevB : ∀ i, ev (Algebra.TensorProduct.basis L b i) = f i := by
    intro i
    rw [Algebra.TensorProduct.basis_apply, hev, Algebra.TensorProduct.lift_tmul]
    ext p
    simp [f, Algebra.ofId_apply]
  have hli : LinearIndependent L f := by
    have h := (Algebra.TensorProduct.basis L b).linearIndependent.map' ev.toLinearMap
      (LinearMap.ker_eq_bot.mpr hinj)
    convert h using 1
    ext i p
    simp [Function.comp_apply]
    rw [← hevB, Algebra.TensorProduct.basis_apply]
  set T := b.tensorProduct b with hT
  set c := T.repr x with hc
  have hxsum : x = ∑ ij, c ij • (b ij.1 ⊗ₜ[K] b ij.2) := by
    conv_lhs => rw [← T.sum_repr x]
    refine Finset.sum_congr rfl fun ij _ => ?_
    obtain ⟨i, j⟩ := ij
    rw [hT, Module.Basis.tensorProduct_apply]
  have hsum : ∀ p q : P, ∑ ij : Module.Free.ChooseBasisIndex K A × Module.Free.ChooseBasisIndex K A,
      algebraMap K L (c ij) * (pt p (b ij.1) * pt q (b ij.2)) = 0 := by
    intro p q
    have h := hx p q
    rw [hxsum, map_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [map_smul, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  have hd : ∀ (q : P) (i : Module.Free.ChooseBasisIndex K A),
      ∑ j, algebraMap K L (c (i, j)) * pt q (b j) = 0 := by
    intro q
    apply (Fintype.linearIndependent_iff.mp hli)
    ext p
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f]
    rw [← hsum p q, Fintype.sum_prod_type]
    simp [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hcz : ∀ ij : Module.Free.ChooseBasisIndex K A × Module.Free.ChooseBasisIndex K A, c ij = 0 := by
    intro ij
    obtain ⟨i, j⟩ := ij
    have hrel : ∑ j', (algebraMap K L (c (i, j'))) • f j' = 0 := by
      ext q
      simp [Finset.sum_apply, Algebra.smul_def, f]
      apply hd q i
    have := (Fintype.linearIndependent_iff.mp hli) _ hrel j
    apply (map_eq_zero_iff _ (algebraMap K L).injective).mp this
  have : c = 0 := by
    ext ij
    apply hcz
  rw [hc] at this
  apply (LinearEquiv.map_eq_zero_iff T.repr).mp this


-- created on 2026-10-16
