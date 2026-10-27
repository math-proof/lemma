import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

private lemma lmul'_comp_map_comp
  {R : Type u} [CommRing R]
  {H : Type v} [CommRing H] [HopfAlgebra R H]
  {T : Type w} [CommRing T] [Algebra R T]
  (g : AlgHom R H T) (a b : AlgHom R H H) :
  -- imply
  (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map (g.comp a) (g.comp b)) = g.comp ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map a b)) := by
  -- proof
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro x y
  simp [Algebra.TensorProduct.lmul'_apply_tmul]

private lemma toConv_comp_pow
  {R : Type u} [CommRing R]
  {H : Type v} [CommRing H] [HopfAlgebra R H]
  {T : Type w} [CommRing T] [Algebra R T]
  (g : AlgHom R H T) (u : WithConv (AlgHom R H H)) (k : ℕ) :
  -- imply
  (WithConv.toConv (g.comp u.ofConv)) ^ k = WithConv.toConv (g.comp (u ^ k).ofConv) := by
  -- proof
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, AlgHom.convOne_def, AlgHom.convOne_def]
    congr 1
    change (Algebra.ofId R T).comp (Bialgebra.counitAlgHom R H) = g.comp ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H))
    rw [← AlgHom.comp_assoc]
    congr 1
    apply AlgHom.ext fun r => (g.commutes r).symm
  | succ k ih =>
    rw [pow_succ, pow_succ, ih, AlgHom.convMul_def, AlgHom.convMul_def]
    congr 1
    change (Algebra.TensorProduct.lmul' R).comp ((Algebra.TensorProduct.map (g.comp (u ^ k).ofConv) (g.comp u.ofConv)).comp (Bialgebra.comulAlgHom R H)) = g.comp ((Algebra.TensorProduct.lmul' R).comp ((Algebra.TensorProduct.map (u ^ k).ofConv u.ofConv).comp (Bialgebra.comulAlgHom R H)))
    rw [← AlgHom.comp_assoc, lmul'_comp_map_comp, AlgHom.comp_assoc, AlgHom.comp_assoc]

/--
[HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {H : Type v} [CommRing H] [HopfAlgebra R H]
  (m : ℕ) :
  -- imply
  (∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (AlgHom R H T)), f ^ m = 1) ↔ (WithConv.toConv (AlgHom.id R H)) ^ m = 1 := by
  -- proof
  constructor
  ·
    intro h
    apply h H (WithConv.toConv (AlgHom.id R H))
  ·
    intro hid T _ _ f
    have hf : f = WithConv.toConv (f.ofConv.comp (WithConv.toConv (AlgHom.id R H)).ofConv) := by
      change f = WithConv.toConv (f.ofConv.comp (AlgHom.id R H))
      rw [AlgHom.comp_id]
    rw [hf, toConv_comp_pow, hid]
    have h0 := toConv_comp_pow f.ofConv (WithConv.toConv (AlgHom.id R H)) 0
    rw [pow_zero, pow_zero] at h0
    apply h0.symm


-- created on 2026-10-20
