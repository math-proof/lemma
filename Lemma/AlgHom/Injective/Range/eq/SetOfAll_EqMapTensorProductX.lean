import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


/--
[Algebra_TensorProduct_injective_map_fixedPoints_val_and_range_eq_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_injective_map_fixedPoints_val_and_range_eq_of_flat.lean)
-/
@[path]
private lemma main
  [CommRing B] [CommRing A] [Algebra B A] [CommRing T] [Algebra B T]
  [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G B A] [Module.Flat B T] :
-- imply
  Function.Injective (Algebra.TensorProduct.map (AlgHom.id T T) (FixedPoints.subalgebra B A G).val) ∧
    Set.range (Algebra.TensorProduct.map (AlgHom.id T T) (FixedPoints.subalgebra B A G).val) =
      {x : T ⊗[B] A | ∀ g : G,
        Algebra.TensorProduct.map (AlgHom.id T T) (MulSemiringAction.toAlgHom B A g) x = x} := by
-- proof
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : DecidableEq G := Classical.decEq G
  let act : A →ₐ[B] (G → A) := AlgHom.pi (fun g : G => MulSemiringAction.toAlgHom B A g)
  let diag : A →ₐ[B] (G → A) := AlgHom.pi (fun _ : G => AlgHom.id B A)
  have heq : FixedPoints.subalgebra B A G = AlgHom.equalizer act diag := by
    ext a
    simp only [AlgHom.mem_equalizer, act, diag, AlgHom.pi_apply, MulSemiringAction.toAlgHom_apply,
      AlgHom.id_apply, funext_iff]
    rfl
  rw [heq]
  let e := AlgHom.tensorEqualizerEquiv T T act diag
  have hfac : ∀ x, Algebra.TensorProduct.map (AlgHom.id T T) (AlgHom.equalizer act diag).val x =
      (e x : T ⊗[B] A) := by
    intro x
    rw [AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer]
  let p := Algebra.TensorProduct.piRight B T T (fun _ : G => A)
  have h1 : ∀ (x : T ⊗[B] A) (g : G), p (Algebra.TensorProduct.map (AlgHom.id T T) act x) g =
      Algebra.TensorProduct.map (AlgHom.id T T) (MulSemiringAction.toAlgHom B A g) x := by
    intro x g
    induction x using TensorProduct.inductionOn with
    | tmul t a =>
      simp [p, act, Algebra.TensorProduct.piRight_tmul]
    | add x y hx hy =>
      simp only [map_add, Pi.add_apply, hx, hy]
  have h2 : ∀ (x : T ⊗[B] A) (g : G), p (Algebra.TensorProduct.map (AlgHom.id T T) diag x) g = x := by
    intro x g
    induction x using TensorProduct.inductionOn with
    | tmul t a =>
      simp [p, diag, Algebra.TensorProduct.piRight_tmul]
    | add x y hx hy =>
      simp only [map_add, Pi.add_apply, hx, hy]
  have key : ∀ x : T ⊗[B] A,
      x ∈ AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id T T) act)
        (Algebra.TensorProduct.map (AlgHom.id T T) diag) ↔
      ∀ g : G, Algebra.TensorProduct.map (AlgHom.id T T) (MulSemiringAction.toAlgHom B A g) x = x := by
    intro x
    rw [AlgHom.mem_equalizer, ← p.injective.eq_iff, funext_iff]
    apply forall_congr'
    intro g
    rw [h1, h2]
  refine ⟨?_, ?_⟩
  ·
    intro x y hxy
    rw [hfac, hfac] at hxy
    apply e.injective (Subtype.ext hxy)
  ·
    ext z
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    ·
      rintro ⟨x, rfl⟩
      rw [hfac]
      apply (key _).mp (e x).2
    ·
      intro hz
      refine ⟨e.symm ⟨z, (key z).mpr hz⟩, ?_⟩
      rw [hfac, AlgEquiv.apply_symm_apply]


-- created on 2026-10-16
