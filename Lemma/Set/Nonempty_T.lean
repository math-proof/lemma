import Mathlib
import sympy.Basic
open scoped TensorProduct


/--
[Algebra_nonempty_algHom_tensorProduct_adjoin_equiv_subtype_apply_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_nonempty_algHom_tensorProduct_adjoin_equiv_subtype_apply_eq.lean)
-/
@[path]
private lemma main
  [CommRing A] [CommRing B] [Algebra A B]
  {a : B} [CommRing F] [Algebra (Algebra.adjoin A ({a} : Set B)) F] [CommRing T] [Algebra A T] [Algebra F T] [Algebra (Algebra.adjoin A ({a} : Set B)) T] [IsScalarTower (Algebra.adjoin A ({a} : Set B)) F T] [IsScalarTower A (Algebra.adjoin A ({a} : Set B)) T] :
-- imply
  Nonempty ((F ⊗[Algebra.adjoin A ({a} : Set B)] B →ₐ[F] T) ≃
    (Subtype fun φ : B →ₐ[A] T => φ a =
      algebraMap (Algebra.adjoin A ({a} : Set B)) T ⟨a, Algebra.self_mem_adjoin_singleton A a⟩)) := by
-- proof
  classical
  set S : Subalgebra A B := Algebra.adjoin A ({a} : Set B) with hS
  have haS : a ∈ S := Algebra.self_mem_adjoin_singleton A a
  have key : ∀ φ : B →ₐ[A] T, φ a = algebraMap S T ⟨a, haS⟩ →
      ∀ s : S, φ (s : B) = algebraMap S T s := by
    intro φ hφ s
    obtain ⟨p, hp⟩ : ∃ p : Polynomial A, Polynomial.aeval a p = (s : B) := by
      have : (s : B) ∈ (Polynomial.aeval a : Polynomial A →ₐ[A] B).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]
        apply s.2
      exact (AlgHom.mem_range _).mp this
    have hs : s = Polynomial.aeval (⟨a, haS⟩ : S) p := by
      apply Subtype.ext
      change (s : B) = S.val (Polynomial.aeval (⟨a, haS⟩ : S) p)
      rw [← Polynomial.aeval_algHom_apply, ← hp]
      rfl
    calc
      _ = φ (Polynomial.aeval a p) := by rw [hp]
      _ = Polynomial.aeval (φ a) p := (Polynomial.aeval_algHom_apply φ a p).symm
      _ = Polynomial.aeval ((IsScalarTower.toAlgHom A S T) ⟨a, haS⟩) p := by
        rw [hφ]
        rfl
      _ = IsScalarTower.toAlgHom A S T (Polynomial.aeval (⟨a, haS⟩ : S) p) :=
        Polynomial.aeval_algHom_apply _ _ _
      _ = algebraMap S T s := by
        rw [← hs]
        rfl
  let toS : (Subtype fun φ : B →ₐ[A] T => φ a = algebraMap S T ⟨a, haS⟩) → (B →ₐ[S] T) := fun φ =>
    AlgHom.mk φ.1.toRingHom (fun s => key φ.1 φ.2 s)
  have htoS : ∀ φ b, toS φ b = φ.1 b := fun φ b => rfl
  have e1 : algebraMap S (F ⊗[S] B) ⟨a, haS⟩ = (1 : F) ⊗ₜ[S] a := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, ← TensorProduct.tmul_smul,
      Algebra.smul_def, mul_one]
    rfl
  let toFun (g : F ⊗[S] B →ₐ[F] T) : Subtype fun φ : B →ₐ[A] T => φ a = algebraMap S T ⟨a, haS⟩ :=
    ⟨((g.restrictScalars S).comp (Algebra.TensorProduct.includeRight (R := S) (A := F) (B := B))).restrictScalars A, by show g ((1 : F) ⊗ₜ[S] a) = algebraMap S T ⟨a, haS⟩; rw [← e1]; apply (g.restrictScalars S).commutes⟩
  let invFun (φ : Subtype fun ψ : B →ₐ[A] T => ψ a = algebraMap S T ⟨a, haS⟩) : F ⊗[S] B →ₐ[F] T :=
    Algebra.TensorProduct.lift (Algebra.ofId F T) (toS φ) (fun _ _ => Commute.all _ _)
  have hleft (g : F ⊗[S] B →ₐ[F] T) : invFun (toFun g) = g := by
    unfold toFun invFun
    apply Algebra.TensorProduct.ext'
    intro f b
    simp only [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, htoS,
      AlgHom.coe_restrictScalars', AlgHom.coe_comp, Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply]
    have : (f ⊗ₜ[S] b : F ⊗[S] B) = f • ((1 : F) ⊗ₜ[S] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, Algebra.smul_def]
  have hright (φ : Subtype fun ψ : B →ₐ[A] T => ψ a = algebraMap S T ⟨a, haS⟩) : toFun (invFun φ) = φ := by
    unfold toFun invFun
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    simp [htoS]
  refine ⟨⟨toFun, invFun, hleft, hright⟩⟩


-- created on 2026-10-13
