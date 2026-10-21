import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
  {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
private lemma map_id_apply_eq (g : B →ₐ[R] C) (x : S ⊗[R] B) :
    Algebra.TensorProduct.map (AlgHom.id S S) g x = Algebra.TensorProduct.map (AlgHom.id R S) g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b => simp
  | add x y hx hy => simp [map_add, hx, hy]
private lemma _root_.Ideal.map_algHom_eq_map_ringHom {X Y : Type*} [Semiring X] [Semiring Y] [Algebra R X] [Algebra R Y]
    (f : X →ₐ[R] Y) (I : Ideal X) : Ideal.map f I = Ideal.map (f : X →+* Y) I := rfl
private lemma ker_map_id_eq (g : B →ₐ[R] C) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id S S) g) = RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S) g) := by
  ext x
  simp only [RingHom.mem_ker]
  change Algebra.TensorProduct.map (AlgHom.id S S) g x = 0 ↔ Algebra.TensorProduct.map (AlgHom.id R S) g x = 0
  rw [map_id_apply_eq]
private lemma algHom_eq_of_comp_eq {X Y Z : Type*} [Semiring X] [Semiring Y] [Semiring Z] [Algebra S X] [Algebra S Y] [Algebra S Z]
    (π : X →ₐ[S] Y) (hπ : Function.Surjective π) (f g : Y →ₐ[S] Z) (h : f.comp π = g.comp π) : f = g := by
  ext t
  obtain ⟨x, rfl⟩ := hπ t
  exact DFunLike.congr_fun h x
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {B : Type*} [CommRing B] [Bialgebra R B]
private lemma ker_counitAlgHom_baseChange :
    RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] B)) =
      (RingHom.ker (Bialgebra.counitAlgHom R B)).map (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B) := by
  have hsurj : Function.Surjective (Bialgebra.counitAlgHom R B) := fun r =>
    ⟨algebraMap R B r, by rw [Bialgebra.counitAlgHom_apply, Bialgebra.counit_algebraMap]⟩
  rw [← Algebra.TensorProduct.lTensor_ker (A := S) (Bialgebra.counitAlgHom R B) hsurj]
  ext x
  simp only [RingHom.mem_ker]
  rw [Bialgebra.TensorProduct.counitAlgHom_def]
  change (Algebra.TensorProduct.rid R S S) (Algebra.TensorProduct.map (Bialgebra.counitAlgHom S S) (Bialgebra.counitAlgHom R B) x) = 0 ↔
    Algebra.TensorProduct.map (AlgHom.id R S) (Bialgebra.counitAlgHom R B) x = 0
  rw [map_eq_zero_iff _ (Algebra.TensorProduct.rid R S S).injective]
  have h1 : Bialgebra.counitAlgHom S S = AlgHom.id S S := AlgHom.ext fun _ => rfl
  rw [h1, map_id_apply_eq]
/--
[Bialgebra_exists_bialgEquiv_comp_eq_tensorProduct_map_of_surjective_of_ker_eq_map_ker_counit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Bialgebra_exists_bialgEquiv_comp_eq_tensorProduct_map_of_surjective_of_ker_eq_map_ker_counit.lean)
-/
@[path]
private lemma main
    {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    {B C H : Type*} [CommRing B] [CommRing C] [CommRing H] [Bialgebra R B] [Bialgebra R C] [Bialgebra R H]
    (ψ : B →ₐc[R] C) (q : C →ₐc[R] H) (hq : Function.Surjective q)
    (hkerq : RingHom.ker (q : C →+* H) = Ideal.map (ψ : B →ₐ[R] C) (RingHom.ker (Bialgebra.counitAlgHom R B)))
    {T : Type*} [CommRing T] [Bialgebra S T]
    (π : S ⊗[R] C →ₐc[S] T) (hπ : Function.Surjective π)
    (hkerπ : RingHom.ker (π : S ⊗[R] C →ₐ[S] T) =
      Ideal.map (Bialgebra.TensorProduct.map (BialgHom.id S S) ψ : S ⊗[R] B →ₐ[S] S ⊗[R] C)
        (RingHom.ker (Bialgebra.counitAlgHom S (S ⊗[R] B)))) :
    ∃ e : T ≃ₐc[S] S ⊗[R] H, ∀ x : S ⊗[R] C, e (π x) = Bialgebra.TensorProduct.map (BialgHom.id S S) q x := by
  classical
  set Q : S ⊗[R] C →ₐ[S] S ⊗[R] H := (Bialgebra.TensorProduct.map (BialgHom.id S S) q : S ⊗[R] C →ₐ[S] S ⊗[R] H) with hQ
  have hQdef : Q = Algebra.TensorProduct.map (AlgHom.id S S) (q : C →ₐ[R] H) := rfl
  have hQsurj : Function.Surjective Q := by
    rw [hQdef]
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul s h =>
        obtain ⟨c, rfl⟩ := hq h
        exact ⟨s ⊗ₜ c, by simp⟩
    | add x y hx hy =>
        obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, map_add _ _ _⟩
  have hkerQ : RingHom.ker Q = RingHom.ker (π : S ⊗[R] C →ₐ[S] T) := by
    rw [hQdef, ker_map_id_eq, Algebra.TensorProduct.lTensor_ker _ hq]
    change Ideal.map _ (RingHom.ker (q : C →+* H)) = _
    rw [hkerq, hkerπ, ker_counitAlgHom_baseChange]
    simp only [Ideal.map_algHom_eq_map_ringHom, Ideal.map_map]
    congr 1
  let eAlg : T ≃ₐ[S] S ⊗[R] H :=
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.trans
      ((Ideal.quotientEquivAlgOfEq S hkerQ.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hQsurj))
  have heAlg : ∀ x, eAlg (π x) = Q x := by
    intro x
    simp only [eAlg, AlgEquiv.trans_apply]
    rw [show (π x) = (π : S ⊗[R] C →ₐ[S] T) x from rfl, Ideal.quotientKerAlgEquivOfSurjective_symm_apply,
      Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]
  have heAlg' : (eAlg : T →ₐ[S] S ⊗[R] H).comp (π : S ⊗[R] C →ₐ[S] T) = Q := AlgHom.ext heAlg
  refine ⟨BialgEquiv.ofAlgEquiv eAlg ?_ ?_, fun x => heAlg x⟩
  · apply algHom_eq_of_comp_eq (π : S ⊗[R] C →ₐ[S] T) hπ
    rw [AlgHom.comp_assoc, heAlg', hQ, BialgHom.counitAlgHom_comp, BialgHom.counitAlgHom_comp]
  · apply algHom_eq_of_comp_eq (π : S ⊗[R] C →ₐ[S] T) hπ
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, heAlg', ← BialgHom.map_comp_comulAlgHom, ← AlgHom.comp_assoc,
      ← Algebra.TensorProduct.map_comp, heAlg', hQ, BialgHom.map_comp_comulAlgHom]

-- created on 2026-10-20
