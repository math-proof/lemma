import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

universe u v w

open scoped TensorProduct

namespace IsAlgClosed

section FiniteType

variable {K : Type u} [Field K]

theorem algebraMap_quotient_bijective [IsAlgClosed K] {A : Type v} [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    Function.Bijective (algebraMap K (A ⧸ m)) := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  have : Algebra.IsIntegral K (A ⧸ m) := inferInstance
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

variable (K) in

noncomputable def pointOfMaximal [IsAlgClosed K] {A : Type v} [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] : A →ₐ[K] K :=
  let e := RingEquiv.ofBijective (algebraMap K (A ⧸ m)) (algebraMap_quotient_bijective m)
  { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk m)
    commutes' := fun k => by
      change e.symm (Ideal.Quotient.mk m (algebraMap K A k)) = k
      rw [Ideal.Quotient.mk_algebraMap]
      exact e.symm_apply_apply k }

theorem pointOfMaximal_eq_zero_iff [IsAlgClosed K] {A : Type v} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] (a : A) :
    pointOfMaximal K m a = 0 ↔ a ∈ m := by
  change (RingEquiv.ofBijective (algebraMap K (A ⧸ m))
    (algebraMap_quotient_bijective m)).symm (Ideal.Quotient.mk m a) = 0 ↔ a ∈ m
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

theorem isDomain_tensorProduct_of_finiteType [IsAlgClosed K] (A : Type v) (B : Type w)
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [IsDomain A]
    [CommRing B] [Algebra K B] [IsDomain B] :
    IsDomain (A ⊗[K] B) := by
  classical
  haveI : Nontrivial (A ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K A B
      (algebraMap K A).injective (algebraMap K B).injective

  let bB := Module.Free.chooseBasis K B
  let 𝔅 := Algebra.TensorProduct.basis A bB
  let I : A ⊗[K] B → Ideal A := fun x => Ideal.span (Set.range (𝔅.repr x))
  have hI : ∀ x, I x = ⊥ → x = 0 := by
    intro x hx
    apply 𝔅.repr.injective
    rw [map_zero]
    ext i
    exact (Ideal.span_eq_bot.mp hx) _ ⟨i, rfl⟩

  have hpt : ∀ (x y : A ⊗[K] B), x * y = 0 →
      ∀ (m : Ideal A) [m.IsMaximal], I x ≤ m ∨ I y ≤ m := by
    intro x y hxy m _
    let φ : A →ₐ[K] K := pointOfMaximal K m
    let ψ : A ⊗[K] B →ₐ[K] B :=
      Algebra.TensorProduct.lift ((Algebra.ofId K B).comp φ) (AlgHom.id K B)
        (fun _ _ => Commute.all _ _)
    have hψ : ∀ (z : A ⊗[K] B) (i), bB.repr (ψ z) i = φ (𝔅.repr z i) := by
      intro z i
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [ψ, 𝔅, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, Function.comp_apply,
          Algebra.ofId_apply, AlgHom.coe_id, id_eq, Algebra.TensorProduct.basis_repr_tmul,
          Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
        rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, Algebra.algebraMap_self,
          RingHom.id_apply]
      | add z w hz hw => simp [map_add, hz, hw]
    have hker : ∀ z : A ⊗[K] B, ψ z = 0 → I z ≤ m := by
      intro z hz
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, ← pointOfMaximal_eq_zero_iff (K := K), ← hψ, hz, map_zero,
        Finsupp.zero_apply]
    have h0 : ψ x * ψ y = 0 := by rw [← map_mul, hxy, map_zero]
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (hker x h)
    · exact Or.inr (hker y h)

  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K) (B := A)
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} hxy => ?_⟩
  have hle : I x * I y ≤ (⊥ : Ideal A) := by
    rw [← Ideal.radical_bot_of_noZeroDivisors, Ideal.radical_eq_jacobson]
    refine le_sInf ?_
    rintro J ⟨-, hJ⟩
    rcases hpt x y hxy J with h | h
    · exact Ideal.mul_le_left.trans h
    · exact Ideal.mul_le_right.trans h
  rcases (Ideal.mul_eq_bot.mp (le_bot_iff.mp hle)) with h | h
  · exact Or.inl (hI x h)
  · exact Or.inr (hI y h)

end FiniteType

section Fields

variable (k : Type u) [Field k] [IsAlgClosed k]

theorem isDomain_tensorProduct_of_field (F : Type v) (B : Type w) [Field F] [Algebra k F]
    [CommRing B] [Algebra k B] [IsDomain B] : IsDomain (F ⊗[k] B) := by
  classical
  haveI : Nontrivial (F ⊗[k] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k F B
      (algebraMap k F).injective (algebraMap k B).injective
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} hxy => ?_⟩
  obtain ⟨sx, hx⟩ := TensorProduct.exists_finset x
  obtain ⟨sy, hy⟩ := TensorProduct.exists_finset y

  let A : Subalgebra k F := Algebra.adjoin k ↑(sx.image Prod.fst ∪ sy.image Prod.fst)
  haveI : Algebra.FiniteType k A :=
    A.fg_iff_finiteType.mp ⟨sx.image Prod.fst ∪ sy.image Prod.fst, rfl⟩
  let ι : A ⊗[k] B →ₐ[k] F ⊗[k] B := Algebra.TensorProduct.map A.val (AlgHom.id k B)
  have hι : Function.Injective ι := by
    have h : Function.Injective (A.val.toLinearMap.rTensor B) :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := B) A.val.toLinearMap
        Subtype.val_injective
    intro a b hab
    exact h hab
  have hlift : ∀ s : Finset (F × B), (∀ p ∈ s, p.1 ∈ A) →
      ∃ z : A ⊗[k] B, ι z = ∑ p ∈ s, p.1 ⊗ₜ[k] p.2 := by
    intro s hs
    refine ⟨∑ p ∈ s.attach, (⟨p.1.1, hs p.1 p.2⟩ : A) ⊗ₜ[k] p.1.2, ?_⟩
    rw [map_sum, ← Finset.sum_attach s]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [ι]
  have hxA : ∀ p ∈ sx, p.1 ∈ A := fun p hp =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr
      (Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hp)))
  have hyA : ∀ p ∈ sy, p.1 ∈ A := fun p hp =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.fst hp)))
  obtain ⟨x', hx'⟩ := hlift sx hxA
  obtain ⟨y', hy'⟩ := hlift sy hyA
  rw [← hx] at hx'
  rw [← hy] at hy'
  subst hx' hy'
  haveI : IsDomain (A ⊗[k] B) := isDomain_tensorProduct_of_finiteType (K := k) A B
  have hxy' : x' * y' = 0 := hι (by rw [map_mul, hxy, map_zero])
  rcases mul_eq_zero.mp hxy' with h | h
  · exact Or.inl (by rw [h, map_zero])
  · exact Or.inr (by rw [h, map_zero])

end Fields

end IsAlgClosed
