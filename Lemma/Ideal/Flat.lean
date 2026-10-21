import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma flat_quotientMap
  (𝒪 : Type) [CommRing 𝒪] (S : Type) [CommRing S] [Algebra 𝒪 S] [Module.Flat 𝒪 S]
  (I : Ideal 𝒪) (J : Ideal S) (hIJ : I ≤ J.comap (algebraMap 𝒪 S))
  (hJI : J ≤ I.map (algebraMap 𝒪 S)) :
    (Ideal.quotientMap J (algebraMap 𝒪 S) hIJ).Flat := by
  set A := 𝒪 ⧸ I
  set φ := Ideal.quotientMap J (algebraMap 𝒪 S) hIJ
  let _ : Algebra A (S ⧸ J) := φ.toAlgebra
  have hφa : ∀ a : A, algebraMap A (S ⧸ J) a = φ a := fun a => rfl
  let _ : IsScalarTower 𝒪 A (S ⧸ J) := IsScalarTower.of_algebraMap_eq (fun o => rfl)
  let L : AlgHom A (TensorProduct 𝒪 A S) (S ⧸ J) :=
    Algebra.TensorProduct.lift (Algebra.ofId A (S ⧸ J)) (Ideal.Quotient.mkₐ 𝒪 J) (fun _ _ => Commute.all _ _)
  have hL : ∀ (a : A) (s : S), L (TensorProduct.tmul 𝒪 a s) = φ a * Ideal.Quotient.mk J s := fun a s => by
    simp only [L, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk, hφa]
  have hker : ∀ s ∈ J, (Algebra.TensorProduct.includeRight : AlgHom 𝒪 S (TensorProduct 𝒪 A S)) s = 0 := by
    intro s hs
    have hs' : s ∈ Ideal.span ((algebraMap 𝒪 S) '' (I : Set 𝒪)) := hJI hs
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hs'
    ·
      rintro _ ⟨o, ho, rfl⟩
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, show algebraMap 𝒪 A o = 0 from (Ideal.Quotient.eq_zero_iff_mem.2 ho), TensorProduct.zero_tmul]
    · apply map_zero
    ·
      intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    ·
      intro r x _ hx
      rw [smul_eq_mul, map_mul, hx, mul_zero]
  let K : RingHom (S ⧸ J) (TensorProduct 𝒪 A S) :=
    Ideal.Quotient.lift J (Algebra.TensorProduct.includeRight : AlgHom 𝒪 S (TensorProduct 𝒪 A S)).toRingHom hker
  have hK : ∀ s : S, K (Ideal.Quotient.mk J s) = TensorProduct.tmul 𝒪 (1 : A) s := fun s => rfl
  have hKφ : ∀ a : A, K (φ a) = TensorProduct.tmul 𝒪 a (1 : S) := by
    intro a
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective a
    show K (Ideal.Quotient.mk J (algebraMap 𝒪 S o)) = _
    rw [hK, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  have hKL : ∀ t : TensorProduct 𝒪 A S, K (L t) = t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a s => rw [hL, map_mul, hKφ, hK, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hLK : ∀ x : S ⧸ J, L (K x) = x := by
    intro x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hK, hL, map_one, one_mul]
  let e : LinearEquiv (RingHom.id A) (S ⧸ J) (TensorProduct 𝒪 A S) :=
    { toFun := K
      invFun := L
      map_add' := fun x y => map_add K x y
      map_smul' := fun a x => by
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
        show K (a • Ideal.Quotient.mk J s) = a • K (Ideal.Quotient.mk J s)
        rw [Algebra.smul_def, hφa, map_mul, hKφ, hK, TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul, mul_one]
      left_inv := hLK
      right_inv := hKL }
  show @Module.Flat A (S ⧸ J) _ _ φ.toAlgebra.toModule
  apply Module.Flat.of_linearEquiv e

private lemma span_pow_le
  (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (S : Type) [CommRing S] [Algebra 𝒪 S] (n : ℕ) :
    Ideal.span {π ^ (n + 1)} ≤ (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}).comap (algebraMap 𝒪 S) := by
  rw [Ideal.span_le]
  rw [Set.singleton_subset_iff]
  rw [SetLike.mem_coe]
  rw [Ideal.mem_comap]
  rw [map_pow]
  exact Ideal.subset_span rfl

/--
[AlgebraicGeometry_flat_specMap_quotientMap_pow_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_flat_specMap_quotientMap_pow_of_flat.lean)
-/
@[path]
private lemma main
  (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (S : Type) [CommRing S] [Algebra 𝒪 S] [Module.Flat 𝒪 S] (n : ℕ) :
    Flat (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S) (span_pow_le 𝒪 π S n)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom]
  apply flat_quotientMap 𝒪 S _ _ _ (by rw [Ideal.map_span, Set.image_singleton, map_pow])


-- created on 2026-10-20
