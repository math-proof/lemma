import Lemma.AlgebraicGeometry.ProjSpace
import Notation.AlgebraicGeometry_ProjSpaceLinMap

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

section LinMap

variable (R : Type u) [CommRing R] (n : ℕ)

open scoped AlgebraicGeometry_ProjSpaceLinMap

def linForm (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) R :=
  ∑ j, C (M i j) * X j

theorem linForm_eq_mulVec (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    linForm R n M = Matrix.mulVec (M.map C) X := rfl

theorem isHomogeneous_linForm (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) :
    (linForm R n M i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (M i j) j

theorem linForm_mem (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) : linForm R n M i ∈ 𝒜 1 :=
  (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_linForm R n M i)

def linSubst (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : 𝒜 →+*ᵍ 𝒜 where
  __ := (MvPolynomial.aeval (linForm R n M)).toRingHom
  map_mem {i} {p} hp := by
    rw [mem_homogeneousSubmodule] at hp
    have h := hp.aeval (linForm R n M) (isHomogeneous_linForm R n M)
    rw [one_mul] at h
    exact (mem_homogeneousSubmodule i _).mpr h

theorem linSubst_apply (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (p : MvPolynomial (Fin (n + 1)) R) :
    linSubst R n M p = MvPolynomial.aeval (linForm R n M) p := rfl

@[simp] theorem linSubst_X (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) :
    linSubst R n M (X i) = linForm R n M i :=
  MvPolynomial.aeval_X _ i

@[simp] theorem linSubst_C (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (r : R) :
    linSubst R n M (C r) = C r :=
  MvPolynomial.aeval_C _ r

theorem linSubst_linForm (M M' : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i : Fin (n + 1)) :
    linSubst R n M (linForm R n M' i) = linForm R n (M' * M) i := by
  simp only [linForm, map_sum, map_mul, linSubst_C, linSubst_X, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (mul_assoc _ _ _).symm

theorem irrelevant_le_map_linSubst (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hM : IsUnit M) :
    HomogeneousIdeal.irrelevant 𝒜 ≤ HomogeneousIdeal.map (linSubst R n M) (HomogeneousIdeal.irrelevant 𝒜) := by
  obtain ⟨M', hM'⟩ := hM.exists_left_inv
  intro a ha
  show a ∈ (HomogeneousIdeal.map (linSubst R n M) (HomogeneousIdeal.irrelevant _)).toIdeal
  rw [HomogeneousIdeal.toIdeal_map]
  refine (Ideal.span_le.mpr ?_) (irrelevant_le_span_X R n ha)
  rintro _ ⟨j, rfl⟩
  have hX : (X j : MvPolynomial (Fin (n + 1)) R) = (linSubst R n M).toRingHom (linForm R n M' j) := by
    change X j = linSubst R n M (linForm R n M' j)
    rw [linSubst_linForm, hM', linForm]
    simp only [Matrix.one_apply]
    rw [Fintype.sum_eq_single j (fun k hk => by rw [if_neg (Ne.symm hk), C_0, zero_mul])]
    rw [if_pos rfl, C_1, one_mul]
  rw [hX]
  exact Ideal.mem_map_of_mem _ ((HomogeneousIdeal.mem_irrelevant_iff _ _).mpr (by
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne _ (linForm_mem R n M' j) one_ne_zero]))

def linMap (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hM : IsUnit M) :
    Proj 𝒜 ⟶ Proj 𝒜 :=
  Proj.map (linSubst R n M) (irrelevant_le_map_linSubst R n M hM)

theorem linMap_eq (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hM : IsUnit M) :
    linMap R n M hM = Proj.map (linSubst R n M) (irrelevant_le_map_linSubst R n M hM) := rfl

end LinMap

end ProjSpace

end AlgebraicGeometry

end
