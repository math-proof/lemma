import Mathlib
import sympy.Basic
import Def.LinearAlgebra.Matrix.MvPolynomial
open Polynomial
open Matrix


namespace Matrix

/--
[det_one_add_vecMulVec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MvPolynomial.lean)
-/
@[path]
private lemma det_one_add_vecMulVec {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
  (u v : n → R) :
  det (1 + vecMulVec u v) = 1 + v ⬝ᵥ u := by
  rw [show vecMulVec u v = replicateCol Unit u * replicateRow Unit v by
    ext i j
    simp [vecMulVec, mul_apply, replicateCol, replicateRow]]
  exact det_one_add_replicateCol_mul_replicateRow u v

end Matrix

namespace Matrix

/--
[exists_det_add_smul_vecMulVec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MvPolynomial.lean)
-/
@[path]
private lemma exists_det_add_smul_vecMulVec {n K : Type*}
  [Fintype n] [DecidableEq n] [Field K] (B : Matrix n n K) (u v : n → K) :
  ∃ c : K, ∀ t : K, det (B + t • vecMulVec u v) = det B + t * c := by
  by_cases hu : u = 0
  · refine ⟨0, fun t ↦ ?_⟩
    simp [hu]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
    let e : n → K := Pi.single i 1
    let w : n → K := fun j ↦ if j = i then 0 else u j / u i
    let E : Matrix n n K := 1 - vecMulVec w e
    have hwi : w i = 0 := by simp [w]
    have he_dot (x : n → K) : e ⬝ᵥ x = x i := by
      rw [dotProduct]
      calc
        (∑ j, e j * x j) = e i * x i := by
          apply Fintype.sum_eq_single i
          intro j hji
          simp [e, hji]
        _ = x i := by simp [e]
    have hew : e ⬝ᵥ (-w) = 0 := by
      rw [he_dot]
      simp [hwi]
    have hdetE : det E = 1 := by
      rw [show E = 1 + vecMulVec (-w) e by
        ext j k
        simp [E, vecMulVec]
        ring]
      rw [det_one_add_vecMulVec, hew, add_zero]
    have hEu : E *ᵥ u = Pi.single i (u i) := by
      ext j
      simp only [E, sub_mulVec, one_mulVec, vecMulVec_mulVec]
      rw [he_dot]
      simp only [Pi.sub_apply]
      change u j - w j * u i = (Pi.single i (u i) : n → K) j
      by_cases hji : j = i
      · subst j
        simp [w]
      · rw [show w j = u j / u i by simp only [w, hji, ↓reduceIte]]
        rw [Pi.single_eq_of_ne hji, div_mul_cancel₀ _ hi, sub_self]
    let D := E * B
    let c : K := det (updateRow D i ((u i) • v))
    refine ⟨c, fun t ↦ ?_⟩
    have hleft : det (E * (B + t • vecMulVec u v)) =
      det (B + t • vecMulVec u v) := by
      rw [det_mul, hdetE, one_mul]
    have hbase : det D = det B := by
      simp only [D, det_mul, hdetE, one_mul]
    have hmatrix : E * (B + t • vecMulVec u v) =
      updateRow D i (D i + (t * u i) • v) := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_vecMulVec, hEu]
      change D + t • vecMulVec (Pi.single i (u i)) v =
        updateRow D i (D i + (t * u i) • v)
      ext j k
      simp only [add_apply, smul_apply, vecMulVec_apply]
      by_cases hji : j = i
      · subst j
        rw [updateRow_self]
        simp
        ring
      · rw [updateRow_ne hji]
        simp [hji]
    rw [← hleft, hmatrix, det_updateRow_add, det_updateRow_smul]
    rw [updateRow_eq_self, hbase]
    change _ = det B + t * c
    change det B + t * u i * det (updateRow D i v) =
      det B + t * det (updateRow D i ((u i) • v))
    rw [det_updateRow_smul]
    ring

end Matrix

namespace Matrix

/--
[det_add_smul_vecMulVec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MvPolynomial.lean)
-/
@[path]
lemma det_add_smul_vecMulVec
  [Fintype n] [DecidableEq n] [Field K]
  {B : Matrix n n K}
  {u v : n → K}
  {t : K} :
-- imply
  det (B + t • vecMulVec u v) =
    det B + t * (det (B + vecMulVec u v) - det B) := by
-- proof
  obtain ⟨c, hc⟩ := exists_det_add_smul_vecMulVec B u v
  have h1 := hc 1
  simp only [one_smul, one_mul] at h1
  rw [hc, h1]
  ring

end Matrix

namespace Matrix

/--
[coeff_one_det_add_X_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MvPolynomial.lean)
-/
@[path]
lemma coeff_one_det_add_X_smul
  [Fintype n] [DecidableEq n] [CommRing R]
  {B A : Matrix n n R} :
-- imply
  (det (B.map Polynomial.C + (Polynomial.X : R[X]) • A.map Polynomial.C)).coeff 1 =
    detLinear B A := by
-- proof
  let D := (detRowAlternating : (n → R[X]) [⋀^n]→ₗ[R[X]] R[X])
  change (D (fun i ↦ (B.map Polynomial.C + (Polynomial.X : R[X]) •
    A.map Polynomial.C) i)).coeff 1 = _
  have hrows : (fun i ↦ (B.map Polynomial.C + (Polynomial.X : R[X]) •
    A.map Polynomial.C) i) =
    (fun i ↦ ((Polynomial.X : R[X]) • A.map Polynomial.C) i) +
      (fun i ↦ (B.map Polynomial.C) i) := by
    funext i j
    simp [add_comm]
  rw [hrows, D.map_add_univ]
  change Polynomial.lcoeff R 1
    (∑ s : Finset n,
      D (s.piecewise (fun i ↦ ((Polynomial.X : R[X]) • A.map Polynomial.C) i)
        (fun i ↦ (B.map Polynomial.C) i))) = _
  rw [map_sum]
  have hterm (s : Finset n) :
    D (s.piecewise (fun i ↦ ((Polynomial.X : R[X]) • A.map Polynomial.C) i)
      (fun i ↦ (B.map Polynomial.C) i)) =
      Polynomial.X ^ s.card *
        Polynomial.C (det (fun i j ↦ if i ∈ s then A i j else B i j)) := by
    let c : n → R[X] := fun i ↦ if i ∈ s then Polynomial.X else 1
    let N : Matrix n n R := fun i j ↦ if i ∈ s then A i j else B i j
    let M : Matrix n n R[X] := N.map Polynomial.C
    have hm : s.piecewise (fun i ↦ ((Polynomial.X : R[X]) • A.map Polynomial.C) i)
      (fun i ↦ (B.map Polynomial.C) i) = fun i ↦ c i • M i := by
      funext i j
      by_cases hi : i ∈ s
      · simp only [Finset.piecewise, hi, ↓reduceIte, Matrix.smul_apply, Pi.smul_apply, c]
        have hM : M i j = Polynomial.C (A i j) := by
          dsimp only [M]
          rw [Matrix.map_apply]
          dsimp only [N]
          simp only [hi, ↓reduceIte]
        rw [hM, Matrix.map_apply]
      · simp only [Finset.piecewise, hi, ↓reduceIte, Pi.smul_apply, c]
        have hM : M i j = Polynomial.C (B i j) := by
          dsimp only [M]
          rw [Matrix.map_apply]
          dsimp only [N]
          simp only [hi, ↓reduceIte]
        rw [hM]
        simp
    rw [hm, AlternatingMap.map_smul_univ D c M]
    have hc : ∏ i, c i = Polynomial.X ^ s.card := by simp [c]
    rw [hc]
    change Polynomial.X ^ s.card * det M = _
    rw [show det M = Polynomial.C (det N) by
      exact (RingHom.map_det Polynomial.C N).symm]
  simp_rw [hterm]
  have hcoeff (s : Finset n) :
    (Polynomial.X ^ s.card * Polynomial.C
      (det (fun i j ↦ if i ∈ s then A i j else B i j))).coeff 1 =
      if s.card = 1 then det (fun i j ↦ if i ∈ s then A i j else B i j) else 0 := by
    rw [Polynomial.coeff_mul_C]
    by_cases h : s.card = 1
    · simp [h]
    · have hk : 1 ≠ s.card := Ne.symm h
      simp [h, hk, Polynomial.coeff_X_pow]
  change (∑ s : Finset n,
    (Polynomial.X ^ s.card * Polynomial.C
      (det (fun i j ↦ if i ∈ s then A i j else B i j))).coeff 1) = _
  rw [Finset.sum_congr rfl fun s _ ↦ hcoeff s]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter fun s : Finset n ↦ s.card = 1) =
    Finset.univ.powersetCard 1 := by
    rw [Finset.powersetCard_eq_filter, Finset.powerset_univ]
  rw [hfilter, Finset.powersetCard_one, Finset.sum_map]
  unfold detLinear
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ext j k
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

end Matrix

namespace Matrix

/--
[detLinear_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MvPolynomial.lean)
-/
@[path]
lemma detLinear_add
  [Fintype n] [DecidableEq n] [CommRing R]
  {B A C : Matrix n n R} :
-- imply
  detLinear B (A + C) = detLinear B A + detLinear B C := by
-- proof
  unfold detLinear
  simp_rw [Matrix.add_apply, show (fun j ↦ A _ j + C _ j) = A _ + C _ by rfl,
    det_updateRow_add]
  exact Finset.sum_add_distrib

end Matrix

namespace Matrix

/--
[detLinear_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/MvPolynomial.lean)
-/
@[path]
lemma detLinear_smul
  [Fintype n] [DecidableEq n] [CommRing R]
  {B A : Matrix n n R}
  {a : R} :
-- imply
  detLinear B (a • A) = a * detLinear B A := by
-- proof
  unfold detLinear
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← det_updateRow_smul B i a (fun j ↦ A i j)]
  congr

end Matrix


-- created on 2026-10-20
-- updated on 2026-10-23
