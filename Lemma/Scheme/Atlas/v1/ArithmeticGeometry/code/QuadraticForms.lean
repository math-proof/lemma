import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.QuadraticForms.Part2
open LinearMap (BilinMap BilinForm) QuadraticFormEquiv QuadraticMap QuadraticFormDef93 QuadraticFormDef94
open QuadraticMap
open Module


namespace QuadraticFormEquiv

/--
[associated_bilinForm_isSymm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma associated_bilinForm_isSymm
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {Q : QuadraticForm k V} :
-- imply
  (QuadraticMap.associated (R := k) Q).IsSymm :=
-- proof
  QuadraticForm.associated_isSymm k Q

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[quadForm_eq_associated_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma quadForm_eq_associated_self
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {Q : QuadraticForm k V}
  {x : V} :
-- imply
  Q x = QuadraticMap.associated (R := k) Q x x :=
-- proof
  (QuadraticMap.associated_eq_self_apply k Q x).symm

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[associated_eq_half_polar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma associated_eq_half_polar
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {Q : QuadraticForm k V}
  {x y : V} :
-- imply
  QuadraticMap.associated (R := k) Q x y = ⅟(2 : k) * (Q (x + y) - Q x - Q y) := by
-- proof
  rw [QuadraticMap.associated_apply]
  simp only [Module.End.smul_def, QuadraticMap.half_moduleEnd_apply_eq_half_smul, smul_eq_mul]

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[associated_toQuadraticMap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma associated_toQuadraticMap_eq
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {Q : QuadraticForm k V} :
-- imply
  (QuadraticMap.associated (R := k) Q).toQuadraticMap = Q :=
-- proof
  QuadraticMap.toQuadraticMap_associated k Q

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[associated_of_symm_bilinForm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma associated_of_symm_bilinForm
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {B : BilinForm k V}
-- given
  (hB : B.IsSymm) :
-- imply
  QuadraticMap.associated (R := k) B.toQuadraticMap = B :=
-- proof
  QuadraticMap.associated_left_inverse k hB.eq

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[quadForm_add_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma quadForm_add_expansion
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {Q : QuadraticForm k V}
  {x y : V} :
-- imply
  Q (x + y) = Q x + Q y + 2 * (QuadraticMap.associated (R := k) Q x y) := by
-- proof
  rw [QuadraticMap.associated_apply]
  simp only [Module.End.smul_def, QuadraticMap.half_moduleEnd_apply_eq_half_smul, smul_eq_mul]
  rw [show (2 : k) * (⅟(2 : k) * (Q (x + y) - Q x - Q y)) = Q (x + y) - Q x - Q y from by
    rw [← mul_assoc, mul_invOf_self', one_mul]]
  ring

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[matrix_to_bilinForm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma matrix_to_bilinForm_apply
  [Field k]
  [Fintype n]
  [DecidableEq n]
  {A : Matrix n n k}
  {x y : n → k} :
-- imply
  matrixBilinEquiv A x y = dotProduct x (A.mulVec y) :=
-- proof
  Matrix.toLinearMap₂'_apply' A x y

end QuadraticFormEquiv

namespace QuadraticFormEquiv

variable [Field k]
variable [Fintype n] [DecidableEq n]
/--
[toMatrix_toLinearMap₂](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma toMatrix_toLinearMap₂ (A : Matrix n n k) :
  bilinFormToMatrix (matrixBilinEquiv A) = A :=
  bilinFormToMatrix.apply_symm_apply A

end QuadraticFormEquiv

namespace QuadraticFormEquiv

variable [Field k]
variable [Fintype n] [DecidableEq n]
/--
[toLinearMap₂_toMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma toLinearMap₂_toMatrix (B : BilinMap k (n → k) k) :
  matrixBilinEquiv (bilinFormToMatrix B) = B :=
  matrixBilinEquiv.apply_symm_apply B

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[quadraticFormToMatrix_isSymm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma quadraticFormToMatrix_isSymm
  [Field k]
  [NeZero (2 : k)]
  [Fintype n]
  [DecidableEq n]
  {Q : QuadraticForm k (n → k)} :
-- imply
  Q.toMatrix'.IsSymm :=
-- proof
  QuadraticMap.isSymm_toMatrix' Q

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[bilinForm_symm_to_matrix_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma bilinForm_symm_to_matrix_symm
  [Field k]
  [Fintype n]
  [DecidableEq n]
  {B : BilinForm k (n → k)}
-- given
  (hB : B.IsSymm) :
-- imply
  (LinearMap.toMatrix₂' k B).IsSymm := by
-- proof
  ext i j
  simp only [Matrix.transpose_apply, LinearMap.toMatrix₂'_apply]
  exact (hB.eq (Pi.single i 1) (Pi.single j 1)).symm

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[matrix_symm_to_bilinForm_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma matrix_symm_to_bilinForm_symm
  [Field k]
  [Fintype n]
  [DecidableEq n]
  {A : Matrix n n k}
-- given
  (hA : A.IsSymm) :
-- imply
  (Matrix.toLinearMap₂' k A).IsSymm := by
-- proof
  constructor
  intro x y
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have hij : A j i = A i j := by
    have h := congr_fun (congr_fun hA.symm i) j
    simp only [Matrix.transpose_apply] at h
    exact h.symm
  rw [hij]; ring
section EquivalentQuadraticForms
open QuadraticMap

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[equivalent_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma equivalent_def
  [CommSemiring k]
  [AddCommMonoid V]
  [Module k V]
  {f g : QuadraticMap k V k} :
-- imply
  f.Equivalent g ↔ Nonempty (f.IsometryEquiv g) :=
-- proof
  Iff.rfl

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[equivalent_iff_exists_linearEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma equivalent_iff_exists_linearEquiv
  [CommSemiring k]
  [AddCommMonoid V]
  [Module k V]
  {f g : QuadraticMap k V k} :
-- imply
  f.Equivalent g ↔ ∃ T : V ≃ₗ[k] V, ∀ v, g (T v) = f v := by
-- proof
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toLinearEquiv, e.map_app⟩
  · rintro ⟨T, hT⟩
    exact ⟨⟨T, hT⟩⟩

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[isometryEquiv_map_app](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma isometryEquiv_map_app
  [CommSemiring k]
  [AddCommMonoid V]
  [Module k V]
  {f g : QuadraticMap k V k}
  {e : f.IsometryEquiv g}
  {v : V} :
-- imply
  g (e v) = f v :=
-- proof
  e.map_app v

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[equivalent_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma equivalent_refl
  [CommSemiring k]
  [AddCommMonoid V]
  [Module k V]
  {f : QuadraticMap k V k} :
-- imply
  f.Equivalent f :=
-- proof
  Equivalent.refl f

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[equivalent_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma equivalent_symm
  [CommSemiring k]
  [AddCommMonoid V]
  [Module k V]
  {f g : QuadraticMap k V k}
-- given
  (h : f.Equivalent g) :
-- imply
  g.Equivalent f :=
-- proof
  h.symm

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[equivalent_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma equivalent_comm
  [CommSemiring k]
  [AddCommMonoid V]
  [Module k V]
  {f g : QuadraticMap k V k} :
-- imply
  f.Equivalent g ↔ g.Equivalent f :=
-- proof
  ⟨Equivalent.symm, Equivalent.symm⟩

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[equivalent_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma equivalent_trans
  [CommSemiring k]
  [AddCommMonoid V]
  [Module k V]
  {f g h : QuadraticMap k V k}
-- given
  (hfg : f.Equivalent g)
  (hgh : g.Equivalent h) :
-- imply
  f.Equivalent h :=
-- proof
  hfg.trans hgh

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[equivalent_isEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma equivalent_isEquiv
  [CommSemiring k]
  [AddCommMonoid V]
  [Module k V] :
-- imply
  Equivalence (QuadraticMap.Equivalent (R := k) (M₁ := V) (M₂ := V) (N := k)) :=
-- proof
  ⟨Equivalent.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[weightedSumSquares_is_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma weightedSumSquares_is_diagonal
  [Field k]
  {n : ℕ}
  {w : Fin n → k}
  {v : Fin n → k} :
-- imply
  QuadraticMap.weightedSumSquares k w v = ∑ i, w i * (v i * v i) := by
-- proof
  simp [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
section DiagonalizationConstructive
open Module

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[diagonalization_via_orthogonal_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma diagonalization_via_orthogonal_basis
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  {Q : QuadraticForm k V}
  {v : Basis (Fin (finrank k V)) k V}
-- given
  (hv : (QuadraticMap.associated (R := k) Q).IsOrthoᵢ v) :
-- imply
  Q.Equivalent (QuadraticMap.weightedSumSquares k (fun i => Q (v i))) :=
-- proof
  ⟨Q.isometryEquivWeightedSumSquares v hv⟩
section Diagonalization
open Module

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[diagonalization_of_quadratic_forms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma diagonalization_of_quadratic_forms
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {Q : QuadraticForm k V} :
-- imply
  ∃ w : Fin (finrank k V) → k, Q.Equivalent (QuadraticMap.weightedSumSquares k w) :=
-- proof
  Q.equivalent_weightedSumSquares

end QuadraticFormEquiv

namespace QuadraticFormEquiv

/--
[exists_orthogonal_basis_for_quadForm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma exists_orthogonal_basis_for_quadForm
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {Q : QuadraticForm k V} :
-- imply
  ∃ v : Basis (Fin (finrank k V)) k V, (QuadraticMap.associated (R := k) Q).IsOrthoᵢ v :=
-- proof
  LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm k Q)
end QuadraticFormEquiv


namespace QuadraticMap

/--
[Represents.of_isometryEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma Represents.of_isometryEquiv
  [CommSemiring R]
  [AddCommMonoid M₁]
  [AddCommMonoid M₂]
  [Module R M₁]
  [Module R M₂]
  {Q₁ : QuadraticForm R M₁}
  {Q₂ : QuadraticForm R M₂}
  {e : Q₁.IsometryEquiv Q₂}
  {a : R}
-- given
  (h : Q₁.Represents a) :
-- imply
  Q₂.Represents a := by
-- proof
  obtain ⟨v, hv_ne, hv⟩ := h
  refine ⟨e v, ?_, by rw [e.map_app, hv]⟩
  intro h_eq
  exact hv_ne (e.toLinearEquiv.injective (by simp [h_eq]))

end QuadraticMap

namespace QuadraticMap

/--
[represents_iff_of_isometryEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma represents_iff_of_isometryEquiv
  [CommSemiring R]
  [AddCommMonoid M₁]
  [AddCommMonoid M₂]
  [Module R M₁]
  [Module R M₂]
  {Q₁ : QuadraticForm R M₁}
  {Q₂ : QuadraticForm R M₂}
  {e : Q₁.IsometryEquiv Q₂}
  {a : R} :
-- imply
  Q₁.Represents a ↔ Q₂.Represents a :=
-- proof
  ⟨Represents.of_isometryEquiv e, Represents.of_isometryEquiv e.symm⟩

end QuadraticMap

namespace QuadraticMap

/--
[eval_smul_isotropic_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma eval_smul_isotropic_add
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {Q : QuadraticForm k V}
  {v w : V}
  {x : k}
-- given
  (hv : Q v = 0) :
-- imply
  Q (x • v + w) = Q w + x * QuadraticMap.polar (↑Q) v w := by
-- proof
  have h1 := QuadraticMap.map_add (↑Q) (x • v) w
  rw [QuadraticMap.map_smul, hv, smul_zero, zero_add,
    QuadraticMap.polar_smul_left, smul_eq_mul] at h1
  exact h1

end QuadraticMap

namespace QuadraticMap

/--
[nondegenerate_represents_zero_represents_all](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma nondegenerate_represents_zero_represents_all
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {Q : QuadraticForm k V}
-- given
  (hnd : Q.Nondegenerate)
  (hiso : Q.Represents 0) :
-- imply
  ∀ c : k, Q.Represents c := by
-- proof
  intro c
  obtain ⟨v, hv_ne, hv_zero⟩ := hiso
  have hv_not_rad : v ∉ Q.radical := by
    intro hv_rad
    rw [hnd.radical_eq_bot] at hv_rad
    exact hv_ne hv_rad
  have hpol_ne : Q.polarBilin v ≠ 0 :=
    fun hpol => hv_not_rad ⟨hv_zero, hpol⟩
  rw [Ne, LinearMap.ext_iff, not_forall] at hpol_ne
  push Not at hpol_ne
  obtain ⟨w, hw⟩ := hpol_ne
  rw [LinearMap.zero_apply, QuadraticMap.polarBilin_apply_apply] at hw
  by_cases hc : c = 0
  · exact hc ▸ ⟨v, hv_ne, hv_zero⟩
  ·
    let x := (c - Q w) * (QuadraticMap.polar (↑Q) v w)⁻¹
    have heval : Q (x • v + w) = c := by
      rw [eval_smul_isotropic_add Q v w x hv_zero]
      show Q w + (c - Q w) * (QuadraticMap.polar (↑Q) v w)⁻¹ *
        QuadraticMap.polar (↑Q) v w = c
      rw [mul_assoc, inv_mul_cancel₀ hw, mul_one]
      ring
    exact ⟨x • v + w, fun h_eq => hc (by rw [← heval, h_eq, QuadraticMap.map_zero]), heval⟩
end QuadraticMap
namespace QuadraticFormDef93
open LinearMap (BilinMap BilinForm)
section MatrixRank


namespace QuadraticFormDef93

/--
[matrix_fullRank_iff_det_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma matrix_fullRank_iff_det_ne_zero
  [Field k]
  [Fintype n]
  [DecidableEq n]
  [Nonempty n]
  {A : Matrix n n k} :
-- imply
  A.rank = Fintype.card n ↔ A.det ≠ 0 := by
-- proof
  constructor
  · intro hA hdet
    rw [← Matrix.exists_mulVec_eq_zero_iff] at hdet
    obtain ⟨v, hv, hAv⟩ := hdet
    have hrange : A.mulVecLin.range = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [show Module.finrank k A.mulVecLin.range = Fintype.card n from hA,
        Module.finrank_pi k]
    rw [LinearMap.range_eq_top] at hrange
    exact hv ((LinearMap.injective_iff_surjective.mpr hrange)
      (show A.mulVecLin v = A.mulVecLin 0 by simp [hAv]))
  · intro h
    exact Matrix.rank_of_isUnit A
      ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h))

end QuadraticFormDef93

namespace QuadraticFormDef93

/--
[symmetric_dotProduct_zero_implies_mulVec_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma symmetric_dotProduct_zero_implies_mulVec_zero
  [Field k]
  [Fintype n]
  {M : Matrix n n k}
  {x : n → k}
-- given
  (hM : M.IsSymm)
  (h : ∀ y, x ⬝ᵥ (M.mulVec y) = 0) :
-- imply
  M.mulVec x = 0 := by
-- proof
  have h1 : ∀ y, (Matrix.vecMul x M) ⬝ᵥ y = 0 := by
    intro y; rw [← Matrix.dotProduct_mulVec]; exact h y
  have h2 : Matrix.vecMul x M = 0 := dotProduct_eq_zero_iff.mp h1
  rwa [← Matrix.vecMul_transpose M x, hM.eq]

end QuadraticFormDef93

namespace QuadraticFormDef93

/--
[quadraticForm_nondegenerate_iff_det_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma quadraticForm_nondegenerate_iff_det_ne_zero
  [Field k]
  [NeZero (2 : k)]
  [Fintype n]
  [DecidableEq n]
  [Nonempty n]
  {Q : QuadraticForm k (n → k)} :
-- imply
  quadraticFormIsNondegenerate Q ↔ Q.toMatrix'.det ≠ 0 :=
-- proof
  matrix_fullRank_iff_det_ne_zero Q.toMatrix'

end QuadraticFormDef93

namespace QuadraticFormDef93

variable [Field k] [NeZero (2 : k)]
variable [Fintype n] [DecidableEq n]
/--
[toLinearMap₂'_toMatrix'_eq_associated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma toLinearMap₂'_toMatrix'_eq_associated
  (Q : QuadraticForm k (n → k)) :
  (Matrix.toLinearMap₂' k) Q.toMatrix' = QuadraticMap.associated (R := k) Q := by
  unfold QuadraticMap.toMatrix'
  exact (Matrix.toLinearMap₂' k).apply_symm_apply _

end QuadraticFormDef93

namespace QuadraticFormDef93

/--
[matrix_eq_associated_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma matrix_eq_associated_apply
  [Field k]
  [NeZero (2 : k)]
  [Fintype n]
  [DecidableEq n]
  {Q : QuadraticForm k (n → k)}
  {x y : n → k} :
-- imply
  (Matrix.toLinearMap₂' k) Q.toMatrix' x y = (QuadraticMap.associated (R := k) Q) x y := by
-- proof
  rw [toLinearMap₂'_toMatrix'_eq_associated]

end QuadraticFormDef93

namespace QuadraticFormDef93

/--
[nondegenerate_associated_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma nondegenerate_associated_ne_zero
  [Field k]
  [NeZero (2 : k)]
  [Fintype n]
  [DecidableEq n]
  [Nonempty n]
  {Q : QuadraticForm k (n → k)}
  {x : n → k}
-- given
  (hQ : quadraticFormIsNondegenerate Q)
  (hx : x ≠ 0) :
-- imply
  ∃ y : n → k, (QuadraticMap.associated (R := k) Q) x y ≠ 0 := by
-- proof
  by_contra hall
  push Not at hall
  have hmat : ∀ y, x ⬝ᵥ (Q.toMatrix'.mulVec y) = 0 := by
    intro y
    have := hall y
    rw [← matrix_eq_associated_apply] at this
    rwa [Matrix.toLinearMap₂'_apply'] at this
  have hAx : Q.toMatrix'.mulVec x = 0 :=
    symmetric_dotProduct_zero_implies_mulVec_zero Q.toMatrix'
      (QuadraticMap.isSymm_toMatrix' Q) x hmat
  rw [quadraticForm_nondegenerate_iff_det_ne_zero] at hQ
  exact hx (Matrix.eq_zero_of_mulVec_eq_zero hQ hAx)
end QuadraticFormDef93


namespace QuadraticFormDef94

/--
[toSquareClass_sq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma toSquareClass_sq_mul
  {k : Type*}
  [Field k]
  {c a : kˣ} :
-- imply
  toSquareClass k (c ^ 2 * a) = toSquareClass k a := by
-- proof
  show QuotientGroup.mk _ = QuotientGroup.mk _
  rw [show c ^ 2 * a = a * c ^ 2 from mul_comm _ _]
  exact QuotientGroup.mk_mul_of_mem a ⟨c, rfl⟩

end QuadraticFormDef94

namespace QuadraticFormDef94

/--
[linearEquiv_toMatrix'_det_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma linearEquiv_toMatrix'_det_ne_zero
  {k : Type*}
  [Field k]
  [NeZero (2 : k)]
  [Fintype n]
  [DecidableEq n]
  [Field k']
  [Fintype m]
  [DecidableEq m]
  {T : (m → k') ≃ₗ[k'] (m → k')} :
-- imply
  (LinearMap.toMatrix' T.toLinearMap).det ≠ 0 := by
-- proof
  have h : (LinearMap.toMatrix' T.toLinearMap) *
    (LinearMap.toMatrix' T.symm.toLinearMap) = 1 := by
    rw [← LinearMap.toMatrix'_comp]; simp
  exact left_ne_zero_of_mul
    (by rw [← Matrix.det_mul, h, Matrix.det_one]; exact one_ne_zero)

end QuadraticFormDef94

namespace QuadraticFormDef94

/--
[discr_isometryEquiv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma discr_isometryEquiv_eq
  {k : Type*}
  [Field k]
  [NeZero (2 : k)]
  [Fintype n]
  [DecidableEq n]
  {Q₁ Q₂ : QuadraticMap k (n → k) k}
  {e : Q₁.IsometryEquiv Q₂} :
-- imply
  Q₁.discr = (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det * (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det * Q₂.discr := by
-- proof
  have h : Q₁ = Q₂.comp e.toLinearEquiv.toLinearMap := by
    ext v; simp [QuadraticMap.comp_apply, e.map_app v]
  conv_lhs => rw [h]
  exact QuadraticMap.discr_comp _

end QuadraticFormDef94

namespace QuadraticFormDef94

/--
[discriminant_preserved_by_isometryEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
lemma discriminant_preserved_by_isometryEquiv
  {k : Type*}
  [Field k]
  [NeZero (2 : k)]
  [Fintype n]
  [DecidableEq n]
  {Q₁ Q₂ : QuadraticMap k (n → k) k}
  {e : Q₁.IsometryEquiv Q₂}
-- given
  (hQ₁ : Q₁.discr ≠ 0)
  (hQ₂ : Q₂.discr ≠ 0) :
-- imply
  discriminant k Q₁ hQ₁ = discriminant k Q₂ hQ₂ := by
-- proof
  unfold discriminant discrUnit
  have hdet := linearEquiv_toMatrix'_det_ne_zero e.toLinearEquiv
  have heq := discr_isometryEquiv_eq k e
  have : Units.mk0 Q₁.discr hQ₁ =
    (Units.mk0 ((LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det) hdet) ^ 2 *
    Units.mk0 Q₂.discr hQ₂ := by
    ext; simp [heq, sq]
  rw [this]
  exact toSquareClass_sq_mul k _ _

end QuadraticFormDef94

/--
[toMatrix_toLinearMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
private lemma toMatrix_toLinearMap_eq
  [Field k]
  [Fintype n]
  [DecidableEq n]
  {A : Matrix n n k} :
-- imply
  bilinFormToMatrix (matrixBilinEquiv A) = A := by
-- proof
  apply QuadraticFormEquiv.toMatrix_toLinearMap A

/--
[toLinearMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
private lemma toLinearMap_eq
  [Field k]
  [Fintype n]
  [DecidableEq n]
  {B : BilinMap k (n → k) k} :
-- imply
  matrixBilinEquiv (bilinFormToMatrix B) = B := by
-- proof
  apply QuadraticFormEquiv.toLinearMap B

/--
[toLinearMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean)
-/
@[path]
private lemma toLinearMap_eq_2
  [Field k]
  [NeZero (2 : k)]
  [Fintype n]
  [DecidableEq n]
  {Q : QuadraticForm k (n → k)} :
-- imply
  (Matrix.toLinearMap₂' k) Q.toMatrix' = QuadraticMap.associated (R := k) Q := by
-- proof
  apply QuadraticFormDef93.toLinearMap Q


-- created on 2026-10-23
