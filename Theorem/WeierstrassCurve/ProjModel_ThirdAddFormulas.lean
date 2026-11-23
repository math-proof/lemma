module

public import Theorem.WeierstrassCurve.ProjModel_AddFormulas
public import Notation.WeierstrassCurve_ProjModel_ThirdAddFormulas

public noncomputable section

set_option Elab.async false

section MEGA_KwLRThirdAddFormulas_lean
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial WeierstrassCurve

namespace WeierstrassProjModel

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open scoped WeierstrassCurve_ProjModel_ThirdAddFormulas


public theorem kw_lrThird_X_isHomogeneous : (kw_lrThird_X W).IsHomogeneous 4 := by
  unfold kw_lrThird_X
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)


public theorem kw_lrThird_Y_isHomogeneous : (kw_lrThird_Y W).IsHomogeneous 4 := by
  unfold kw_lrThird_Y
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)


public theorem kw_lrThird_Z_isHomogeneous : (kw_lrThird_Z W).IsHomogeneous 4 := by
  unfold kw_lrThird_Z
  repeat' first
    | with_reducible apply IsHomogeneous.add
    | with_reducible exact isHomogeneous_C _ _
    | with_reducible refine IsHomogeneous.mul ?_ (isHomogeneous_X _ _)
    | with_reducible refine IsHomogeneous.mul ?_ ((isHomogeneous_X _ _).pow _)

section Minors


public theorem kw_lrThird_minor_XZ :
    kw_lrThird_X W * kw_lrAdd_Z W - kw_lrThird_Z W * kw_lrAdd_X W
      = kw_lrThird_pXZ W * WP₁ + kw_lrThird_qXZ W * WP₂ := by
  simp only [kw_lrThird_X, kw_lrThird_Z, kw_lrThird_pXZ, kw_lrThird_qXZ,
    kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z,
    kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    kw_lrAdd_WP₁, kw_lrAdd_WP₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, rename_X, rename_C,
    MvPolynomial.algebraMap_eq]
  ring


public theorem kw_lrThird_minor_XZ_mem_span :
    kw_lrThird_X W * kw_lrAdd_Z W - kw_lrThird_Z W * kw_lrAdd_X W
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrThird_minor_XZ]
  exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))


public theorem kw_lrThird_minor_YZ :
    kw_lrThird_Y W * kw_lrAdd_Z W - kw_lrThird_Z W * kw_lrAdd_Y W
      = kw_lrThird_pYZ W * WP₁ + kw_lrThird_qYZ W * WP₂ := by
  simp only [kw_lrThird_Y, kw_lrThird_Z, kw_lrThird_pYZ, kw_lrThird_qYZ,
    kw_lrAdd_X, kw_lrAdd_Y, kw_lrAdd_Z,
    kw_lrAdd_starX, kw_lrAdd_starY, kw_lrAdd_starZ, kw_lrAdd_c₂₁, kw_lrAdd_c₁₂,
    kw_lrAdd_WP₁, kw_lrAdd_WP₂,
    WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, rename_X, rename_C,
    MvPolynomial.algebraMap_eq]
  ring


public theorem kw_lrThird_minor_YZ_mem_span :
    kw_lrThird_Y W * kw_lrAdd_Z W - kw_lrThird_Z W * kw_lrAdd_Y W
      ∈ Ideal.span {WP₁, WP₂} := by
  rw [kw_lrThird_minor_YZ]
  exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

end Minors

section Diag


public theorem kw_lrThird_X_diag : δ (kw_lrThird_X W) = kw_lrSym_dblX W := by
  simp only [kw_lrThird_X, kw_lrSym_dblX,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
    aeval_X, aeval_C, Sum.elim_inl, Sum.elim_inr, MvPolynomial.algebraMap_eq]
  ring


public theorem kw_lrThird_Y_diag : δ (kw_lrThird_Y W) = kw_lrSym_dblY W := by
  simp only [kw_lrThird_Y, kw_lrSym_dblY,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
    aeval_X, aeval_C, Sum.elim_inl, Sum.elim_inr, MvPolynomial.algebraMap_eq]
  ring


public theorem kw_lrThird_Z_diag : δ (kw_lrThird_Z W) = kw_lrSym_dblZ W := by
  simp only [kw_lrThird_Z, kw_lrSym_dblZ,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
    aeval_X, aeval_C, Sum.elim_inl, Sum.elim_inr, MvPolynomial.algebraMap_eq]
  ring

end Diag

end WeierstrassProjModel

end

end MEGA_KwLRThirdAddFormulas_lean
