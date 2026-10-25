import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec20SmoothClosedSubvariety
open KaehlerDifferential TensorProduct SmoothClosedSubvariety


namespace SmoothClosedSubvariety

/--
[corollary25_smooth_closed_subvariety_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean)
-/
@[path]
lemma corollary25_smooth_closed_subvariety_criterion
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  [Algebra.FormallySmooth k R] :
-- imply
  Algebra.FormallySmooth k (R ⧸ I) ↔ ∃ l, l ∘ₗ (kerCotangentToTensor k R (R ⧸ I)) = LinearMap.id :=
-- proof
  Algebra.FormallySmooth.iff_split_injection Ideal.Quotient.mk_surjective

end SmoothClosedSubvariety

namespace SmoothClosedSubvariety

/--
[proposition35_conormal_right_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean)
-/
@[path]
lemma proposition35_conormal_right_exact
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R} :
-- imply
  Function.Exact (kerCotangentToTensor k R (R ⧸ I)) (mapBaseChange k R (R ⧸ I)) :=
-- proof
  exact_kerCotangentToTensor_mapBaseChange k R (R ⧸ I) Ideal.Quotient.mk_surjective

end SmoothClosedSubvariety

namespace SmoothClosedSubvariety

/--
[proposition35_conormal_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean)
-/
@[path]
lemma proposition35_conormal_surjective
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R} :
-- imply
  Function.Surjective (mapBaseChange k R (R ⧸ I)) :=
-- proof
  mapBaseChange_surjective k R (R ⧸ I) Ideal.Quotient.mk_surjective

end SmoothClosedSubvariety

namespace SmoothClosedSubvariety

/--
[corollary26_conormal_ses_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean)
-/
@[path]
lemma corollary26_conormal_ses_injective
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  [Algebra.FormallySmooth k R]
  [Algebra.FormallySmooth k (R ⧸ I)] :
-- imply
  Function.Injective (kerCotangentToTensor k R (R ⧸ I)) := by
-- proof
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection
    (R := k) (P := R) (A := R ⧸ I) Ideal.Quotient.mk_surjective).mp inferInstance
  exact Function.HasLeftInverse.injective ⟨l, fun x => LinearMap.ext_iff.mp hl x⟩

end SmoothClosedSubvariety

namespace SmoothClosedSubvariety

/--
[corollary26_conormal_ses_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean)
-/
@[path]
lemma corollary26_conormal_ses_exact
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R} :
-- imply
  Function.Exact (kerCotangentToTensor k R (R ⧸ I)) (mapBaseChange k R (R ⧸ I)) :=
-- proof
  exact_kerCotangentToTensor_mapBaseChange k R (R ⧸ I) Ideal.Quotient.mk_surjective

end SmoothClosedSubvariety

namespace SmoothClosedSubvariety

/--
[corollary26_conormal_ses_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean)
-/
@[path]
lemma corollary26_conormal_ses_surjective
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R} :
-- imply
  Function.Surjective (mapBaseChange k R (R ⧸ I)) :=
-- proof
  mapBaseChange_surjective k R (R ⧸ I) Ideal.Quotient.mk_surjective

end SmoothClosedSubvariety

namespace SmoothClosedSubvariety

/--
[corollary26_conormal_ses_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean)
-/
@[path]
lemma corollary26_conormal_ses_split
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  [Algebra.FormallySmooth k R]
  [Algebra.FormallySmooth k (R ⧸ I)] :
-- imply
  ∃ l, l ∘ₗ (kerCotangentToTensor k R (R ⧸ I)) = LinearMap.id :=
-- proof
  (Algebra.FormallySmooth.iff_split_injection
    (R := k) (P := R) (A := R ⧸ I) Ideal.Quotient.mk_surjective).mp inferInstance

end SmoothClosedSubvariety

namespace SmoothClosedSubvariety

/--
[corollary26_conormal_locally_free_direct_summand](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean)
-/
@[path]
lemma corollary26_conormal_locally_free_direct_summand
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  [Algebra.FormallySmooth k R]
  [Algebra.FormallySmooth k (R ⧸ I)] :
-- imply
  ∃ l, l ∘ₗ (kerCotangentToTensor k R (R ⧸ I)) = LinearMap.id ∧ Function.Injective (kerCotangentToTensor k R (R ⧸ I)) := by
-- proof
  obtain ⟨l, hl⟩ := corollary26_conormal_ses_split k R I
  exact ⟨l, hl, by
    exact Function.HasLeftInverse.injective ⟨l, fun x => LinearMap.ext_iff.mp hl x⟩⟩

end SmoothClosedSubvariety

namespace SmoothClosedSubvariety

/--
[corollary26_canonical_bundle_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean)
-/
@[path]
lemma corollary26_canonical_bundle_formula
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  [Algebra.FormallySmooth k R]
  [Algebra.FormallySmooth k (R ⧸ I)]
  [Nontrivial (R ⧸ I)]
  [Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
  [Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
  [Module.Free (R ⧸ I) (Ω[R ⧸ I⁄k])]
  [Module.Finite (R ⧸ I) (Ω[R ⧸ I⁄k])]
  [Module.Free (R ⧸ I) I.Cotangent]
  [Module.Finite (R ⧸ I) I.Cotangent]
  {d c : ℕ}
-- given
  (hd : Module.finrank (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k]) = d)
  (hc : Module.finrank (R ⧸ I) I.Cotangent = c)
  (hdc : Module.finrank (R ⧸ I) (Ω[R ⧸ I⁄k]) = d - c) :
-- imply
  Nonempty ( ↥(⋀[R ⧸ I]^d ((R ⧸ I) ⊗[R] Ω[R⁄k])) ≃ₗ[R ⧸ I] (↥(⋀[R ⧸ I]^(d - c) (Ω[R ⧸ I⁄k]))) ⊗[R ⧸ I] (↥(⋀[R ⧸ I]^c I.Cotangent))) := by
-- proof
  apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  rw [exteriorPower.finrank_eq (R ⧸ I) d, hd]
  rw [Module.finrank_tensorProduct,
    exteriorPower.finrank_eq (R ⧸ I) (d - c), hdc,
    exteriorPower.finrank_eq (R ⧸ I) c, hc]
  simp [Nat.choose_self]

end SmoothClosedSubvariety

namespace SmoothClosedSubvariety

/--
[corollary26_adjunction_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean)
-/
@[path]
lemma corollary26_adjunction_formula
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  [Algebra.FormallySmooth k R]
  [Algebra.FormallySmooth k (R ⧸ I)]
  [Nontrivial (R ⧸ I)]
  [Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
  [Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
  [Module.Free (R ⧸ I) (Ω[R ⧸ I⁄k])]
  [Module.Finite (R ⧸ I) (Ω[R ⧸ I⁄k])]
  [Module.Free (R ⧸ I) I.Cotangent]
  [Module.Finite (R ⧸ I) I.Cotangent]
  {d : ℕ}
-- given
  (hd : Module.finrank (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k]) = d)
  (hc : Module.finrank (R ⧸ I) I.Cotangent = 1)
  (hdc : Module.finrank (R ⧸ I) (Ω[R ⧸ I⁄k]) = d - 1) :
-- imply
  Nonempty ( ↥(⋀[R ⧸ I]^d ((R ⧸ I) ⊗[R] Ω[R⁄k])) ≃ₗ[R ⧸ I] (↥(⋀[R ⧸ I]^(d - 1) (Ω[R ⧸ I⁄k]))) ⊗[R ⧸ I] (↥(⋀[R ⧸ I]^1 I.Cotangent))) :=
-- proof
  corollary26_canonical_bundle_formula k R I d 1 hd hc hdc

end SmoothClosedSubvariety

namespace SmoothClosedSubvariety

/--
[adjunction_formula_with_twisting](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean)
-/
@[path]
lemma adjunction_formula_with_twisting
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  [Algebra.FormallySmooth k R]
  [Algebra.FormallySmooth k (R ⧸ I)]
  [Nontrivial (R ⧸ I)]
  [Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
  [Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
  [Module.Free (R ⧸ I) (Ω[R ⧸ I⁄k])]
  [Module.Finite (R ⧸ I) (Ω[R ⧸ I⁄k])]
  [Module.Free (R ⧸ I) I.Cotangent]
  [Module.Finite (R ⧸ I) I.Cotangent]
  {d c : ℕ}
-- given
  (hd : Module.finrank (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k]) = d)
  (hc : Module.finrank (R ⧸ I) I.Cotangent = c)
  (hdc : Module.finrank (R ⧸ I) (Ω[R ⧸ I⁄k]) = d - c) :
-- imply
  Nonempty ( ↥(⋀[R ⧸ I]^(d - c) (Ω[R ⧸ I⁄k])) ≃ₗ[R ⧸ I] (↥(⋀[R ⧸ I]^d ((R ⧸ I) ⊗[R] Ω[R⁄k]))) ⊗[R ⧸ I] (↥(⋀[R ⧸ I]^c (NormalModule R I)))) := by
-- proof
  apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  rw [exteriorPower.finrank_eq (R ⧸ I) (d - c), hdc]
  rw [Module.finrank_tensorProduct,
    exteriorPower.finrank_eq (R ⧸ I) d, hd,
    exteriorPower.finrank_eq (R ⧸ I) c]
  rw [show Module.finrank (R ⧸ I) (NormalModule R I) = c from by
    rw [Module.finrank_linearMap_self (R ⧸ I) (R ⧸ I) I.Cotangent, hc]]
  simp [Nat.choose_self]

end SmoothClosedSubvariety

namespace SmoothClosedSubvariety

/--
[adjunction_formula_divisor_twisting](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20SmoothClosedSubvariety.lean)
-/
@[path]
lemma adjunction_formula_divisor_twisting
  {k : Type*}
  [Field k]
  {R : Type*}
  [CommRing R]
  [Algebra k R]
  {I : Ideal R}
  [Algebra.FormallySmooth k R]
  [Algebra.FormallySmooth k (R ⧸ I)]
  [Nontrivial (R ⧸ I)]
  [Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
  [Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k])]
  [Module.Free (R ⧸ I) (Ω[R ⧸ I⁄k])]
  [Module.Finite (R ⧸ I) (Ω[R ⧸ I⁄k])]
  [Module.Free (R ⧸ I) I.Cotangent]
  [Module.Finite (R ⧸ I) I.Cotangent]
  {d : ℕ}
-- given
  (hd : Module.finrank (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄k]) = d)
  (hc : Module.finrank (R ⧸ I) I.Cotangent = 1)
  (hdc : Module.finrank (R ⧸ I) (Ω[R ⧸ I⁄k]) = d - 1) :
-- imply
  Nonempty ( ↥(⋀[R ⧸ I]^(d - 1) (Ω[R ⧸ I⁄k])) ≃ₗ[R ⧸ I] (↥(⋀[R ⧸ I]^d ((R ⧸ I) ⊗[R] Ω[R⁄k]))) ⊗[R ⧸ I] (↥(⋀[R ⧸ I]^1 (NormalModule R I)))) :=
-- proof
  adjunction_formula_with_twisting k R I d 1 hd hc hdc
end SmoothClosedSubvariety



-- created on 2026-10-23
