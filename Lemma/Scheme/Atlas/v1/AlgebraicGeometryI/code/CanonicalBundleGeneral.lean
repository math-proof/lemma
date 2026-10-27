import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
open KaehlerDifferential Module
open Set


/--
[rank_kahler_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleGeneral.lean)
-/
@[path]
lemma rank_kahler_polynomial
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Module.finrank (MvPolynomial (Fin (n+1)) k) (Ω[MvPolynomial (Fin (n+1)) k⁄k]) = n + 1 := by
-- proof
  rw [Module.finrank_eq_card_basis (mvPolynomialBasis k (Fin (n + 1))), Fintype.card_fin]

/--
[det_kahler_rank_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleGeneral.lean)
-/
@[path]
lemma det_kahler_rank_one
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Module.finrank (MvPolynomial (Fin (n+1)) k) (⋀[MvPolynomial (Fin (n+1)) k]^(n + 1) (Ω[MvPolynomial (Fin (n+1)) k⁄k])) = 1 := by
-- proof
  rw [exteriorPower.finrank_eq, rank_kahler_polynomial, Nat.choose_self]

/--
[exterior_power_kahler_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleGeneral.lean)
-/
@[path]
lemma exterior_power_kahler_rank
  {k : Type u}
  [Field k]
  {n : ℕ}
  {p : ℕ} :
-- imply
  Module.finrank (MvPolynomial (Fin (n+1)) k) (⋀[MvPolynomial (Fin (n+1)) k]^p (Ω[MvPolynomial (Fin (n+1)) k⁄k])) = Nat.choose (n + 1) p := by
-- proof
  rw [exteriorPower.finrank_eq, rank_kahler_polynomial]
section CanonicalBundleIso
open Set
variable (k : Type u) [Field k] (n : ℕ)

/--
[canonical_bundle_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleGeneral.lean)
-/
@[path]
lemma canonical_bundle_free
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Module.Free (MvPolynomial (Fin (n+1)) k) (⋀[MvPolynomial (Fin (n+1)) k]^(n+1) (Ω[MvPolynomial (Fin (n+1)) k⁄k])) :=
-- proof
  inferInstance

/--
[canonical_bundle_free_rank_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleGeneral.lean)
-/
@[path]
lemma canonical_bundle_free_rank_one
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Module.Free (MvPolynomial (Fin (n+1)) k) (⋀[MvPolynomial (Fin (n+1)) k]^(n+1) (Ω[MvPolynomial (Fin (n+1)) k⁄k])) ∧ Module.finrank (MvPolynomial (Fin (n+1)) k) (⋀[MvPolynomial (Fin (n+1)) k]^(n+1) (Ω[MvPolynomial (Fin (n+1)) k⁄k])) = 1 := by
-- proof
  refine ⟨inferInstance, ?_⟩
  rw [exteriorPower.finrank_eq, finrank_eq_card_basis (mvPolynomialBasis k (Fin (n + 1))),
    Fintype.card_fin, Nat.choose_self]
end CanonicalBundleIso


-- created on 2026-10-23
