import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Theorem22_11
open FunctionFieldAdeleRing DiscreteValuationFamily
open scoped RestrictedProduct


/--
[exists_defect_eq_genus_ax'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem22_11.lean)
-/
@[path]
lemma exists_defect_eq_genus_ax'
  [Field F]
  [DecidableEq P]
  [Field F]
  [DecidableEq P]
  {O : P → ValuationSubring F}
  {k : Type*}
  [Field k]
  [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  [HasResidueFieldSurjection P F k O] :
-- imply
  ∃ (D₀ : P →₀ ℤ), riemannDefect (F := F) (O := O) k D₀ = (genusVal_ax (F := F) (O := O) k : ℤ) - 1 :=
-- proof
  genus_attained_ax k

/--
[exists_maximal_defect](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem22_11.lean)
-/
@[path]
lemma exists_maximal_defect
  [Field F]
  [DecidableEq P]
  {D : P →₀ ℤ} :
-- imply
  ∃ (D' : P →₀ ℤ), (∀ p, D p ≤ D' p) ∧ riemannDefect (F := F) (O := O) k D' = (genusVal_ax (F := F) (O := O) k : ℤ) - 1 := by
-- proof
  obtain ⟨D₀, hD₀⟩ := exists_defect_eq_genus_ax' (F := F) (O := O) k
  refine ⟨D ⊔ D₀, le_sup_left (a := D) (b := D₀), ?_⟩
  apply le_antisymm
  · exact riemannDefect_le_of_genus (F := F) (O := O) k (D ⊔ D₀)
  · rw [← hD₀]
    exact riemannDefect_mono k
      D₀ (D ⊔ D₀) (le_sup_right (a := D) (b := D₀))

/--
[speciality_eq_adele_quotient_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem22_11.lean)
-/
@[path]
lemma speciality_eq_adele_quotient_dim
  [Field F]
  [DecidableEq P]
  {D : P →₀ ℤ} :
-- imply
  FiniteDimensional k (FunctionFieldAdeleRing F P O ⧸ AF_subspace (F := F) (O := O) k (D : P → ℤ)) ∧ (Module.finrank k (FunctionFieldAdeleRing F P O ⧸ AF_subspace (F := F) (O := O) k (D : P → ℤ)) : ℤ) = adeleIndexOfSpeciality (F := F) (O := O) k D := by
-- proof
  obtain ⟨D', hD'_ge, hrD'⟩ := exists_maximal_defect (F := F) (O := O) k D
  have hAF_top : AF_subspace (F := F) (O := O) k (D' : P → ℤ) = ⊤ :=
    AF_subspace_eq_top k D' hrD'
  have h_dim := AF_subspace_dim (F := F) (O := O) k D D' hD'_ge
  obtain ⟨hFD, h_dim_eq⟩ := h_dim
  haveI := hFD
  set S := AF_subspace (F := F) (O := O) k (D : P → ℤ) with hS_def
  set T := AF_subspace (F := F) (O := O) k (D' : P → ℤ) with hT_def
  have h_le : S ≤ T := AF_subspace_mono k hD'_ge
  let qe := quotientTopEquiv S T hAF_top h_le
  constructor
  ·
    exact Module.Finite.equiv qe
  ·
    have h_rank : Module.finrank k (FunctionFieldAdeleRing F P O ⧸ S) =
      Module.finrank k (↥T ⧸ Submodule.comap T.subtype S) :=
      (LinearEquiv.finrank_eq qe).symm
    push_cast [h_rank]
    rw [h_dim_eq, hrD']
    unfold adeleIndexOfSpeciality
    ring


-- created on 2026-10-23
