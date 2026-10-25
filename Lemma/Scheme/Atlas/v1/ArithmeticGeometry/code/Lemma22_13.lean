import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.Lemma22_13
open FunctionFieldAdeleRing DiscreteValuationFamily
open scoped RestrictedProduct


/--
[weilDifferentials_dim_eq_indexOfSpeciality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma22_13.lean)
-/
@[path]
lemma weilDifferentials_dim_eq_indexOfSpeciality
  [Field F]
  [DecidableEq P]
  {D : P →₀ ℤ} :
-- imply
  (Module.finrank k ↥(weilDifferentials (F := F) (O := O) k (D : P → ℤ)) : ℤ) = adeleIndexOfSpeciality (F := F) (O := O) k D := by
-- proof
  have h_duality := weilDifferentials_finrank_eq (F := F) (O := O) k (D : P → ℤ)
  obtain ⟨_, h_dim⟩ := speciality_eq_adele_quotient_dim (F := F) (O := O) k D
  have h1 : (Module.finrank k ↥(weilDifferentials (F := F) (O := O) k (↑D : P → ℤ)) : ℤ) =
    (Module.finrank k (FunctionFieldAdeleRing F P O ⧸
      (adeleSpace (F := F) (O := O) k (↑D : P → ℤ) ⊔
        principalAdeles (F := F) (O := O) k)) : ℤ) := by
    exact_mod_cast h_duality
  exact h1.trans h_dim


-- created on 2026-10-23
