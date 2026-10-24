import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_LogDeRhamH1
import Lemma.Int.P2MUtil
open KaehlerDifferential


/--
[AlgebraicCurve_Place_exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {v : AlgebraicCurve.Place K F} :
-- imply
  ∃ π : v.toValuationSubring, Irreducible π ∧
      v.dCoord = KaehlerDifferential.D K F (π : F) ∧
      (∀ (n : ℕ) (ω : Ω[F⁄K]), v.HasPoleOrderLE n ω ↔
        ∃ f : F, (π : F) ^ n * f ∈ v.toValuationSubring ∧ ω = f • v.dCoord) ∧
      (∀ (n : ℕ) (g : F), v.FnPoleOrderLE n g ↔ (π : F) ^ n * g ∈ v.toValuationSubring) ∧
      (∀ (ω : Ω[F⁄K]) (a : K), v.HasLogResidue ω a ↔
        ∃ f : F, ω = f • v.dCoord ∧ v.HasValue ((π : F) * f) a) := by
-- proof
  refine ⟨(IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose,
    (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec,
    rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩


-- created on 2026-10-23
-- updated on 2026-10-24
