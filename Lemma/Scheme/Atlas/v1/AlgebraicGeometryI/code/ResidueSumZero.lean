import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ResidueSumZero
open AlgebraicGeometry CategoryTheory Polynomial Finset BigOperators HahnSeries Classical ResidueSumZero
open AlgebraicGeometry CategoryTheory Polynomial Finset BigOperators HahnSeries Classical IsDedekindDomain


namespace ResidueSumZero

/--
[laurentResidue_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
lemma laurentResidue_zero
  {k : Type u}
  [Field k] :
-- imply
  laurentResidue (0 : LaurentSeries k) = 0 := by
-- proof
  simp [laurentResidue, HahnSeries.coeff_zero]

end ResidueSumZero

namespace ResidueSumZero

/--
[laurentResidue_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
lemma laurentResidue_sum
  {k : Type u}
  [Field k]
  {s : Finset ι}
  {f : ι → LaurentSeries k} :
-- imply
  laurentResidue (∑ i ∈ s, f i) = ∑ i ∈ s, laurentResidue (f i) := by
-- proof
  simp [laurentResidue, HahnSeries.coeff_sum]

end ResidueSumZero

namespace ResidueSumZero

/--
[laurentResidue_ofPowerSeries](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
lemma laurentResidue_ofPowerSeries
  {k : Type u}
  [Field k]
  {f : PowerSeries k} :
-- imply
  laurentResidue (f : LaurentSeries k) = 0 := by
-- proof
  simp [laurentResidue, PowerSeries.coeff_coe]

end ResidueSumZero

namespace ResidueSumZero

/--
[laurentResidue_simplePole](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
lemma laurentResidue_simplePole
  {k : Type u}
  [Field k]
  {c : k} :
-- imply
  laurentResidue (simplePole c) = c := by
-- proof
  simp [laurentResidue, simplePole]

end ResidueSumZero

namespace ResidueSumZero

/--
[laurentResidue_nonneg_order](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
lemma laurentResidue_nonneg_order
  {k : Type u}
  [Field k]
  {f : LaurentSeries k}
-- given
  (hf : ∀ n : ℤ, n < 0 → f.coeff n = 0) :
-- imply
  laurentResidue f = 0 :=
-- proof
  hf (-1) (by omega)

end ResidueSumZero

namespace ResidueSumZero

/--
[PartialFracDiff.residue_at_pole](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
lemma PartialFracDiff.residue_at_pole
  {k : Type u}
  [Field k]
  {ω : PartialFracDiff k}
  {j : Fin ω.n} :
-- imply
  laurentResidue (ω.localExpansionAtPole j) = ω.c j := by
-- proof
  simp [localExpansionAtPole]

end ResidueSumZero

namespace ResidueSumZero

/--
[PartialFracDiff.residue_at_inf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
lemma PartialFracDiff.residue_at_inf
  {k : Type u}
  [Field k]
  {ω : PartialFracDiff k} :
-- imply
  laurentResidue ω.localExpansionAtInf = -(∑ i, ω.c i) := by
-- proof
  simp [localExpansionAtInf]

end ResidueSumZero

namespace ResidueSumZero

/--
[PartialFracDiff.residue_agrees_with_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
lemma PartialFracDiff.residue_agrees_with_polynomial
  {k : Type u}
  [Field k]
  {ω : PartialFracDiff k}
  {j : Fin ω.n} :
-- imply
  laurentResidue (ω.localExpansionAtPole j) = ResidueSum.residuePartialFrac ω.c ω.a j := by
-- proof
  rw [residue_at_pole, ResidueSum.residue_partial_frac_eq_coeff _ _ _ ω.hdist]

end ResidueSumZero

namespace ResidueSumZero

/--
[residue_sum_zero_P1_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
lemma residue_sum_zero_P1_explicit
  {k : Type u}
  [Field k]
  {ω : PartialFracDiff k} :
-- imply
  (∑ j : Fin ω.n, ω.c j) + (-(∑ j : Fin ω.n, ω.c j)) = 0 :=
-- proof
  add_neg_cancel _

end ResidueSumZero

namespace ResidueSumZero

/--
[residue_sum_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
lemma residue_sum_consistent
  {k : Type u}
  [Field k]
  {C : SmoothProperCurve k}
  {n : ℕ}
  {c a : Fin n → k}
-- given
  (hdist : Function.Injective a) :
-- imply
  (∑ i, ResidueSum.residuePartialFrac c a i) + ResidueSum.residueAtInfPartialFrac c a = 0 :=
-- proof
  ResidueSum.residue_sum_partial_frac c a hdist

end ResidueSumZero

namespace ResidueSumZero

/--
[polynomial_residue_eq_laurent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
lemma polynomial_residue_eq_laurent
  {k : Type u}
  [Field k]
  {C : SmoothProperCurve k}
  {n : ℕ}
  {c a : Fin n → k}
  {j : Fin n}
-- given
  (hdist : Function.Injective a) :
-- imply
  ResidueSum.residuePartialFrac c a j = laurentResidue (simplePole (c j)) := by
-- proof
  rw [ResidueSum.residue_partial_frac_eq_coeff c a j hdist, laurentResidue_simplePole]
end ResidueSumZero


/--
[laurentResidue_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
private lemma laurentResidue_add_eq
  {k : Type u}
  [Field k]
  {f g : LaurentSeries k} :
-- imply
  laurentResidue (f + g) = laurentResidue f + laurentResidue g := by
-- proof
  apply ResidueSumZero.laurentResidue_add f g

/--
[laurentResidue_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSumZero.lean)
-/
@[path]
private lemma laurentResidue_smul_eq
  {k : Type u}
  [Field k]
  {c : k}
  {f : LaurentSeries k} :
-- imply
  laurentResidue (c • f) = c * laurentResidue f := by
-- proof
  apply ResidueSumZero.laurentResidue_smul c f


-- created on 2026-10-23
