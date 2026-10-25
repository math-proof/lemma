import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.PascalTheorem.Part2
open Polynomial PascalTheoremConics


namespace PascalTheoremConics

/--
[natDegree_triple_linear_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma natDegree_triple_linear_le
  [CommRing R]
  {p₁ p₂ p₃ : Polynomial R}
-- given
  (h₁ : p₁.natDegree ≤ 1)
  (h₂ : p₂.natDegree ≤ 1)
  (h₃ : p₃.natDegree ≤ 1) :
-- imply
  (p₁ * p₂ * p₃).natDegree ≤ 3 :=
-- proof
  calc (p₁ * p₂ * p₃).natDegree
    ≤ (p₁ * p₂).natDegree + p₃.natDegree := natDegree_mul_le
    _ ≤ (p₁.natDegree + p₂.natDegree) + p₃.natDegree :=
      Nat.add_le_add_right natDegree_mul_le _
    _ ≤ 3 := by omega

end PascalTheoremConics

namespace PascalTheoremConics

/--
[eval_cubic_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma eval_cubic_vanish
  [Field k]
  {p r s q u v : Polynomial k}
  {t : k}
  {x : k}
-- given
  (hp : p.eval x = 0)
  (hq : q.eval x = 0) :
-- imply
  (p * r * s - Polynomial.C t * (q * u * v)).eval x = 0 := by
-- proof
  simp [eval_sub, eval_mul, eval_C, hp, hq]

end PascalTheoremConics

namespace PascalTheoremConics

/--
[eval_factor_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma eval_factor_vanish
  [Field k]
  {Q L : Polynomial k}
  {x : k}
-- given
  (hP : (Q * L).eval x = 0)
  (hQ : Q.eval x ≠ 0) :
-- imply
  L.eval x = 0 := by
-- proof
  rw [eval_mul] at hP
  exact (mul_eq_zero.mp hP).resolve_left hQ

end PascalTheoremConics

namespace PascalTheoremConics

/--
[monic_dvd_eq_mul_divByMonic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma monic_dvd_eq_mul_divByMonic
  [Field k]
  {f g : Polynomial k}
-- given
  (hg : g.Monic)
  (h : g ∣ f) :
-- imply
  f = g * (f /ₘ g) := by
-- proof
  obtain ⟨c, rfl⟩ := h
  rw [mul_divByMonic_cancel_left _ hg]

end PascalTheoremConics

namespace PascalTheoremConics

/--
[InscribedHexagon.cubicP_deg_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma InscribedHexagon.cubicP_deg_le
  [Field k]
  {conic : ProjectiveConic k}
-- given
  (hex : InscribedHexagon k conic) :
-- imply
  hex.cubicP.natDegree ≤ 3 := by
-- proof
  unfold cubicP
  have h1 := natDegree_triple_linear_le hex.sideA_deg hex.sideB_deg hex.sideC_deg
  have h2 : (Polynomial.C hex.t * (hex.oppA * hex.oppB * hex.oppC)).natDegree ≤ 3 :=
    calc (Polynomial.C hex.t * (hex.oppA * hex.oppB * hex.oppC)).natDegree
      ≤ (Polynomial.C hex.t).natDegree + (hex.oppA * hex.oppB * hex.oppC).natDegree :=
        natDegree_mul_le
      _ ≤ 0 + 3 := Nat.add_le_add (le_of_eq (natDegree_C hex.t))
        (natDegree_triple_linear_le hex.oppA_deg hex.oppB_deg hex.oppC_deg)
      _ = 3 := by omega
  exact (natDegree_sub_le _ _).trans (max_le h1 h2)

end PascalTheoremConics

namespace PascalTheoremConics

/--
[pascal_divisibility](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma pascal_divisibility
  [Field k]
  {conic : ProjectiveConic k}
-- given
  (hex : InscribedHexagon k conic) :
-- imply
  conic.poly ∣ hex.cubicP :=
-- proof
  conic.irred.dvd_iff_not_isCoprime.mpr hex.not_coprime

end PascalTheoremConics

namespace PascalTheoremConics

/--
[pascal_quotient_is_line](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma pascal_quotient_is_line
  [Field k]
  {conic : ProjectiveConic k}
-- given
  (hex : InscribedHexagon k conic) :
-- imply
  hex.pascalLine.natDegree ≤ 1 := by
-- proof
  unfold InscribedHexagon.pascalLine
  rw [Polynomial.natDegree_divByMonic _ conic.monic, conic.deg]
  have := hex.cubicP_deg_le
  omega

end PascalTheoremConics

namespace PascalTheoremConics

/--
[pascal_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma pascal_factorization
  [Field k]
  {conic : ProjectiveConic k}
-- given
  (hex : InscribedHexagon k conic) :
-- imply
  hex.cubicP = conic.poly * hex.pascalLine := by
-- proof
  unfold InscribedHexagon.pascalLine
  exact monic_dvd_eq_mul_divByMonic _ _ conic.monic (pascal_divisibility hex)

end PascalTheoremConics

namespace PascalTheoremConics

/--
[point_on_line_of_on_cubic_not_on_conic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma point_on_line_of_on_cubic_not_on_conic
  [Field k]
  {conic : ProjectiveConic k}
  {x : k}
-- given
  (hex : InscribedHexagon k conic)
  (hP : hex.cubicP.eval x = 0)
  (hQ : conic.poly.eval x ≠ 0) :
-- imply
  hex.pascalLine.eval x = 0 := by
-- proof
  have hfact := pascal_factorization hex
  rw [hfact] at hP
  exact eval_factor_vanish conic.poly hex.pascalLine x hP hQ

end PascalTheoremConics

namespace PascalTheoremConics

/--
[pascal_collinear_A](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma pascal_collinear_A
  [Field k]
  {conic : ProjectiveConic k}
  {x : k}
-- given
  (hex : InscribedHexagon k conic)
  (h_sideA : hex.sideA.eval x = 0)
  (h_oppA : hex.oppA.eval x = 0)
  (h_not_on_conic : conic.poly.eval x ≠ 0) :
-- imply
  hex.pascalLine.eval x = 0 := by
-- proof
  apply point_on_line_of_on_cubic_not_on_conic hex x _ h_not_on_conic
  exact eval_cubic_vanish hex.sideA hex.sideB hex.sideC hex.oppA hex.oppB hex.oppC hex.t x
    h_sideA h_oppA

end PascalTheoremConics

namespace PascalTheoremConics

/--
[pascal_collinear_B](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma pascal_collinear_B
  [Field k]
  {conic : ProjectiveConic k}
  {x : k}
-- given
  (hex : InscribedHexagon k conic)
  (h_sideB : hex.sideB.eval x = 0)
  (h_oppB : hex.oppB.eval x = 0)
  (h_not_on_conic : conic.poly.eval x ≠ 0) :
-- imply
  hex.pascalLine.eval x = 0 := by
-- proof
  apply point_on_line_of_on_cubic_not_on_conic hex x _ h_not_on_conic
  unfold InscribedHexagon.cubicP
  simp [eval_sub, eval_mul, eval_C, h_sideB, h_oppB]

end PascalTheoremConics

namespace PascalTheoremConics

/--
[pascal_collinear_C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma pascal_collinear_C
  [Field k]
  {conic : ProjectiveConic k}
  {x : k}
-- given
  (hex : InscribedHexagon k conic)
  (h_sideC : hex.sideC.eval x = 0)
  (h_oppC : hex.oppC.eval x = 0)
  (h_not_on_conic : conic.poly.eval x ≠ 0) :
-- imply
  hex.pascalLine.eval x = 0 := by
-- proof
  apply point_on_line_of_on_cubic_not_on_conic hex x _ h_not_on_conic
  unfold InscribedHexagon.cubicP
  simp [eval_sub, eval_mul, eval_C, h_sideC, h_oppC]

end PascalTheoremConics

namespace PascalTheoremConics

/--
[pascal_theorem_conics](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalTheorem.lean)
-/
@[path]
lemma pascal_theorem_conics
  [Field k]
  {conic : ProjectiveConic k}
  {xA xB xC : k}
-- given
  (hex : InscribedHexagon k conic)
  (hA_side : hex.sideA.eval xA = 0)
  (hA_opp : hex.oppA.eval xA = 0)
  (hB_side : hex.sideB.eval xB = 0)
  (hB_opp : hex.oppB.eval xB = 0)
  (hC_side : hex.sideC.eval xC = 0)
  (hC_opp : hex.oppC.eval xC = 0)
  (hA_conic : conic.poly.eval xA ≠ 0)
  (hB_conic : conic.poly.eval xB ≠ 0)
  (hC_conic : conic.poly.eval xC ≠ 0) :
-- imply
  hex.pascalLine.eval xA = 0 ∧ hex.pascalLine.eval xB = 0 ∧ hex.pascalLine.eval xC = 0 ∧ hex.pascalLine.natDegree ≤ 1 :=
-- proof
  ⟨pascal_collinear_A hex xA hA_side hA_opp hA_conic,
    pascal_collinear_B hex xB hB_side hB_opp hB_conic,
    pascal_collinear_C hex xC hC_side hC_opp hC_conic,
    pascal_quotient_is_line hex⟩

end PascalTheoremConics


-- created on 2026-10-23
