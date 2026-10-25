import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Def_5_5
open InformationTheory MeasureTheory MeasureTheory.Measure Rigollet Rigollet.Chapter5


namespace Rigollet.Chapter5

/--
[prop_5_6_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Def_5_5.lean)
-/
@[path]
lemma prop_5_6_nonneg
  [MeasurableSpace Omega]
  {P Q : Measure Omega} :
-- imply
  (0 : ENNReal) ≤ klDiv P Q :=
-- proof
  zero_le _

end Rigollet.Chapter5

namespace Rigollet.Chapter5

/--
[prop_5_6_gibbs_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Def_5_5.lean)
-/
@[path]
lemma prop_5_6_gibbs_real
  [MeasurableSpace Omega]
  {P Q : Measure Omega}
  [IsFiniteMeasure P]
  [IsFiniteMeasure Q]
-- given
  (hPQ : P.AbsolutelyContinuous Q)
  (h_int : Integrable (llr P Q) P) :
-- imply
  0 ≤ ∫ x, llr P Q x ∂P + Q.real Set.univ - P.real Set.univ :=
-- proof
  integral_llr_add_sub_measure_univ_nonneg hPQ h_int

end Rigollet.Chapter5

namespace Rigollet.Chapter5

/--
[rnDeriv_prod_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Def_5_5.lean)
-/
@[path]
lemma rnDeriv_prod_eq
  [MeasurableSpace alpha]
  [MeasurableSpace beta]
  {P1 Q1 : Measure alpha}
  {P2 Q2 : Measure beta}
  [SigmaFinite P1]
  [SigmaFinite Q1]
  [SigmaFinite P2]
  [SigmaFinite Q2]
-- given
  (_hac1 : P1.AbsolutelyContinuous Q1)
  (_hac2 : P2.AbsolutelyContinuous Q2) :
-- imply
  (P1.prod P2).rnDeriv (Q1.prod Q2) =ᵐ[Q1.prod Q2] fun x => P1.rnDeriv Q1 x.1 * P2.rnDeriv Q2 x.2 :=
-- proof
InfoTheory.rnDeriv_prod_eq _hac1 _hac2

end Rigollet.Chapter5

namespace Rigollet.Chapter5

/--
[prop_5_6_tensorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Def_5_5.lean)
-/
@[path]
lemma prop_5_6_tensorization
  {_ : MeasurableSpace alpha}
  {_ : MeasurableSpace beta}
  {P1 Q1 : Measure alpha}
  {P2 Q2 : Measure beta}
-- given
  (hP1 : IsProbabilityMeasure P1)
  (hQ1 : IsProbabilityMeasure Q1)
  (hP2 : IsProbabilityMeasure P2)
  (hQ2 : IsProbabilityMeasure Q2)
  (hPQ1 : P1.AbsolutelyContinuous Q1)
  (hPQ2 : P2.AbsolutelyContinuous Q2)
  (h_int1 : Integrable (llr P1 Q1) P1)
  (h_int2 : Integrable (llr P2 Q2) P2) :
-- imply
  klDiv (P1.prod P2) (Q1.prod Q2) = klDiv P1 Q1 + klDiv P2 Q2 := by
-- proof
  haveI := hP1; haveI := hQ1; haveI := hP2; haveI := hQ2
  exact InfoTheory.klDiv_prod_eq hPQ1 hPQ2 h_int1 h_int2

end Rigollet.Chapter5


-- created on 2026-10-23
