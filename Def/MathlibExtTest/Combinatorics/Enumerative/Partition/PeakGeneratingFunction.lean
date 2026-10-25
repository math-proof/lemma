/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/


import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part9
import Lemma.Finset.Enumerative.Partition.PeakGeneratingFunction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Abbrev.MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction


namespace MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction

open MetaMathlibExt

noncomputable def pgf_testX : pgf_testK :=
  algebraMap pgf_testR pgf_testK PowerSeries.X

noncomputable def pgf_testQ : pgf_testK :=
  algebraMap pgf_testR pgf_testK (PowerSeries.C Polynomial.X)

noncomputable def pgf_testT : pgf_testK :=
  1 + pgf_testX ^ 2 * (1 - pgf_testQ) / 2

noncomputable def pgf_testPP1 : pgf_testK :=
  algebraMap pgf_testR pgf_testK (PowerSeries.mk (fun n => ∑ w ∈ Finset.univ.filter
    (fun w : Fin n → Fin 1 => IsSurjectiveRestrictedGrowthString w),
    Polynomial.X ^ (Finset.filter
      (fun s : Fin n × Fin n × Fin n =>
        s.1.val + 1 = s.2.1.val ∧ s.2.1.val + 1 = s.2.2.val ∧
        w s.1 < w s.2.1 ∧ w s.2.2 < w s.2.1) Finset.univ).card))

end MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction
