/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/


import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part9
import Lemma.Finset.Enumerative.Partition.PeakGeneratingFunction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring


namespace MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction

open MetaMathlibExt

abbrev pgf_testR := PowerSeries (Polynomial ℤ)

abbrev pgf_testK := FractionRing pgf_testR

end MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction
