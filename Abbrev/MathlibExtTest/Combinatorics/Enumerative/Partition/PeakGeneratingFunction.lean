module
public import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part9
public import Theorem.Finset.Enumerative.Partition.PeakGeneratingFunction
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/
namespace MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction

open MetaMathlibExt

abbrev pgf_testR := PowerSeries (Polynomial ℤ)

abbrev pgf_testK := FractionRing pgf_testR

end MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction
