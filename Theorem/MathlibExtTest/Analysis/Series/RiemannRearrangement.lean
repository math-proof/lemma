/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Series/RiemannRearrangement.lean -/


import sympy.atlas.Analysis.Series.RiemannRearrangement


namespace MathlibExtTest.Analysis.Series.RiemannRearrangement

open MathlibExt.Analysis.Series.RiemannRearrangementWanted

example : OrderedHasSum (fun _ => 0) 0 := by
  rw [orderedHasSum_iff]
  simp

example (f : ℕ → ℝ) (s : ℝ) (h : OrderedHasSum f s) :
    Filter.Tendsto f Filter.atTop (nhds 0) :=
  orderedHasSum_tendsto_zero f s h

end MathlibExtTest.Analysis.Series.RiemannRearrangement
