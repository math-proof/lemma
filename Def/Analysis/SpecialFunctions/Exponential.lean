module

@[expose] public section

open Filter Hyperreal Int


noncomputable def Hyperreal.exp (x : ℝ*) : ℝ* :=
  x.map Real.exp

