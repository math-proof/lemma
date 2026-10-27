import Lemma.Hyperreal.UFn.of.All_UFn
import Lemma.Int.Abs.eq.Max_Neg
open Filter Hyperreal Int


noncomputable def Hyperreal.exp (x : ℝ*) : ℝ* :=
  x.map Real.exp

