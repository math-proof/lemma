import Instance.Data.Vector.Vector
import Instance.Analysis.SpecialFunctions.Exponential.Part5
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Theorem.Analysis.Real.Relational
import Def.Data.Vector.Functions.Part2
open Vector


instance [XEq α] : XEq (List.Vector α n) where
  r a b := ∀ i : Fin n, a[i] ≈ b[i]
  iseqv :=
    {
      refl x := by simp
      symm {a b} h := by
        intro i
        specialize h i
        exact h.symm
      trans {a b c} h_ab h_bc:= by
        intro i
        specialize h_ab i
        specialize h_bc i
        exact h_ab.trans h_bc
    }

