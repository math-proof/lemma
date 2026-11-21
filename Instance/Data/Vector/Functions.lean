import Abbrev.Analysis.Real.Relational
import Instance.Data.Vector.Vector
import Instance.Analysis.SpecialFunctions.Logarithm
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Def.Data.Vector.Functions
open Vector


namespace List.Vector

instance [Sin α] : Sin (Vector α n) where
  sin := sin

instance [Cos α] : Cos (Vector α n) where
  cos := cos

instance [Cot α] : Cot (Vector α n) where
  cot := cot

instance [Tan α] : Tan (Vector α n) where
  tan := tan

instance [Exp α] : Exp (Vector α n) where
  exp a := a.map Exp.exp
  exp_add x y := by
    ext i
    simp [GetMul.eq.MulGetS.fin]
    rw [GetAdd.eq.AddGetS.fin]
    apply Exp.exp_add
  exp_zero := by
    ext i
    simp [Zero.eq.Replicate]
    simp [One.eq.Replicate]
    apply Exp.exp_zero
  exp_neg x := by
    ext i
    simp [GetInv.eq.InvGet.fin]
    simp [GetNeg.eq.NegGet.fin]
    apply Exp.exp_neg

instance [NeZero n] [ExpNeZero α] : ExpNeZero (Vector α n) where
  exp_ne_zero x := by
    intro h_eq
    let i : Fin n := ⟨0, NeZero.pos n⟩
    apply ExpNeZero.exp_ne_zero (x.get i)
    simpa [Exp.exp, Zero.eq.Replicate, List.Vector.get_replicate] using
      congrArg (fun v : Vector α n => v.get i) h_eq


instance [Log α] : Log (Vector α n) where
  log a := a.map Log.log
  log_zero := by
    ext i
    simp [Zero.eq.Replicate]
    apply Log.log_zero
  log_one := by
    ext i
    simp [One.eq.Replicate]
    simp [EqGet0_0.fin]
    apply Log.log_one
  log_div_self x := by
    ext i
    simp [GetDiv.eq.DivGetS.fin]
    simp [EqGet0_0.fin]
    apply Log.log_div_self

end List.Vector

instance [XEq α] : XEq (List.Vector α n) where
  r a b := ∀ i : Fin n, a[i] ≈ b[i]
  iseqv :=
    {
      refl a i := Setoid.refl a[i]
      symm h i := Setoid.symm (h i)
      trans h_ab h_bc i := Setoid.trans (h_ab i) (h_bc i)
    }
