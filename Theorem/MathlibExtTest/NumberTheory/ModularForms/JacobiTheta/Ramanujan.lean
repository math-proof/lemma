/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ModularForms/JacobiTheta/Ramanujan.lean -/


import Def.NumberTheory.ModularForms.JacobiTheta.Ramanujan
import Lemma.Nat.ModularForms.JacobiTheta.Ramanujan


namespace MetaMathlibExt

example (a b : ℂ) (n : ℤ) :
    ramanujanThetaTerm a b n =
      a ^ (n * (n + 1) / 2).toNat * b ^ (n * (n - 1) / 2).toNat :=
  rfl

example (a b : ℂ) :
    ramanujanThetaRaw a b = ∑' n : ℤ, ramanujanThetaTerm a b n :=
  rfl

example (a b : ℂ) (h : Summable (ramanujanThetaTerm a b)) :
    ramanujanTheta a b h = ∑' n : ℤ, ramanujanThetaTerm a b n :=
  rfl

example (a b : ℂ) : ramanujanThetaTerm a b 0 = 1 :=
  ramanujanThetaTerm_zero a b

example (a b : ℂ) : ramanujanThetaTerm a b 1 = a :=
  ramanujanThetaTerm_one a b

example (a b : ℂ) : ramanujanThetaTerm a b (-1) = b :=
  ramanujanThetaTerm_neg_one a b

example : ramanujanThetaTerm (2 : ℂ) 3 2 = 24 := by
  simp [ramanujanThetaTerm]
  norm_num

example : ramanujanThetaTerm (2 : ℂ) 3 (-2) = 54 := by
  simp [ramanujanThetaTerm]
  norm_num

example (a b : ℂ) (n : ℤ) :
    ramanujanThetaTerm a b (-n) = ramanujanThetaTerm b a n :=
  ramanujanThetaTerm_neg a b n

example (a b : ℂ) : ramanujanThetaRaw a b = ramanujanThetaRaw b a :=
  ramanujanThetaRaw_symm a b

example (a b : ℂ) :
    Summable (ramanujanThetaTerm a b) ↔ Summable (ramanujanThetaTerm b a) :=
  ramanujanTheta_summable_symm a b

example (a b : ℂ) (h : Summable (ramanujanThetaTerm a b)) :
    ramanujanTheta a b h =
      ramanujanTheta b a ((ramanujanTheta_summable_symm a b).mp h) :=
  ramanujanTheta_symm a b h

example : ¬Summable (ramanujanThetaTerm 1 1) :=
  not_summable_ramanujanThetaTerm_one_one

example : ramanujanThetaRaw 1 1 = 0 :=
  ramanujanThetaRaw_one_one

end MetaMathlibExt
