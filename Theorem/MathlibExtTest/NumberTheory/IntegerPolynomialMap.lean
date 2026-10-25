/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/IntegerPolynomialMap.lean -/


import Def.NumberTheory.IntegerPolynomialMap


namespace MetaMathlibExt

noncomputable example {n m : ℕ} (F : IntegerPolynomialMap n m) (x : Fin n → ℤ) :
    Fin m → ℤ :=
  F.toFun x

noncomputable example {n m p : ℕ} (F : IntegerPolynomialMap n m) (x : Fin n → ZMod p) :
    Fin m → ZMod p :=
  F.toFunReduce p x

noncomputable example {n : ℕ} (F : IntegerPolynomialMap n n) (x : Fin n → ℤ) :
    F.iterate 0 x = x := rfl

noncomputable example {n p : ℕ} (F : IntegerPolynomialMap n n) (x : Fin n → ZMod p) :
    F.iterateReduce p 0 x = x := rfl

#print axioms MetaMathlibExt.IntegerPolynomialMap
#print axioms MetaMathlibExt.IntegerPolynomialMap.toFun
#print axioms MetaMathlibExt.IntegerPolynomialMap.toFunReduce
#print axioms MetaMathlibExt.IntegerPolynomialMap.iterate
#print axioms MetaMathlibExt.IntegerPolynomialMap.iterateReduce

end MetaMathlibExt
