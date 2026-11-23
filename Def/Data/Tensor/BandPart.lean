module

public import Def.Data.Tensor.Tril
public import Def.Data.Tensor.Triu
public import Def.Data.Tensor.Inv
public import Def.Data.Tensor.Det

@[expose] public section

open Tensor


/--
dilated version of [band_part](https://tensorflow.google.cn/api_docs/python/tf/linalg/band_part)
-/
def Tensor.band_part [Zero α] (X : Tensor α s) (l : ℕ) (u : ℕ) (d : ℕ := 1) : Tensor α s :=
  ((X.tril u).triu (-l)).masked_fill d (fun Δ d => ¬d ∣ Δ + l)

