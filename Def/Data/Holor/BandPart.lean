import Def.Data.Holor.Tril
import Def.Data.Holor.Triu
import Def.Data.Holor.Inv
import Def.Data.Holor.Det
open Tensor


/--
dilated version of [band_part](https://tensorflow.google.cn/api_docs/python/tf/linalg/band_part)
-/
def Tensor.band_part [Zero α] (X : Tensor α s) (l : ℕ) (u : ℕ) (d : ℕ := 1) : Tensor α s :=
  ((X.tril u).triu (-l)).masked_fill d (fun Δ d => ¬d ∣ Δ + l)

