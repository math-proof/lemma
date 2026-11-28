module

public import Instance.Data.Tensor.Tensor
@[expose] public section

open Tensor


instance [HPow α β α] : HPow (Tensor α s) (Tensor β s) (Tensor α s) where
  hPow A B := A.map₂ HPow.hPow B

instance [HPow α β α] : HPow α (Tensor β s) (Tensor α s) where
  hPow a B := ⟨B.data.map (a ^ ·)⟩

