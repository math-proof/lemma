import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import torch.Tensor.prod
import Lemma.Vector.Eq.of.Val
import sympy.core.mul
import Lemma.Tensor.MulShape.comm
import Lemma.Vector.ValCast.eq.Val.of.Eq
import Lemma.Vector.GetVal.eq.Get.of.Lt.Lt
import Lemma.Tensor.ValDataMul.eq.Nil.of.EqProdMulShape_0
open Tensor Vector


@[main]
private lemma main
  [CommMagma α]
-- given
  (A : Tensor α s)
  (B : Tensor α s') :
-- imply
  A.mul B ≃ B.mul A := by
-- proof
  apply SEq.of.SEqDataS.Eq (MulShape.comm s s')
  refine ⟨?_, ?_⟩
  ·
    exact congrArg List.prod (MulShape.comm s s')
  ·
    have hn :
        (mul_shape s s').prod = (mul_shape s' s).prod :=
      congrArg List.prod (MulShape.comm s s')
    have heq :
        (A.mul B).data =
          cast (congrArg (List.Vector α) hn.symm) (B.mul A).data := by
      apply Eq.of.Val
      rw [ValCast.eq.Val.of.Eq hn.symm]
      by_cases hz : (mul_shape s s').prod = 0
      ·
        rw [ValDataMul.eq.Nil.of.EqProdMulShape_0 A B hz,
          ValDataMul.eq.Nil.of.EqProdMulShape_0 B A (by rwa [← MulShape.comm])]
      ·
        have hz' : (mul_shape s' s).prod ≠ 0 := by
          rwa [← MulShape.comm]
        apply List.ext_getElem
        ·
          rw [show (A.mul B).data.val.length = (mul_shape s s').prod
              from (A.mul B).data.property,
            show (B.mul A).data.val.length = (mul_shape s' s).prod
              from (B.mul A).data.property,
            hn]
        ·
          intro i hi₁ hi₂
          have hi : i < (mul_shape s s').prod := by
            rw [← (A.mul B).data.property]
            exact hi₁
          have hi' : i < (mul_shape s' s).prod := by
            rw [← (B.mul A).data.property]
            exact hi₂
          rw [GetVal.eq.Get.of.Lt.Lt (A.mul B).data hi hi₁,
            GetVal.eq.Get.of.Lt.Lt (B.mul A).data hi' hi₂,
            get_mul A B hz ⟨i, hi⟩,
            get_mul B A hz' ⟨i, hi'⟩]
          have hmax : s.length ⊔ s'.length = s'.length ⊔ s.length := max_comm _ _
          have hout : mul_shape s s' = mul_shape s' s :=
            MulShape.comm s s'
          simp [hmax, hout]
          exact _root_.mul_comm _ _
    exact heq ▸ (cast_heq (congrArg (List.Vector α) hn.symm) (B.mul A).data)


-- created on 2026-09-06
-- updated on 2026-09-07
