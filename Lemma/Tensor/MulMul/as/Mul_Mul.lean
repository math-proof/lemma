import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import torch.Tensor.prod
import Lemma.Vector.Eq.of.Val
import sympy.core.mul
import Lemma.Tensor.MulShape.assoc
import Lemma.Vector.ValCast.eq.Val.of.Eq
import Lemma.Vector.GetVal.eq.Get.of.Lt.Lt
import Lemma.Tensor.ValDataMul.eq.Nil.of.EqProdMulShape_0
import Lemma.Tensor.WrapFlatPad1LeftWrapFlat.eq.WrapFlatPad1.of.NeProdMulShapeMulShape_0.NeProdMulShape_0
import Lemma.Tensor.WrapFlatPad1RightWrapFlat.eq.WrapFlatPad1.of.NeProdMulShapeMulShape_0.NeProdMulShape_0
import Lemma.Tensor.WrapFlatPad1LeftWrapFlat.eq.WrapFlatPad1.of.NeProdMulShape_MulShape_0.NeProdMulShape_0
import Lemma.Tensor.WrapFlatPad1RightWrapFlat.eq.WrapFlatPad1.of.NeProdMulShape_MulShape_0.NeProdMulShape_0
import Lemma.Tensor.WrapFlatPad1Max_LengthMulShape.eq.WrapFlatPad1MaxMax
import Lemma.Tensor.WrapFlatPad1MaxLengthMulShape.eq.WrapFlatPad1MaxMax
open Tensor Vector


/--
Associativity of `Tensor.mul`.

Per-axis `lcm` is associative, and wrapping satisfies
`(i % lcm(a,b)) % a = i % a`, so the data is
`A[i%a] * B[i%b] * C[i%c]` in either association.
-/
@[path]
private lemma main
  [Semigroup α]
-- given
  (A : Tensor α s)
  (B : Tensor α s')
  (C : Tensor α s'') :
-- imply
  (A.mul B).mul C ≃ A.mul (B.mul C) := by
-- proof
  apply SEq.of.SEqDataS.Eq (MulShape.assoc s s' s'')
  refine ⟨?_, ?_⟩
  ·
    exact congrArg List.prod (MulShape.assoc s s' s'')
  ·
    have hn :
        (mul_shape (mul_shape s s') s'').prod =
          (mul_shape s (mul_shape s' s'')).prod :=
      congrArg List.prod (MulShape.assoc s s' s'')
    have heq :
        ((A.mul B).mul C).data =
          cast (congrArg (List.Vector α) hn.symm)
            (A.mul (B.mul C)).data := by
      apply Eq.of.Val
      rw [ValCast.eq.Val.of.Eq hn.symm]
      by_cases hz : (mul_shape (mul_shape s s') s'').prod = 0
      ·
        rw [ValDataMul.eq.Nil.of.EqProdMulShape_0 (A.mul B) C hz,
          ValDataMul.eq.Nil.of.EqProdMulShape_0 A (B.mul C)
            (by rwa [← MulShape.assoc])]
      ·
        have hz' : (mul_shape s (mul_shape s' s'')).prod ≠ 0 := by
          rwa [← MulShape.assoc]
        have hAB : (mul_shape s s').prod ≠ 0 := by
          intro h
          exact hz ((mul_shape_prod_eq_zero_iff _ _).mpr (Or.inl h))
        have hBC : (mul_shape s' s'').prod ≠ 0 := by
          intro h
          exact hz' ((mul_shape_prod_eq_zero_iff s (mul_shape s' s'')).mpr (Or.inr h))
        apply List.ext_getElem
        ·
          rw [show ((A.mul B).mul C).data.val.length =
                (mul_shape (mul_shape s s') s'').prod
              from ((A.mul B).mul C).data.property,
            show (A.mul (B.mul C)).data.val.length =
                (mul_shape s (mul_shape s' s'')).prod
              from (A.mul (B.mul C)).data.property,
            hn]
        ·
          intro i hi₁ hi₂
          have hi : i < (mul_shape (mul_shape s s') s'').prod := by
            rw [← ((A.mul B).mul C).data.property]
            exact hi₁
          have hi' : i < (mul_shape s (mul_shape s' s'')).prod := by
            rw [← (A.mul (B.mul C)).data.property]
            exact hi₂
          rw [GetVal.eq.Get.of.Lt.Lt ((A.mul B).mul C).data hi hi₁,
            GetVal.eq.Get.of.Lt.Lt (A.mul (B.mul C)).data hi' hi₂,
            get_mul (A.mul B) C hz ⟨i, hi⟩,
            get_mul A (B.mul C) hz' ⟨i, hi'⟩]
          have jL :
              wrapFlat
                  (pad1 (mul_shape s s')
                    ((mul_shape s s').length ⊔ s''.length))
                  (mul_shape (mul_shape s s') s'') i <
                (mul_shape s s').prod := by
            have := wrapFlat_lt
              (pad1 (mul_shape s s')
                ((mul_shape s s').length ⊔ s''.length))
              (mul_shape (mul_shape s s') s'')
              (by
                rw [pad1_length _ _ (by
                    rw [mul_shape_length]
                    exact le_sup_left)]
                exact (mul_shape_length _ _).symm)
              (by rwa [pad1_prod]) i
            rwa [pad1_prod] at this
          have jR :
              wrapFlat
                  (pad1 (mul_shape s' s'')
                    (s.length ⊔ (mul_shape s' s'').length))
                  (mul_shape s (mul_shape s' s'')) i <
                (mul_shape s' s'').prod := by
            have := wrapFlat_lt
              (pad1 (mul_shape s' s'')
                (s.length ⊔ (mul_shape s' s'').length))
              (mul_shape s (mul_shape s' s''))
              (by
                rw [pad1_length _ _ (by
                    rw [mul_shape_length]
                    exact le_sup_right)]
                exact (mul_shape_length _ _).symm)
              (by rwa [pad1_prod]) i
            rwa [pad1_prod] at this
          rw [get_mul A B hAB ⟨_, jL⟩, get_mul B C hBC ⟨_, jR⟩]
          rw [_root_.mul_assoc]
          have hA :
              wrapFlat (pad1 s (s.length ⊔ s'.length)) (mul_shape s s')
                  (wrapFlat
                    (pad1 (mul_shape s s')
                      ((mul_shape s s').length ⊔ s''.length))
                    (mul_shape (mul_shape s s') s'') i) =
                wrapFlat (pad1 s (s.length ⊔ (mul_shape s' s'').length))
                  (mul_shape s (mul_shape s' s'')) i := by
            rw [WrapFlatPad1LeftWrapFlat.eq.WrapFlatPad1.of.NeProdMulShapeMulShape_0.NeProdMulShape_0 s s' s'' i hAB hz,
              WrapFlatPad1Max_LengthMulShape.eq.WrapFlatPad1MaxMax, MulShape.assoc]
          have hB :
              wrapFlat (pad1 s' (s.length ⊔ s'.length)) (mul_shape s s')
                  (wrapFlat
                    (pad1 (mul_shape s s')
                      ((mul_shape s s').length ⊔ s''.length))
                    (mul_shape (mul_shape s s') s'') i) =
                wrapFlat (pad1 s' (s'.length ⊔ s''.length)) (mul_shape s' s'')
                  (wrapFlat
                    (pad1 (mul_shape s' s'')
                      (s.length ⊔ (mul_shape s' s'').length))
                    (mul_shape s (mul_shape s' s'')) i) := by
            rw [WrapFlatPad1RightWrapFlat.eq.WrapFlatPad1.of.NeProdMulShapeMulShape_0.NeProdMulShape_0 s s' s'' i hAB hz,
              WrapFlatPad1LeftWrapFlat.eq.WrapFlatPad1.of.NeProdMulShape_MulShape_0.NeProdMulShape_0 s s' s'' i hBC hz',
              MulShape.assoc]
          have hC :
              wrapFlat (pad1 s'' ((mul_shape s s').length ⊔ s''.length))
                  (mul_shape (mul_shape s s') s'') i =
                wrapFlat (pad1 s'' (s'.length ⊔ s''.length)) (mul_shape s' s'')
                  (wrapFlat
                    (pad1 (mul_shape s' s'')
                      (s.length ⊔ (mul_shape s' s'').length))
                    (mul_shape s (mul_shape s' s'')) i) := by
            rw [WrapFlatPad1MaxLengthMulShape.eq.WrapFlatPad1MaxMax,
              WrapFlatPad1RightWrapFlat.eq.WrapFlatPad1.of.NeProdMulShape_MulShape_0.NeProdMulShape_0 s s' s'' i hBC hz',
              MulShape.assoc]
          refine congrArg₂ HMul.hMul ?_ (congrArg₂ HMul.hMul ?_ ?_)
          ·
            apply congrArg
            exact Fin.eq_of_val_eq hA
          ·
            apply congrArg
            exact Fin.eq_of_val_eq hB
          ·
            apply congrArg
            exact Fin.eq_of_val_eq hC
    exact heq ▸ (cast_heq (congrArg (List.Vector α) hn.symm)
      (A.mul (B.mul C)).data)


-- created on 2026-09-06
-- updated on 2026-09-07
