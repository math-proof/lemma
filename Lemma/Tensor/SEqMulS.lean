import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.Eq.of.Val
import sympy.core.mul
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
  apply SEq.of.SEqDataS.Eq (mul_shape_comm s s')
  refine ⟨?_, ?_⟩
  ·
    exact congrArg List.prod (mul_shape_comm s s')
  ·
    have hn :
        (mul_shape s s').prod = (mul_shape s' s).prod :=
      congrArg List.prod (mul_shape_comm s s')
    have heq :
        (A.mul B).data =
          cast (congrArg (List.Vector α) hn.symm) (B.mul A).data := by
      apply Eq.of.Val
      rw [val_cast_vector hn.symm]
      by_cases hz : (mul_shape s s').prod = 0
      ·
        rw [val_mul_zero A B hz,
          val_mul_zero B A (by rwa [← mul_shape_comm])]
      ·
        have hz' : (mul_shape s' s).prod ≠ 0 := by
          rwa [← mul_shape_comm]
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
          rw [val_get (A.mul B).data hi hi₁,
            val_get (B.mul A).data hi' hi₂,
            get_mul A B hz ⟨i, hi⟩,
            get_mul B A hz' ⟨i, hi'⟩]
          have hmax : s.length ⊔ s'.length = s'.length ⊔ s.length := max_comm _ _
          have hout : mul_shape s s' = mul_shape s' s :=
            mul_shape_comm s s'
          simp [hmax, hout]
          exact _root_.mul_comm _ _
    exact heq ▸ (cast_heq (congrArg (List.Vector α) hn.symm) (B.mul A).data)


-- created on 2026-09-06
-- updated on 2026-09-07
