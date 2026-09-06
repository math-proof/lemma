import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.Eq.of.Val
import sympy.tensor.multiply
open Tensor Vector Nat List.Vector


@[main]
private lemma main
  [CommMagma α]
-- given
  (A : Tensor α s)
  (B : Tensor α s') :
-- imply
  A.multiply B ≃ B.multiply A := by
-- proof
  apply SEq.of.SEqDataS.Eq (multiply_shape_comm s s')
  refine ⟨?_, ?_⟩
  ·
    exact congrArg List.prod (multiply_shape_comm s s')
  ·
    have hn :
        (multiply_shape s s').prod = (multiply_shape s' s).prod :=
      congrArg List.prod (multiply_shape_comm s s')
    have heq :
        (A.multiply B).data =
          cast (congrArg (List.Vector α) hn.symm) (B.multiply A).data := by
      apply Eq.of.Val
      rw [val_cast_vector hn.symm]
      by_cases hz : (multiply_shape s s').prod = 0
      ·
        rw [val_multiply_zero A B hz,
          val_multiply_zero B A (by rwa [← multiply_shape_comm])]
      ·
        have hz' : (multiply_shape s' s).prod ≠ 0 := by
          rwa [← multiply_shape_comm]
        apply List.ext_getElem
        ·
          rw [show (A.multiply B).data.val.length = (multiply_shape s s').prod
              from (A.multiply B).data.property,
            show (B.multiply A).data.val.length = (multiply_shape s' s).prod
              from (B.multiply A).data.property,
            hn]
        ·
          intro i hi₁ hi₂
          have hi : i < (multiply_shape s s').prod := by
            rw [← (A.multiply B).data.property]
            exact hi₁
          have hi' : i < (multiply_shape s' s).prod := by
            rw [← (B.multiply A).data.property]
            exact hi₂
          rw [val_get (A.multiply B).data hi hi₁,
            val_get (B.multiply A).data hi' hi₂,
            get_multiply A B hz ⟨i, hi⟩,
            get_multiply B A hz' ⟨i, hi'⟩]
          have hmax : s.length ⊔ s'.length = s'.length ⊔ s.length := max_comm _ _
          have hout : multiply_shape s s' = multiply_shape s' s :=
            multiply_shape_comm s s'
          simp [hmax, hout]
          exact _root_.mul_comm _ _
    exact heq ▸ (cast_heq (congrArg (List.Vector α) hn.symm) (B.multiply A).data)


-- created on 2026-09-06
-- updated on 2026-09-07
