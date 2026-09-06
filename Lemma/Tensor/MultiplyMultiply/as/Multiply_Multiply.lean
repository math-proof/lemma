import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Vector.Eq.of.Val
import sympy.tensor.multiply
open Tensor Vector


/--
Associativity of `Tensor.multiply`.

Per-axis `lcm` is associative, and wrapping satisfies
`(i % lcm(a,b)) % a = i % a`, so the data is
`A[i%a] * B[i%b] * C[i%c]` in either association.
-/
@[main]
private lemma main
  [Semigroup α]
-- given
  (A : Tensor α s)
  (B : Tensor α s')
  (C : Tensor α s'') :
-- imply
  (A.multiply B).multiply C ≃ A.multiply (B.multiply C) := by
-- proof
  apply SEq.of.SEqDataS.Eq (multiply_shape_assoc s s' s'')
  refine ⟨?_, ?_⟩
  ·
    exact congrArg List.prod (multiply_shape_assoc s s' s'')
  ·
    have hn :
        (multiply_shape (multiply_shape s s') s'').prod =
          (multiply_shape s (multiply_shape s' s'')).prod :=
      congrArg List.prod (multiply_shape_assoc s s' s'')
    have heq :
        ((A.multiply B).multiply C).data =
          cast (congrArg (List.Vector α) hn.symm)
            (A.multiply (B.multiply C)).data := by
      apply Eq.of.Val
      rw [val_cast_vector hn.symm]
      by_cases hz : (multiply_shape (multiply_shape s s') s'').prod = 0
      ·
        rw [val_multiply_zero (A.multiply B) C hz,
          val_multiply_zero A (B.multiply C)
            (by rwa [← multiply_shape_assoc])]
      ·
        have hz' : (multiply_shape s (multiply_shape s' s'')).prod ≠ 0 := by
          rwa [← multiply_shape_assoc]
        have hAB : (multiply_shape s s').prod ≠ 0 := by
          intro h
          exact hz ((multiply_shape_prod_eq_zero_iff _ _).mpr (Or.inl h))
        have hBC : (multiply_shape s' s'').prod ≠ 0 := by
          intro h
          exact hz' ((multiply_shape_prod_eq_zero_iff s (multiply_shape s' s'')).mpr (Or.inr h))
        apply List.ext_getElem
        ·
          rw [show ((A.multiply B).multiply C).data.val.length =
                (multiply_shape (multiply_shape s s') s'').prod
              from ((A.multiply B).multiply C).data.property,
            show (A.multiply (B.multiply C)).data.val.length =
                (multiply_shape s (multiply_shape s' s'')).prod
              from (A.multiply (B.multiply C)).data.property,
            hn]
        ·
          intro i hi₁ hi₂
          have hi : i < (multiply_shape (multiply_shape s s') s'').prod := by
            rw [← ((A.multiply B).multiply C).data.property]
            exact hi₁
          have hi' : i < (multiply_shape s (multiply_shape s' s'')).prod := by
            rw [← (A.multiply (B.multiply C)).data.property]
            exact hi₂
          rw [val_get ((A.multiply B).multiply C).data hi hi₁,
            val_get (A.multiply (B.multiply C)).data hi' hi₂,
            get_multiply (A.multiply B) C hz ⟨i, hi⟩,
            get_multiply A (B.multiply C) hz' ⟨i, hi'⟩]
          have jL :
              wrapFlat
                  (pad1 (multiply_shape s s')
                    ((multiply_shape s s').length ⊔ s''.length))
                  (multiply_shape (multiply_shape s s') s'') i <
                (multiply_shape s s').prod := by
            have := wrapFlat_lt
              (pad1 (multiply_shape s s')
                ((multiply_shape s s').length ⊔ s''.length))
              (multiply_shape (multiply_shape s s') s'')
              (by
                rw [pad1_length _ _ (by
                    rw [multiply_shape_length]
                    exact le_sup_left)]
                exact (multiply_shape_length _ _).symm)
              (by rwa [pad1_prod]) i
            rwa [pad1_prod] at this
          have jR :
              wrapFlat
                  (pad1 (multiply_shape s' s'')
                    (s.length ⊔ (multiply_shape s' s'').length))
                  (multiply_shape s (multiply_shape s' s'')) i <
                (multiply_shape s' s'').prod := by
            have := wrapFlat_lt
              (pad1 (multiply_shape s' s'')
                (s.length ⊔ (multiply_shape s' s'').length))
              (multiply_shape s (multiply_shape s' s''))
              (by
                rw [pad1_length _ _ (by
                    rw [multiply_shape_length]
                    exact le_sup_right)]
                exact (multiply_shape_length _ _).symm)
              (by rwa [pad1_prod]) i
            rwa [pad1_prod] at this
          rw [get_multiply A B hAB ⟨_, jL⟩, get_multiply B C hBC ⟨_, jR⟩]
          rw [_root_.mul_assoc]
          have hA :
              wrapFlat (pad1 s (s.length ⊔ s'.length)) (multiply_shape s s')
                  (wrapFlat
                    (pad1 (multiply_shape s s')
                      ((multiply_shape s s').length ⊔ s''.length))
                    (multiply_shape (multiply_shape s s') s'') i) =
                wrapFlat (pad1 s (s.length ⊔ (multiply_shape s' s'').length))
                  (multiply_shape s (multiply_shape s' s'')) i := by
            rw [wrapFlat_through_multiply s s' s'' i hAB hz,
              wrapFlat_align_left, multiply_shape_assoc]
          have hB :
              wrapFlat (pad1 s' (s.length ⊔ s'.length)) (multiply_shape s s')
                  (wrapFlat
                    (pad1 (multiply_shape s s')
                      ((multiply_shape s s').length ⊔ s''.length))
                    (multiply_shape (multiply_shape s s') s'') i) =
                wrapFlat (pad1 s' (s'.length ⊔ s''.length)) (multiply_shape s' s'')
                  (wrapFlat
                    (pad1 (multiply_shape s' s'')
                      (s.length ⊔ (multiply_shape s' s'').length))
                    (multiply_shape s (multiply_shape s' s'')) i) := by
            rw [wrapFlat_through_multiply' s s' s'' i hAB hz,
              wrapFlat_through_multiply_right s s' s'' i hBC hz',
              multiply_shape_assoc]
          have hC :
              wrapFlat (pad1 s'' ((multiply_shape s s').length ⊔ s''.length))
                  (multiply_shape (multiply_shape s s') s'') i =
                wrapFlat (pad1 s'' (s'.length ⊔ s''.length)) (multiply_shape s' s'')
                  (wrapFlat
                    (pad1 (multiply_shape s' s'')
                      (s.length ⊔ (multiply_shape s' s'').length))
                    (multiply_shape s (multiply_shape s' s'')) i) := by
            rw [wrapFlat_align_right,
              wrapFlat_through_multiply_right' s s' s'' i hBC hz',
              multiply_shape_assoc]
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
      (A.multiply (B.multiply C)).data)


-- created on 2026-09-06
-- updated on 2026-09-06
