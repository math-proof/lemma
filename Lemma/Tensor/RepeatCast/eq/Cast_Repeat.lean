import Lemma.List.EqSwap_0'1
import Lemma.Tensor.RepeatCast.as.Repeat.of.Eq
open List Tensor


@[main]
private lemma main
-- given
  (B : Tensor α [l, n])
  (m : ℕ) :
-- imply
  let s := ([l, n].swap ([l, n].length - 2) ([l, n].length - 1)).insertIdx 0 1
  let s' := [1, n, l]
  (cast (congrArg (Tensor α) (show s = s' by simp [s, s', EqSwap_0'1])) (Bᵀ.unsqueeze 0)).repeat m (0 : Fin 3) =
    cast (congrArg (Tensor α) (show s.set 0 (m * s[0]'(by grind)) = s'.set 0 (m * s'[0]'(by grind)) by simp [s, s', EqSwap_0'1])) ((Bᵀ.unsqueeze 0).repeat m (0 : Fin 3)) := by
-- proof
  intro s s'
  have h_s : s = s' := by
    simp [s, s', EqSwap_0'1]
  have := RepeatCast.eq.Cast_Repeat.of.Eq h_s (Bᵀ.unsqueeze 0) m ⟨0, by grind⟩
  simp at this
  assumption


-- created on 2026-07-08
