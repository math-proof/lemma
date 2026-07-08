import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.List.EqSwap_0'1
import Lemma.Tensor.RepeatCast.as.Repeat.of.Eq
open List Tensor


@[main]
private lemma main
-- given
  (B : Tensor α [l, n])
  (i : Fin m) :
-- imply
  have h_s₁ : ([n, l].insertIdx 0 1).set 0 (m * ([n, l].insertIdx 0 1)[0]) = [m, n, l] := by
    grind
  have h_s₂ :
    ((([l, n].swap ([l, n].length - 2) ([l, n].length - 1)).insertIdx 0 1).set 0 (m * (([l, n].swap ([l, n].length - 2) ([l, n].length - 1)).insertIdx 0 1)[0])) =
      ([n, l].insertIdx 0 1).set 0 (m * ([n, l].insertIdx 0 1)[0]) := by
    simp [EqSwap_0'1]
  (cast (congrArg (Tensor α) h_s₁) (cast (congrArg (Tensor α) h_s₂) ((Bᵀ.unsqueeze 0).repeat m (0 : Fin 3)))).get i = (cast (congrArg (Tensor α) (by grind)) ((Bᵀ.unsqueeze 0).repeat m (0 : Fin 3))).get ⟨i, by grind⟩ := by
-- proof
  have h_s : (([l, n].swap ([l, n].length - 2) ([l, n].length - 1)).insertIdx 0 1).set 0 (m * (([l, n].swap ([l, n].length - 2) ([l, n].length - 1)).insertIdx 0 1)[0]) =
    (([n, l].insertIdx 0 1).set 0 (m * ([n, l].insertIdx 0 1)[0])) := by
    simp [EqSwap_0'1]
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin
    (s' := [m, n, l])
    (by simp)
    (by grind)
    (cast (congrArg (Tensor α) h_s) ((Bᵀ.unsqueeze 0).repeat m ⟨0, by grind⟩))
    ⟨i, by grind⟩
  simp at this
  grind


-- created on 2026-07-08
