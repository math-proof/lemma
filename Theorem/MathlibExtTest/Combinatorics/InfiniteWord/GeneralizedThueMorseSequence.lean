/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/GeneralizedThueMorseSequence.lean -/


import Def.Combinatorics.InfiniteWord.GeneralizedThueMorseSequence.Part3
import Lemma.Finset.InfiniteWord.GeneralizedThueMorseSequence


namespace MetaMathlibExt.GeneralizedThueMorse

example : classicalBlock 2 =
    [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2)] := by
  decide

example : List.ofFn
    (fun i : Fin 8 => infLetter 2 2 (by decide) (by decide) classicalKappa i) =
      [(0 : Fin 2), 1, 1, 0, 1, 0, 0, 1] := by
  decide

end MetaMathlibExt.GeneralizedThueMorse
