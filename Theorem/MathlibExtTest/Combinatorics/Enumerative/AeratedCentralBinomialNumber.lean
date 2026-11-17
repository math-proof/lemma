/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/AeratedCentralBinomialNumber.lean -/
module

public import Def.Combinatorics.Enumerative.AeratedCentralBinomialNumber

public section

namespace MetaMathlibExt

example : List.ofFn (fun i : Fin 7 => aeratedCentralBinomialNumber i) =
    [1, 0, 2, 0, 6, 0, 20] := by decide

end MetaMathlibExt
