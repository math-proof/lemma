import Mathlib
import sympy.Basic
import sympy.atlas.Computability.Complexity
open Computability
open MetaMathlibExt
open BitstringEncoding


namespace MetaMathlibExt.BitstringEncoding

/--
[bitDecode_bitEncode](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Computability/Complexity.lean)
-/
@[path]
lemma bitDecode_bitEncode
  [BitstringEncoding α]
  {a : α} :
-- imply
  bitDecode (bitEncode a) = some a :=
-- proof
  toEncoding.decode_encode a

end MetaMathlibExt.BitstringEncoding

/--
[undelimit_delimit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Computability/Complexity.lean)
-/
@[path]
private lemma undelimit_delimit_eq
  {l rest : List Bool} :
-- imply
  undelimit (delimit l ++ rest) = some (l, rest) := by
-- proof
  apply MetaMathlibExt.BitstringEncoding.undelimit_delimit l rest

/--
[length_delimit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Computability/Complexity.lean)
-/
@[path]
private lemma length_delimit_eq
  {l : List Bool} :
-- imply
  (delimit l).length = 2 * l.length + 1 := by
-- proof
  apply MetaMathlibExt.BitstringEncoding.length_delimit l

/--
[length_le_length_flatten_delimit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Computability/Complexity.lean)
-/
@[path]
private lemma length_le_length_flatten_delimit_eq
  {l : List (List Bool)} :
-- imply
  l.length ≤ ((l.map delimit).flatten).length := by
-- proof
  apply MetaMathlibExt.BitstringEncoding.length_le_length_flatten_delimit l

/--
[undelimitBlocks_flatten_delimit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Computability/Complexity.lean)
-/
@[path]
private lemma undelimitBlocks_flatten_delimit_eq
  {l : List (List Bool)} :
-- imply
  undelimitBlocks ((l.map delimit).flatten) = some l := by
-- proof
  apply MetaMathlibExt.BitstringEncoding.undelimitBlocks_flatten_delimit l

/--
[mapM_bitDecode_map_bitEncode](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Computability/Complexity.lean)
-/
@[path]
private lemma mapM_bitDecode_map_bitEncode_eq
  [BitstringEncoding α]
  {l : List α} :
-- imply
  (l.map bitEncode).mapM bitDecode = some l := by
-- proof
  apply MetaMathlibExt.BitstringEncoding.mapM_bitDecode_map_bitEncode l


-- created on 2026-10-20
-- updated on 2026-10-23
