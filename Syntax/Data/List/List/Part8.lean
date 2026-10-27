import Def.Data.List.Slice
import Def.Data.List.List.Part3
open Lean


declare_syntax_cat slice_arg

syntax withoutPosition(term:60) : slice_arg

syntax withoutPosition(term:60) ":" : slice_arg

syntax ":" withoutPosition(term:60) : slice_arg

syntax "::" withoutPosition(term:60) : slice_arg

syntax withoutPosition(term:60) ":" withoutPosition(term:60) : slice_arg

syntax withoutPosition(term:60) ":" withoutPosition(term:60) ":" : slice_arg

syntax ":" withoutPosition(term:60) ":" withoutPosition(term:60) : slice_arg

syntax withoutPosition(term:68) "::" withoutPosition(term:60) : slice_arg

syntax withoutPosition(term:60) ":" withoutPosition(term:60) ":" withoutPosition(term:60) : slice_arg

syntax:max term noWs "[" slice_arg "," slice_arg,+ "]" : term

