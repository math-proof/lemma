import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part2
open Finset BigOperators


namespace DominoTilings

namespace Domino

instance : DecidablePred isHorizontal := fun d => inferInstanceAs (Decidable (d.cell1.2 = d.cell2.2))

instance : DecidablePred isVertical := fun d => inferInstanceAs (Decidable (d.cell1.1 = d.cell2.1))


end Domino
end DominoTilings
