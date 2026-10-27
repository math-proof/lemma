import Mathlib
import Structure.Combinatorics.Tiling.DominoTilings
open Finset BigOperators


namespace DominoTilings

namespace Domino

def cells (d : Domino) : Finset Cell := {d.cell1, d.cell2}


def isHorizontal (d : Domino) : Prop := d.cell1.2 = d.cell2.2


def isVertical (d : Domino) : Prop := d.cell1.1 = d.cell2.1

end Domino
end DominoTilings
