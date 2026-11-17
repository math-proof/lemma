module

public import Mathlib
public import Structure.RibetLevelLowering_ExchangeData

@[expose] public section

open Module

namespace RibetEndgame


namespace ExchangeData

variable {k : Type} [Field k]

def SeqIso (d : ExchangeData k) : Prop :=
  finrank k d.Yp = finrank k d.Lq

end ExchangeData

end RibetEndgame
