/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Data/Finset/PropertyB.lean -/


import Def.Data.Finset.PropertyB


-- The empty family has property B vacuously.
example {α : Type*} : (∅ : Finset (Finset α)).HasPropertyB :=
  ⟨fun _ => 0, fun A h => (Finset.notMem_empty A h).elim⟩

