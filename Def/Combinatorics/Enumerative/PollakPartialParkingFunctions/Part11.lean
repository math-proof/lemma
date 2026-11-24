module
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part11


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/
namespace MetaMathlibExt.PollakPartialParking

/-- Partial parking functions correspond to circle functions leaving the
extra spot empty. -/
def PfEquiv (s t : ℕ) (hst : s ≤ t) :
    {f : Fin s → Fin t // IsPartialParkingFunction s t f} ≃
    {g : Fin s → ZMod (t + 1) // extra t ∈ parkEmpty s t g hst} :=
  { toFun := fun ⟨f, hf⟩ => ⟨lift s t f,
      linSuccess_imp_circle_empty s t f hst
        (threshold_imp_linSuccess s t f hf hst)⟩,
    invFun := fun ⟨g, hg⟩ =>
      let hav : ∀ i, g i ≠ extra t :=
        fun i => circle_empty_avoids s t g hst hg i
      ⟨restrict s t g hav, by
        have hmem : extra t ∈
            parkEmpty s t (lift s t (restrict s t g hav)) hst := by
          have e := lift_restrict s t g hav
          rwa [e]
        have hsucc :=
          circle_empty_imp_linSuccess s t (restrict s t g hav) hst hmem
        exact linSuccess_imp_threshold s t (restrict s t g hav) hsucc⟩,
    left_inv := fun ⟨f, hf⟩ => Subtype.ext (restrict_lift s t f
      (fun i => circle_empty_avoids s t (lift s t f) hst
        (linSuccess_imp_circle_empty s t f hst
          (threshold_imp_linSuccess s t f hf hst)) i)),
    right_inv := fun ⟨g, hg⟩ => Subtype.ext (lift_restrict s t g
      (fun i => circle_empty_avoids s t g hst hg i)) }

end MetaMathlibExt.PollakPartialParking
