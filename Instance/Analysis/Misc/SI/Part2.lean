import Mathlib
import Theorem.Analysis.Misc.UnitsSystem.Part23
import Mathlib.Algebra.Group.MinimalAxioms
import Theorem.Analysis.Misc.SI


/-- {given -show (type := "SI_dimensions")}`d₁, d₂`The addition structure here is simple enough that
  one gets a lot of definitional equalities, e.g., between {lean}`d₁+d₂` and {lean}`d₂+d₁` for
  explicit choices of {name}`d₁` and {name}`d₂`, which is convenient as it means we do not need to
  utilize the {name (full := UnitsSystem.Scalar.cast)}`Scalar.cast` operator much. -/
instance SI_dimensions.instAdd : Add SI_dimensions where
  add d₁ d₂ := ⟨d₁.units_length + d₂.units_length,
                d₁.units_mass + d₂.units_mass,
                d₁.units_time + d₂.units_time,
                d₁.units_current + d₂.units_current,
                d₁.units_temperature + d₂.units_temperature,
                d₁.units_amount + d₂.units_amount,
                d₁.units_intensity + d₂.units_intensity
                ⟩

instance SI_dimensions.instNeg : Neg SI_dimensions where
  neg d := ⟨-d.units_length, -d.units_mass, -d.units_time, -d.units_current,
            -d.units_temperature, -d.units_amount, -d.units_intensity⟩

