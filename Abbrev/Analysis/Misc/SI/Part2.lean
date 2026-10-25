import Mathlib
import Theorem.Analysis.Misc.UnitsSystem.Part23
import Mathlib.Algebra.Group.MinimalAxioms
import Instance.Analysis.Misc.SI.Part4


namespace SI

open UnitsSystem

abbrev deca {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ) • q

abbrev hecto {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^2 • q

abbrev kilo {d:Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^3 • q

abbrev mega {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^6 • q

abbrev giga {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^9 • q

abbrev tera {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^12 • q

abbrev peta {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^15 • q

abbrev exa {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^18 • q

noncomputable abbrev deci {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-1:ℤ) • q

noncomputable abbrev centi {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-2:ℤ) • q

noncomputable abbrev milli {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-3:ℤ) • q

noncomputable abbrev micro {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-6:ℤ) • q

noncomputable abbrev nano {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-9:ℤ) • q

noncomputable abbrev pico {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-12:ℤ) • q

noncomputable abbrev femto {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-15:ℤ) • q

noncomputable abbrev atto {d: Dimensions} (q : Scalar d) : Scalar d := (10:ℝ)^(-18:ℤ) • q

abbrev Dimensionless := Scalar (0:Dimensions)

abbrev length_unit :Dimensions := ⟨1, 0, 0, 0, 0, 0, 0⟩

abbrev Length := Scalar length_unit

abbrev meter:Length := StandardUnit _

abbrev mass_unit :Dimensions := ⟨0, 1, 0, 0, 0, 0, 0⟩

abbrev Mass := Scalar mass_unit

abbrev kilogram:Mass := StandardUnit _

noncomputable abbrev gram:Mass := milli kilogram

abbrev time_unit :Dimensions := ⟨0, 0, 1, 0, 0, 0, 0⟩

abbrev Time := Scalar time_unit

abbrev second:Time := StandardUnit _

abbrev minute:Time := 60 • second

abbrev hour:Time := 60 • minute

abbrev day:Time := 24 • hour

abbrev week:Time := 7 • day

abbrev year:Time := (365.25:ℝ) • day -- average year length, accounting for leap years

abbrev current_unit :Dimensions := ⟨0, 0, 0, 1, 0, 0, 0⟩

abbrev Current := Scalar current_unit

abbrev ampere:Current := StandardUnit _

abbrev temperature_unit :Dimensions := ⟨0, 0, 0, 0, 1, 0, 0⟩

abbrev Temperature := Scalar temperature_unit

abbrev kelvin:Temperature := StandardUnit _

abbrev amount_unit :Dimensions := ⟨0, 0, 0, 0, 0, 1, 0⟩

abbrev Amount := Scalar amount_unit

abbrev mole:Amount := StandardUnit _

abbrev intensity_unit :Dimensions := ⟨0, 0, 0, 0, 0, 0, 1⟩

abbrev Intensity := Scalar intensity_unit

abbrev candela:Intensity := StandardUnit _

abbrev speed_unit := length_unit - time_unit

abbrev Speed := Scalar speed_unit

abbrev acceleration_unit := length_unit - (2 • time_unit)

abbrev Acceleration := Scalar acceleration_unit

abbrev momentum_unit := mass_unit + speed_unit

abbrev Momentum := Scalar momentum_unit

abbrev energy_unit := mass_unit + (2 • speed_unit)

abbrev Energy := Scalar energy_unit

abbrev joule:Energy := StandardUnit _

abbrev force_unit := mass_unit + acceleration_unit

abbrev Force := Scalar force_unit

abbrev newton:Force := StandardUnit _

abbrev frequency_unit := -time_unit

abbrev Frequency := Scalar frequency_unit

abbrev hertz:Frequency := StandardUnit _

abbrev pressure_unit := force_unit - (2 • length_unit)

abbrev Pressure := Scalar pressure_unit

abbrev pascal:Pressure := StandardUnit _

abbrev power_unit := energy_unit - time_unit

abbrev Power := Scalar power_unit

abbrev watt:Power := StandardUnit _

abbrev charge_unit := current_unit + time_unit

abbrev Charge := Scalar charge_unit

abbrev coulomb:Charge := StandardUnit _

abbrev voltage_unit := energy_unit - charge_unit

abbrev Voltage := Scalar voltage_unit

abbrev volt:Voltage := StandardUnit _

abbrev capacitance_unit := charge_unit - voltage_unit

abbrev Capacitance := Scalar capacitance_unit

abbrev farad:Capacitance := StandardUnit _

abbrev resistance_unit := voltage_unit - current_unit

abbrev Resistance := Scalar resistance_unit

abbrev ohm:Resistance := StandardUnit _

abbrev inductance_unit := voltage_unit - (2 • current_unit)

abbrev Inductance := Scalar inductance_unit

abbrev henry:Inductance := StandardUnit _

abbrev magnetic_flux_unit := voltage_unit + time_unit

abbrev MagneticFlux := Scalar magnetic_flux_unit

abbrev weber:MagneticFlux := StandardUnit _

abbrev magnetic_flux_density_unit := magnetic_flux_unit - length_unit

abbrev MagneticFluxDensity := Scalar magnetic_flux_density_unit

abbrev tesla:MagneticFluxDensity := StandardUnit _

abbrev c : Speed := 299792458 • StandardUnit _ -- speed of light in vacuum

noncomputable abbrev h : Scalar (energy_unit + time_unit) := (6.62607015 * (10:ℝ)^(-34:ℤ)) • StandardUnit _ -- Planck's constant

noncomputable abbrev e : Charge := (1.602176634 * (10:ℝ)^(-19:ℤ)) • StandardUnit _ -- elementary charge

noncomputable abbrev ε₀ : Capacitance := (8.854187817 * (10:ℝ)^(-12:ℤ)) • StandardUnit _ -- vacuum permittivity

noncomputable abbrev μ₀ : Inductance := (4 * Real.pi * (10:ℝ)^(-7:ℤ)) • StandardUnit _ -- vacuum permeability

noncomputable abbrev g : Acceleration := (9.80665:ℝ) • StandardUnit _ -- standard acceleration of gravity

noncomputable abbrev k : Scalar (energy_unit + temperature_unit) := (1.380649 * (10:ℝ)^(-23:ℤ)) • StandardUnit _ -- Boltzmann constant

noncomputable abbrev N_A : Amount := (6.02214076 * (10:ℝ)^(23:ℤ)) • StandardUnit _ -- Avogadro's number

end SI
