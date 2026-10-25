import Mathlib
import Lemma.GroupCohomology.RepPi
import Abbrev.GroupCohomology_RepCokernel
import Lemma.NumberField.SIdeleClassModule
import Abbrev.NumberField_ArchimedeanIdeleModule

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

namespace NumberField.SIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

noncomputable abbrev locInf (v : InfinitePlace E) : K →+* (NumberField.ArchIdele.above E K v).Completion := algebraMap K _

abbrev Index : Type := NumberField.FiniteSIdele.Index E S ⊕ InfinitePlace E

end NumberField.SIdele
