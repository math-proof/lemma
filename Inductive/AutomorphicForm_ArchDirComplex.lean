import Mathlib
set_option autoImplicit false


namespace AutomorphicForm

inductive ArchDirComplex where
  | H : ArchDirComplex
  | E : ArchDirComplex
  | Fm : ArchDirComplex
  | iH : ArchDirComplex
  | iE : ArchDirComplex
  | iFm : ArchDirComplex

end AutomorphicForm
