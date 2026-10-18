import DyNetKAT.DyNetKAT.AST

namespace DyNetKAT.DyNetKAT

/-- Recursive-variable definitions used by the `(cpolX)` rule.

    An optional body keeps lookup total without assuming that every variable is
    defined or that definitions are guarded. -/
abbrev RecEnv : Type := Var → Option DyNetKAT

/-- Look up the defining body for a recursive variable. -/
def RecEnv.lookup (env : RecEnv) (name : Var) : Option DyNetKAT := env name

/-- The environment with no recursive definitions. -/
def RecEnv.empty : RecEnv := fun _ => none

/-- Add the unique definition for `name`, replacing any previous entry. -/
def RecEnv.define (env : RecEnv) (name : Var) (body : DyNetKAT) : RecEnv :=
  fun candidate => if candidate = name then some body else env candidate

@[simp] theorem RecEnv.lookup_empty (name : Var) :
    RecEnv.empty.lookup name = none := rfl

@[simp] theorem RecEnv.lookup_define_same (env : RecEnv) (name : Var)
    (body : DyNetKAT) :
    (env.define name body).lookup name = some body := by
  simp [RecEnv.define, RecEnv.lookup]

theorem RecEnv.lookup_define_other (env : RecEnv) (name candidate : Var)
    (body : DyNetKAT) (different : candidate ≠ name) :
    (env.define name body).lookup candidate = env.lookup candidate := by
  simp [RecEnv.define, RecEnv.lookup, different]

end DyNetKAT.DyNetKAT
