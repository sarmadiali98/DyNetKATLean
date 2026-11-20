import DyNetKAT.DyNetKAT.AST

namespace DyNetKAT.DyNetKAT

open DyNetKAT.NetKAT

variable {schema : PacketSchema}

/-- Recursive-variable definitions used by the `(cpolX)` rule.

    An optional body keeps lookup total without assuming that every variable is
    defined or that definitions are guarded. -/
abbrev RecEnv (schema : PacketSchema := ctxSchema) : Type := Var → Option (DyNetKAT schema)

/-- Look up the defining body for a recursive variable. -/
def RecEnv.lookup (env : RecEnv schema) (name : Var) : Option (DyNetKAT schema) := env name

/-- The environment with no recursive definitions. -/
abbrev RecEnv.emptyFor (schema : PacketSchema) : RecEnv schema := fun _ => none

/-- The empty environment for the default packet schema. -/
def RecEnv.empty : RecEnv := RecEnv.emptyFor ctxSchema

/-- Add the unique definition for `name`, replacing any previous entry. -/
def RecEnv.define (env : RecEnv schema) (name : Var) (body : DyNetKAT schema) : RecEnv schema :=
  fun candidate => if candidate = name then some body else env candidate

@[simp] theorem RecEnv.lookup_empty (name : Var) :
    RecEnv.empty.lookup name = none := rfl

@[simp] theorem RecEnv.lookup_emptyFor (name : Var) :
    (RecEnv.emptyFor schema).lookup name = none := rfl

@[simp] theorem RecEnv.lookup_define_same (env : RecEnv schema) (name : Var)
    (body : DyNetKAT schema) :
    (env.define name body).lookup name = some body := by
  simp [RecEnv.define, RecEnv.lookup]

theorem RecEnv.lookup_define_other (env : RecEnv schema) (name candidate : Var)
    (body : DyNetKAT schema) (different : candidate ≠ name) :
    (env.define name body).lookup candidate = env.lookup candidate := by
  simp [RecEnv.define, RecEnv.lookup, different]

end DyNetKAT.DyNetKAT
