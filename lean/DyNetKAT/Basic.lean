namespace DyNetKAT

/-- The project name string. -/
def projectName : String := "DyNetKAT"

/-- Proof that the project name is non-empty. -/
theorem projectName_nonempty : projectName ≠ "" := by
  decide

end DyNetKAT
