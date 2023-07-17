import Mathbin.Tactic.Basic

open Lean.Parser Tactic Interactive

/-- Linter for the sphere eversion project. -/
@[user_command]
unsafe def lint_sphere_cmd (_ : parse <| tk "#lint_sphere") : lean.parser Unit := do
  let str ← get_project_dir `lint_sphere_cmd 9
  lint_cmd_aux (@lint_project str "the sphere eversion project")

/- ./././Mathport/Syntax/Translate/Command.lean:583:11: warning: suppressing unsupported reserve notation -/
