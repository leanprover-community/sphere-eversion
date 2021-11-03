import tactic.basic

open lean.parser tactic interactive
/-- Linter for the sphere eversion project -/
@[user_command] meta def lint_sphere_cmd (_ : parse $ tk "#lint_sphere") : lean.parser unit :=
do str ← get_project_dir `lint_sphere_cmd 9, lint_cmd_aux (@lint_project str "my project")
reserve notation `#lint_sphere`


