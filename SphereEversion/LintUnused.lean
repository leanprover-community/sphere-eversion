import Project.Main
import Project.Local.SphereEversion
import Mathbin.Tactic.FindUnused

attribute [main_declaration] Smale Gromov RelMfld.Ample.satisfies_h_principle_with'

attribute [main_declaration] immersionRel_open_ample immersion_inclusion_sphere
  immersion_antipodal_sphere sphere_eversion_of_loc satisfied_or_refund

-- do we want to keep this?
-- do we want to keep this?
-- this is unused, because it just packages up some stuff.
-- It is referred to in the blueprint
open Tactic

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/- ./././Mathport/Syntax/Translate/Command.lean:735:43: in import_private #[[ident update_unsed_decls_list, [command <some 5>]]]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: too many args -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `exprupdate_unsed_decls_list -/
/--
In the current project, list all the declaration that are not marked as `@[main_declaration]` and
that are not referenced by such declarations -/
unsafe def all_unused_in_project (proj_folder : String) : tactic (name_map declaration) := do
  let env ← get_env
  let ds :=
    env.fold native.mk_rb_map fun d s =>
      if env.is_prefix_of_file proj_folder d.to_name && !d.is_auto_or_internal env then
        s.insert d.to_name d
      else s
  let ls ← ds.keys.filterM (succeeds ∘ user_attribute.get_param_untyped main_declaration_attr)
  let ds ← ls.foldlM (flip (exprupdate_unsed_decls_list)) ds
  return ds

unsafe def lint_unused : tactic Unit := do
  let str ← get_project_dir `lint_sphere_cmd 9
  let env ← get_env
  let ds ← all_unused_in_project str
  let d :=
    grouped_by_filename env (ds.map fun _ => "unused") str.length
      (print_warnings env false Name.anonymous)
  trace d

-- #eval lint_unused
