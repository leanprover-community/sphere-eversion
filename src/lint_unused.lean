import main
import local.sphere_eversion
import tactic.find_unused

attribute [main_declaration] Smale Gromov rel_mfld.ample.satisfies_h_principle_with'

attribute [main_declaration]
  immersion_rel_open_ample
  immersion_inclusion_sphere -- do we want to keep this?
  immersion_antipodal_sphere -- do we want to keep this?
  sphere_eversion_of_loc
  satisfied_or_refund -- this is unused, because it just packages up some stuff.
  -- It is referred to in the blueprint

open tactic
setup_tactic_parser

import_private update_unsed_decls_list

/-- In the current project, list all the declaration that are not marked as `@[main_declaration]` and
that are not referenced by such declarations -/
meta def all_unused_in_project (proj_folder : string) : tactic (name_map declaration) := do
  env ← get_env,
  let ds := env.fold native.mk_rb_map
    (λ d s, if env.is_prefix_of_file proj_folder d.to_name && !d.is_auto_or_internal env
      then s.insert d.to_name d else s),
  ls ← ds.keys.mfilter (succeeds ∘ user_attribute.get_param_untyped main_declaration_attr),
  ds ← ls.mfoldl (flip update_unsed_decls_list) ds,
  return ds

meta def lint_unused : tactic unit := do
  str ← get_project_dir `lint_sphere_cmd 9,
  env ← get_env,
  ds ← all_unused_in_project str,
  let d := grouped_by_filename env (ds.map $ λ _, "unused") str.length (print_warnings env ff name.anonymous),
  trace d

#eval lint_unused
