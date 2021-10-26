import topology.algebra.module
import algebra.module.submodule

variables {α β : Type*} [topological_space α]

namespace submonoid

@[to_additive] instance [topological_space α] [monoid α] [has_continuous_mul α] (S : submonoid α) : 
  has_continuous_mul S := 
{ continuous_mul := 
  begin
    rw embedding_subtype_coe.to_inducing.continuous_iff,
    exact (continuous_subtype_coe.comp continuous_fst).mul 
      (continuous_subtype_coe.comp continuous_snd)
  end }

end submonoid

namespace subgroup

@[to_additive] instance [topological_space α] [group α] [topological_group α] (S : subgroup α) : 
  topological_group S := 
{ continuous_inv := 
  begin
    rw embedding_subtype_coe.to_inducing.continuous_iff,
    exact continuous_subtype_coe.inv
  end,
  ..S.to_submonoid.has_continuous_mul }

end subgroup

namespace submodule

instance [topological_space α] [topological_space β] [semiring α] [add_comm_monoid β] 
  [module α β] [has_continuous_smul α β] (S : submodule α β) : 
  has_continuous_smul α S := 
{ continuous_smul :=
  begin
    rw embedding_subtype_coe.to_inducing.continuous_iff,
    exact continuous_fst.smul 
      (continuous_subtype_coe.comp continuous_snd)
  end }

instance [topological_space α] [topological_space β] [ring α] [add_comm_group β] 
  [module α β] [topological_add_group β] (S : submodule α β) : 
  topological_add_group S := 
S.to_add_subgroup.topological_add_group

end submodule