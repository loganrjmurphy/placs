import Lake
open Lake DSL

package «Assurance» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩
  ]

lean_lib «Assurance»

lean_lib «Var»

lean_lib «SPL»

@[default_target]
lean_lib «Examples» where
leanOptions := #[
  ⟨`pp.unicode.fun, true⟩,
  ⟨`pp.proofs.withType, false⟩
]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
