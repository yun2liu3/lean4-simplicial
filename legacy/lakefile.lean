import Lake
open Lake DSL

package «simplicial» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from ".." / "mathlib4"

@[default_target]
lean_lib «Simplicial» where
  -- srcDir defaults to "."
