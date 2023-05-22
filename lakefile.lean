import Lake
open Lake DSL

package «alg» {
  -- add package configuration options here
}

lean_lib «Alg» {
  -- add library configuration options here
}

@[default_target]
lean_exe «alg» {
  root := `Main
}
