import Lake
open Lake DSL

package "JL" where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,            -- pretty-prints `fun a ↦ b`
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, false⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩
  ]

-- Public umbrella library. `import JL` pulls in exactly the model, the analytic hypotheses, the
-- regime tag, and the RoKoko / LNP route statements.
@[default_target]
lean_lib «JL» where

-- Research-facing target statements (`JL/Research/`). Built in CI so it catches API regressions,
-- but excluded from the public umbrella `JL.lean` so downstream `import JL` stays lean.
@[default_target]
lean_lib «JL.Research» where
  roots := #[`JL.Research.Conjecture, `JL.Research.Harness]

-- Concrete-instance examples (`JL/Examples/`). Same reasoning as Research above.
@[default_target]
lean_lib «JL.Examples» where
  roots := #[`JL.Examples.Concrete]

-- `#eval` / `native_decide` smoke tests (`JL/Tests/`) — the only place `native_decide` is allowed.
@[default_target]
lean_lib «JL.Tests» where
  roots := #[`JL.Tests.Smoke]

require "leanprover-community" / mathlib @ git "v4.31.0"
