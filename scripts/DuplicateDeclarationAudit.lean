/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import RatFuncWittLocalGlobal
import Mathlib.Tactic.DuplicateDecls

/-!
# Duplicate declaration audit

This script asks Mathlib's duplicate-declaration linter to normalize binder
order, binder names, and universe parameters before comparing declarations.
The accompanying Task target filters the report to project declarations.
-/

open Lean Mathlib.Tactic.DuplicateDecls

run_cmd do
  logInfo m!"THEOREMS\n{← Elab.Command.liftCoreM <| lintDuplicateDeclarations .theorems}"
  logInfo m!"INSTANCES\n{← Elab.Command.liftCoreM <| lintDuplicateDeclarations .instances}"
  logInfo m!"DEFINITIONS\n{← Elab.Command.liftCoreM <| lintDuplicateDeclarations .defs}"
