import Lean

/-!
# Axiom audit

Run inside a Lake package, after `lake build`:

```
lake env lean --run ../../scripts/AxiomAudit.lean Abel2018 FeasibleUnivalence
```

The script imports the given root modules and checks **every** declaration (theorems,
definitions, instances, and auxiliary declarations) defined in a module whose name starts with
one of the given prefixes. It exits with a non-zero status if any of them depends on an axiom
other than `propext` and `Quot.sound`. In particular it rejects `sorryAx`, `Classical.choice`,
`Lean.ofReduceBool`, and any custom `axiom`.
-/

open Lean

namespace AxiomAudit

/-- The only axioms permitted in the repository's formal developments. -/
def allowed : List Name := [``propext, ``Quot.sound]

/-- Memoised transitive axiom collection. -/
partial def axiomsOf (env : Environment) (n : Name) :
    StateM (Std.HashMap Name (Array Name)) (Array Name) := do
  if let some r := (← get)[n]? then return r
  -- Placeholder first, so that mutual references terminate.
  modify (·.insert n #[])
  let r ← match env.find? n with
    | none => pure #[]
    | some (.axiomInfo _) => pure #[n]
    | some ci => do
      -- `ConstantInfo.value?` hides theorem and opaque bodies unless `allowOpaque := true`;
      -- an audit that skipped them would be vacuous for every theorem.
      let body? : Option Expr := match ci with
        | .thmInfo v => some v.value
        | .defnInfo v => some v.value
        | .opaqueInfo v => some v.value
        | _ => none
      let refs := ci.type.getUsedConstants ++ (body?.map Expr.getUsedConstants).getD #[]
      let refs := match ci with
        | .inductInfo v => refs ++ v.ctors.toArray
        | .ctorInfo v => refs.push v.induct
        | .recInfo v => refs ++ v.all.toArray
        | _ => refs
      let mut acc : Array Name := #[]
      for c in refs do
        for a in ← axiomsOf env c do
          unless acc.contains a do acc := acc.push a
      pure acc
  modify (·.insert n r)
  return r

end AxiomAudit

open AxiomAudit in
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: lake env lean --run AxiomAudit.lean <RootModule> [<RootModule> ...]"
    return 2
  let roots := args.map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules (roots.toArray.map fun m => { module := m }) {} (trustLevel := 1024)
  let modNames := env.header.moduleNames
  let mut memo : Std.HashMap Name (Array Name) := {}
  let mut bad : Array (Name × Array Name) := #[]
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some mod := modNames[idx.toNat]? | continue
    unless roots.any (·.isPrefixOf mod) do continue
    count := count + 1
    let (axs, memo') := (axiomsOf env n).run memo
    memo := memo'
    let offending := axs.filter (fun a => !allowed.contains a)
    unless offending.isEmpty do bad := bad.push (n, offending)
  if count == 0 then
    IO.eprintln s!"axiom audit: no declarations found under {roots}"
    return 1
  if bad.isEmpty then
    IO.println s!"axiom audit passed: {count} declarations under {roots} use only {allowed}"
    return 0
  IO.eprintln s!"axiom audit FAILED for {bad.size} of {count} declarations under {roots}:"
  for (n, axs) in bad.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.eprintln s!"  {n}: {axs}"
  return 1
