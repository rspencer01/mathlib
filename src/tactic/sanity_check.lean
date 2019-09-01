/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import tactic.core

/-!
# sanity_check command
 This file defines the `#sanity_check` and `#sanity_check_mathlib` commands, to spot common mistakes in the current file or in all of mathlib, respectively.

 Currently this will check for unused arguments in declarations and whether a declaration is incorrectly marked as a def/lemma.

 ## Tags
 sanity check, sanity_check, cleanup, command, tactic
-/

universe variable u
open expr tactic native

reserve notation `#sanity_check`
reserve notation `#sanity_check_mathlib`

setup_tactic_parser

/-- Find all (non-internal) declarations where tac returns `some x` and list them. -/
meta def fold_over_with_cond {α} (tac : declaration → tactic (option α)) :
  tactic (list (declaration × α)) :=
do e ← get_env,
   e.mfold [] $ λ d ds,
     if d.to_name.is_internal || d.is_auto_generated e then return ds else
     do o ← tac d,
     if h : o.is_some then return $ (d, option.get h)::ds else return ds

/-- Find all declarations where tac returns `some x` and sort the resulting list by file name. -/
meta def fold_over_with_cond_sorted {α} (tac : declaration → tactic (option α)) :
  tactic (list (string × list (declaration × α))) :=
do e ← get_env,
   ds ← fold_over_with_cond tac,
   let ds₂ := rb_lmap.of_list (ds.map (λ x, ((e.decl_olean x.1.to_name).iget, x))),
   return $ ds₂.to_list

/-- Make the output of `fold_over_with_cond` printable, in the following form:
      #print <name> <open multiline comment> <elt of α> <close multiline comment> -/
meta def print_decls {α} [has_to_format α] (ds : list (declaration × α)) : format :=
ds.foldl
  (λ f x, f ++ "\n" ++ to_fmt "#print " ++ to_fmt x.1.to_name ++ " /- " ++ to_fmt x.2 ++ " -/")
  format.nil

/-- Make the output of `fold_over_with_cond_sorted` printable, with the file path + name inserted.-/
meta def print_decls_sorted {α} [has_to_format α] (ds : list (string × list (declaration × α))) :
  format :=
ds.foldl
  (λ f x, f ++ "\n" ++ "\n" ++ to_fmt "-- " ++ to_fmt x.1 ++ print_decls x.2)
  format.nil

/- Print all (non-internal) declarations where tac return `some x`-/
meta def print_all_decls {α} [has_to_format α] (tac : declaration → tactic (option α)) :
  tactic format :=
print_decls_sorted <$> fold_over_with_cond_sorted tac

/- Print (non-internal) declarations in the current file where tac return `some x`-/
meta def print_decls_current_file {α} [has_to_format α] (tac : declaration → tactic (option α)) :
  tactic format :=
print_decls <$> fold_over_with_cond
  (λ d, d.in_current_file >>= λ b, if b then tac d else return none)

/- Print (non-internal) declarations in mathlib where tac return `some x` -/
meta def print_decls_mathlib {α} [has_to_format α] (tac : declaration → tactic (option α)) :
  tactic format :=
do ml ← get_mathlib_dir,
   f ← fold_over_with_cond_sorted
   (λ d, is_in_mathlib_aux ml d.to_name >>= λ b,
      if b then tac d else return none),
   return $ print_decls_sorted $ f.map (λ x, ⟨x.1.popn ml.length, x.2⟩)

/-- Auxilliary definition for `check_unused_arguments_aux` -/
meta def check_unused_arguments_aux : list ℕ → ℕ → ℕ → expr → list ℕ | l n n_max e :=
if n > n_max then l else
if ¬is_lambda e ∧ ¬is_pi e then l else
  let b := e.binding_body in
  let l' := if b.has_var_idx 0 then l else n :: l in check_unused_arguments_aux l' (n+1) n_max b

/-- Check which arguments of a declaration are not used.
  Prints a list of natural numbers corresponding to which arguments are not used (e.g.
    this outputs [1, 4] if the first and fourth arguments are unused).
  Checks both the type and the value of `d` for whether the argument is used
  (in rare cases an argument is used in the type but not in the value).
  We return [] if the declaration was automatically generated.
  We print arguments that are larger than the arity of the type of the declaration
  (without unfolding definitions). -/
meta def check_unused_arguments (d : declaration) : option (list ℕ) :=
let l := check_unused_arguments_aux [] 1 d.type.pi_arity d.value in
if l = [] then none else
let l2 := check_unused_arguments_aux [] 1 d.type.pi_arity d.type in
(l.filter $ λ n, n ∈ l2).reverse

/- Check for unused arguments, and print them with their position, variable name, type and whether
  the argument is a duplicate.
  See also `check_unused_arguments`.
  This tactic additionally filters out all unused arguments of type `parse _` -/
meta def prettify_unused_arguments (d : declaration) : tactic (option format) :=
do
  let ns := check_unused_arguments d,
  if ¬ ns.is_some then return none else do
  let ns := ns.iget,
  (ds, _) ← get_pi_binders d.type,
  let ns := ns.map (λ n, (n, (ds.nth $ n - 1).iget)),
  let ns := ns.filter (λ x, x.2.type.get_app_fn ≠ const `interactive.parse []),
  if ns = [] then return none else do
  ds' ← ds.mmap pp,
  ns ← ns.mmap (λ ⟨n, b⟩, (λ s, to_fmt "argument " ++ to_fmt n ++ ": " ++ s ++
    (if ds.countp (λ b', b.type = b'.type) ≥ 2 then " (duplicate)" else "")) <$> pp b),
  return $ some $ ns.to_string_aux tt

/-- Print all declarations with unused arguments -/
meta def get_all_unused_args : tactic unit :=
print_all_decls prettify_unused_arguments >>= trace

/-- Print all declarations in mathlib with unused arguments -/
meta def get_all_unused_args_mathlib : tactic unit :=
print_decls_mathlib prettify_unused_arguments >>= trace

/-- Print all declarations in current file with unused arguments. -/
meta def get_all_unused_args_current_file : tactic unit :=
print_decls_current_file prettify_unused_arguments >>= trace

/-- Checks whether the correct declaration constructor (definition of theorem) by comparing it
  to its sort. Instances will not be printed -/
meta def incorrect_def_lemma (d : declaration) : tactic (option string) :=
do
  e ← get_env,
  expr.sort n ← infer_type d.type,
  let is_def : Prop := d.is_definition,
  if d.is_constant ∨ d.is_axiom ∨ is_def ↔ (n ≠ level.zero)
    then return none
    else is_instance d.to_name >>= λ b, return $
    if b then none
    else if (d.is_definition : bool) then "is a def, should be a lemma/theorem"
    else "is a lemma/theorem, should be a def"

/-- Print all declarations in mathlib incorrectly marked as def/lemma -/
meta def incorrect_def_lemma_mathlib : tactic unit :=
print_decls_mathlib prettify_unused_arguments >>= trace

/-- Checks whether a declaration has a namespace twice consecutively in its name -/
meta def dup_namespace (d : declaration) : tactic (option string) :=
return $ let nm := d.to_name.components in if nm.chain' (≠) then none
  else let s := (nm.find $ λ n, nm.count n ≥ 2).iget.to_string in
  some $ "The namespace " ++ s ++ " is duplicated in the name"


/-- Return the message printed by `#sanity_check`. -/
meta def sanity_check : tactic format :=
do
  let s := to_fmt "/- Note: This command is still in development. -/\n\n",
  f ← print_decls_current_file prettify_unused_arguments,
  let s := s ++ if f.is_nil then "/- OK: No unused arguments in the current file. -/\n\n"
  else to_fmt "/- Unused arguments in the current file: -/" ++ f ++ "\n\n",
  f ← print_decls_current_file incorrect_def_lemma,
  let s := s ++ if f.is_nil then "/- OK: All declarations correctly marked as def/lemma -/\n\n"
  else to_fmt "/- Declarations incorrectly marked as def/lemma: -/" ++ f ++ "\n\n",
  f ← print_decls_current_file dup_namespace,
  let s := s ++ if f.is_nil then "/- OK: No declarations have a duplicate namespace -/\n\n"
  else to_fmt "/- Declarations with a namespace duplicated: -/" ++ f ++ "\n\n",
  return s

/-- The command `#sanity_check` at the bottom of a file will warn you about some common mistakes
  in that file. -/
@[user_command] meta def sanity_check_cmd (_ : parse $ tk "#sanity_check") : parser unit :=
do s ← sanity_check, trace s

/-- The command `#sanity_check_mathlib` checks all of mathlib for certain mistakes. -/
@[user_command] meta def sanity_check_mathlib_cmd (_ : parse $ tk "#sanity_check_mathlib") :
  parser unit :=
do
  trace "/- Note: This command is still in development. -/\n",
  f ← print_decls_mathlib prettify_unused_arguments,
  trace (to_fmt "/- UNUSED ARGUMENTS: -/" ++ f ++ "\n"),
  f ← print_decls_mathlib incorrect_def_lemma,
  trace (to_fmt "/- INCORRECT DEF/LEMMA: -/" ++ f ++ "\n"),
  f ← print_decls_mathlib dup_namespace,
  trace (to_fmt "/- DUPLICATED NAMESPACES IN NAME: -/" ++ f ++ "\n"),
  skip

@[hole_command] meta def sanity_check_hole_cmd : hole_command :=
{ name := "Sanity Check",
  descr := "Sanity check: Find mistakes in current file.",
  action := λ es, do s ← sanity_check, return [(s.to_string,"")] }

-- #sanity_check
-- #sanity_check_mathlib
