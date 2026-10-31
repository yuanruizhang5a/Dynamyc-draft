(* SPDX-License-Identifier: GPL-3.0-only
   Licensed under GNU GPL version 3; https://www.gnu.org/licenses/gpl-3.0.html . See LICENSE at repository root. *)
(** * User-declared, many-sorted vocabularies

    Only symbol equality is decidable. Carriers, functions and Prop-valued
    predicates are supplied separately by a model. No constructor laws or
    decision procedure for semantic equality are implicit in a declaration.
    Formula abbreviations belong to Syntax.v, independently of the signature. *)
From Stdlib Require Import List.

Module Type SINGLE_SORTED_SIGNATURE.
  Parameter function_symbol predicate_symbol : Type.
  Parameter function_eq_dec : forall x y : function_symbol, {x = y} + {x <> y}.
  Parameter predicate_eq_dec : forall x y : predicate_symbol, {x = y} + {x <> y}.
  Parameter function_arity : function_symbol -> nat.
  Parameter predicate_arity : predicate_symbol -> nat.
End SINGLE_SORTED_SIGNATURE.

Module Type SIGNATURE.
  Parameter sort : Type.
  Parameter sort_eq_dec : forall x y : sort, {x = y} + {x <> y}.
  Parameter function_symbol predicate_symbol : Type.
  Parameter function_eq_dec : forall x y : function_symbol, {x = y} + {x <> y}.
  Parameter predicate_eq_dec : forall x y : predicate_symbol, {x = y} + {x <> y}.
  Parameter function_arguments : function_symbol -> list sort.
  Parameter function_result : function_symbol -> sort.
  Parameter predicate_arguments : predicate_symbol -> list sort.
  Definition function_arity f := length (function_arguments f).
  Definition predicate_arity p := length (predicate_arguments p).
End SIGNATURE.

(** A single sort uses the same generalized kernel. *)
Module LiftSingleSorted (S : SINGLE_SORTED_SIGNATURE) <: SIGNATURE.
  Definition sort := unit.
  Definition sort_eq_dec : forall x y : sort, {x=y}+{x<>y}.
  Proof. decide equality. Defined.
  Definition function_symbol := S.function_symbol.
  Definition predicate_symbol := S.predicate_symbol.
  Definition function_eq_dec := S.function_eq_dec.
  Definition predicate_eq_dec := S.predicate_eq_dec.
  Definition function_arguments f := repeat tt (S.function_arity f).
  Definition function_result (_ : function_symbol) := tt.
  Definition predicate_arguments p := repeat tt (S.predicate_arity p).
  Definition function_arity f := length (function_arguments f).
  Definition predicate_arity p := length (predicate_arguments p).
End LiftSingleSorted.
