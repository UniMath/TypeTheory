(** A library for working with partial functions; in particular, providing monadic style programming with them. *)

Require Import UniMath.All.

Section Partial.

  Definition partial (X : UU) : UU
  := { a : hProp & a -> X }.

  Definition make_partial {X} {a : hProp} (f : a -> X) : partial X
  := (a,,f).
 
  Definition is_defined {X} : partial X -> hProp := pr1.
  
  Definition evaluate {X} {x : partial X} : is_defined x -> X := pr2 x.

  Definition return_partial {X} : X -> partial X
  := fun x => make_partial (fun _ : htrue => x).
  
  Definition multiply_partial {X} (x : partial (partial X)) : partial X
  := make_partial
    (fun ij : total2_hProp
                (fun x_def : is_defined x => is_defined (evaluate x_def))
     => evaluate (pr2 ij)).
  
  Definition fmap_partial {X Y} (f : X -> Y) : partial X -> partial Y
  := fun x => make_partial (fun i : is_defined x => f (evaluate i)).
         
  Definition bind_partial {X Y} (x : partial X) (f : X -> partial Y)
    : partial Y
  := multiply_partial (fmap_partial f x).

  Definition assume_partial {X} (P : hProp) (x : P -> partial X) : partial X.
  Proof.
    exists (total2_hProp (fun (H_P : P) => is_defined (x H_P))).
    intros H. exact (evaluate (pr2 H)).
  Defined.

End Partial.

Ltac get_partial t x := apply (bind_partial t); intros x.
(** [get_partial t x]: like Haskell’s [x <- t]. *)
Ltac destruct_partial x := apply (bind_partial x); clear x; intros x.
(** [destruct_partial]: special case of [get_partial] for variables. *)
Ltac assume_partial p x := apply (assume_partial p); intros x.
