(** A library for working with partial functions; in particular, providing monadic style programming with them. *)

Require Import UniMath.All.

Section Partial.

  Definition partial (X : UU) : UU
  := { a : hProp & a -> X }.

  Definition make_partial {X} {a : hProp} (f : a -> X) : partial X
  := (a,,f).
 
  Definition is_defined {X} : partial X -> hProp := pr1.
  
  Definition evaluate {X} {x : partial X} : is_defined x -> X := pr2 x.

  (** Would like to call this “return” for monadic programming,
  but Coq has [return] as reserved syntax. *)
  Definition partial_of_total {X} : X -> partial X
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

End Partial.