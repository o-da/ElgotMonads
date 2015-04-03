(* Auxiliary general purpose lemmas *)

Theorem f_equal1 :
  forall (A B:Type) (f:A -> B) (x y:A), x = y -> f x = f y.
Proof.
  destruct 1; reflexivity.
Qed.
