(* Adjust LoadPath for this to work!! *)
Add LoadPath "~/Schreibtisch/svnba/Elgot/Coq".
Require ElgotMonad.

Section proofs.
Context `(C : ElgotMonad).

Ltac elgot_simpl := repeat (
    rewrite -> id_l ||
    rewrite -> id_r ||
    rewrite -> kl1 ||
    rewrite -> kl2 ||
    rewrite -> kl3 ||
    rewrite -> compcpr ||
    rewrite -> inlcpr ||
    rewrite -> inrcpr ||
    rewrite -> mapcomp).

(*
Ltac liftmap := repeat (
    rewrite -> mapcomp ||
    rewrite <- kl3 ||
    rewrite -> comp_assoc ||
    rewrite -> kl2).

Ltac cprs := repeat (
    rewrite -> compcpr ||
    rewrite -> inrcpr ||
    rewrite -> inlcpr ||
    rewrite -> comp_assoc).
*)

Lemma A2 : forall a b c (f: a ~> (T b)) (g: b ~> (T c)),
    g * ∘ f = [ (map (inr ∘ inr)) ∘ f , (map inl) ∘ g ] † ∘ inl.
Proof.
intros.
rewrite <- unfolding.
rewrite <- comp_assoc.
rewrite -> inlcpr.
rewrite -> mapcomp.
rewrite -> comp_assoc.
rewrite <- kl3.
rewrite -> comp_assoc.
rewrite -> kl2.
rewrite -> comp_assoc.
rewrite -> inrcpr.
rewrite <- unfolding.
rewrite <- comp_assoc.
rewrite -> inrcpr.
rewrite -> comp_assoc.
rewrite -> mapcomp.
rewrite <- kl3.
rewrite -> comp_assoc.
rewrite -> kl2.
rewrite -> inlcpr.
rewrite -> kl3.
rewrite <- comp_assoc.
rewrite -> kl1.
rewrite -> id_r.
trivial.
Qed.

End proofs.