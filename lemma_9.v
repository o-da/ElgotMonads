Add LoadPath "~/Schreibtisch/svnba/Elgot/Coq/".
Require Import ElgotMonad.
Require Import Lemmas_ElgotMonad.
Require Import CofreeElgotMonad.
Require Import Lemmas_CofreeElgotMonad.
Require Import Coq_Steroids.
Require Import Setoid.
Open Scope elgot_scope.

Section ContextCofreeElgotMonad.
Context `(C: CofreeElgotMonad).

Parameter a b : Obj.

(* --- *)

Theorem proving_kl1 : forall (x : Obj), 
(ηv (x:=x) (a:=a) (b:=b)) § = id.
Proof.
intros.
symmetry.
apply lifting2.
rewrite -> id_l.
rewrite -> out_unitcofree.
rewrite -> exphom_id.
rewrite -> prodhom_id.
rewrite -> id_l.
rewrite <- f_cpr.
rewrite -> inl_inr_is_id.
rewrite -> id_l.
rewrite -> kl1.
rewrite -> id_r.
reflexivity.
Qed.


Theorem proving_kl2 : forall (x y : Obj) (f: x ~> coext T a b y), 
f § ∘ ηv (x:=x) = f.
Proof.
intros.
apply out_cong.
rewrite -> comp_assoc.
rewrite -> lifting1.
rewrite <- comp_assoc.

(* since the introduction of cont, this doesn't work anymore TODO *)
Admitted.
(*
rewrite -> out_unitcofree.
rewrite -> comp_assoc.
rewrite -> kl2.
rewrite -> cpr_inl.
reflexivity.
Qed.
*)


Theorem proving_kl3 : forall (x y z : Obj) (f : y ~> coext T a b z) (g : x ~> coext T a b y),
(f § ∘ g) § = f § ∘ g §.
Proof.
intros.
symmetry.
apply lifting2.
rewrite -> comp_assoc.
rewrite -> lifting1.
rewrite <- comp_assoc.
(* since the introduction of cont, this doesn't work anymore TODO *)
Admitted.
(*
rewrite -> lifting1.
rewrite -> comp_assoc with (h':=out).
rewrite -> lifting1.

rewrite -> comp_assoc with (f':=out).
apply f_equal2; trivial.
rewrite <- kl3.
apply f_equal1.

rewrite -> f_cpr.
rewrite <- comp_assoc with (f':=id ×× lifting_cofree g ^^ id).
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite -> comp_assoc with (g':=inr).
rewrite -> cpr_inr.
rewrite <- comp_assoc with (f':=id ×× lifting_cofree g ^^ id).
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
rewrite -> comp_assoc with (f':=g).
reflexivity.
Qed.
*)

(* additional lemmas based on proving_kl1-3 *)

Lemma mapcofree : forall (x y : Obj) (f:x ~> y),
map_cofree f = (ηv (a:=a) (b:=b) ∘ f) §.
Proof.
intros.
(* TODO *)
Admitted.

Lemma liftingcofree_mapcofree : forall 
(x y z : Obj) (f: y ~> coext T a b z) (g: x ~> y),
f § ∘ map_cofree g = (f ∘ g) §.
Proof.
intros.
rewrite -> mapcofree.
rewrite <- proving_kl3.
rewrite -> comp_assoc.
rewrite -> proving_kl2.
reflexivity.
Qed.

(* --- *)

Theorem proving_unfolding : forall x y (f : x ~> (coext T a b (y ⊕ x))),
[ηv , iter_cofree f] § ∘ f = iter_cofree f.
Proof.
intros.
symmetry.

rewrite -> unfolding_triangular1 at 1.
unfold triangular.

rewrite <- comp_assoc with (h':=tuo).
rewrite -> comp_assoc with (g':=tuo).
rewrite -> liftingcofree_tuo.

rewrite -> comp_assoc with (g':=map (inl ⊕⊕ id)).
rewrite <- comp_assoc with (h':=tuo).
rewrite -> lifting_map.
rewrite -> cpr_coprodhom.
rewrite -> cpr_inl.
rewrite -> id_l.

rewrite <- unfolding.

rewrite <- comp_assoc with (h':=tuo).
rewrite -> comp_assoc with (g':=(([η, ((map ([inl ⊕⊕ id, inl ∘ inr]) ∘ out) ∘ f) †]) *)).
rewrite <- kl3.
rewrite -> f_cpr.
rewrite -> kl2.
(* since the introduction of cont, this doesn't work anymore TODO *)
Admitted.
(*
rewrite <- out_itercofree.

rewrite <- comp_assoc with (g':=out).
rewrite -> comp_assoc with (g':=map ([inl ⊕⊕ id, inl ∘ inr])).
rewrite -> lifting_map.
rewrite -> f_cpr.
rewrite -> cpr_coprodhom.
rewrite -> cpr_inl.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite -> cpr_inr.

rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite <- liftingcofree_tuo.
rewrite <- comp_assoc with (g':=tuo).
rewrite -> tuo_out_is_id.
rewrite -> id_l.
reflexivity.
Qed.
*)

(* --- *)


Lemma proving_naturality_h1 : forall x y z (h: x ~> coext T a b (y ⊕ x)) (g: y ~> coext T a b z),
guarded h ->  
  guarded ([map_cofree inl ∘ g, ηv ∘ inr] § ∘ h).
Proof.
intros.
unfold guarded in H.
inversion H as [u' H1].

unfold guarded.

exists ([map (id ⊕⊕ id ×× map_cofree inl ^^ id) ∘ out ∘ g, η ∘ inr ∘ id ×× ([map_cofree inl ∘ g, ηv ∘ inr]) § ^^ id] * ∘ u').
rewrite -> comp_assoc.
rewrite -> lifting1.

rewrite <- comp_assoc.
(* since the introduction of cont, this doesn't work anymore TODO *)
Admitted.
(*
rewrite -> H1.

rewrite -> comp_assoc with (f':=u').
rewrite -> lifting_map.
rewrite -> cpr_coprodhom.
rewrite <- comp_assoc with (f':=inl).
rewrite -> cpr_inl.
rewrite -> id_l.
rewrite -> comp_assoc.
rewrite -> out_mapcofree.

rewrite -> comp_assoc with (f':=u').
apply f_equal2; trivial.
rewrite -> map_lifting.
apply f_equal1.

rewrite -> f_cpr.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> map_comp.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> id_r.
rewrite <- comp_assoc with (h':=η).
rewrite <- comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite <- comp_assoc with (h':=η).
rewrite -> comp_assoc with (h':=inl ⊕⊕ id).
rewrite -> coprodhom_inr.
rewrite -> id_l.
reflexivity.
Qed.
*)


Theorem proving_naturality_h2 : forall x y z (f : x ~> (coext T a b (y ⊕ x)))(g : y ~> (coext T a b z)),
▷(([map_cofree inl ∘ g, ηv ∘ inr]) § ∘ f) =
(([map_cofree inl ∘ g, ηv ∘ inr]) § ∘ ▷f).
Proof.
intros.
unfold triangular.
apply out_cong.

rewrite ->3 comp_assoc.
rewrite -> out_tuo_is_id.
rewrite -> id_r.
rewrite <- comp_assoc with (g':=out).
rewrite -> comp_assoc with (h':=out).
rewrite -> lifting1.
rewrite <- comp_assoc with (h':=tuo).
rewrite -> comp_assoc with (g':=tuo).
rewrite <- comp_assoc with (g':=out).
(* since the introduction of cont, this doesn't work anymore TODO *)
Admitted.
(*
rewrite -> out_tuo_is_id.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=map (inl ⊕⊕ id)).
rewrite -> lifting_map.
rewrite -> cpr_coprodhom.
rewrite <- comp_assoc with (f':=inl).
rewrite -> cpr_inl.
rewrite -> id_l.

unfold map at 1.
rewrite ->2 naturality.
apply f_equal1.
rewrite ->5 comp_assoc.
rewrite -> kl2.
apply f_equal2;trivial.
rewrite -> comp_assoc with (f':=out).
apply f_equal2;trivial.

rewrite ->2 lifting_map.
rewrite <- kl3.
apply f_equal1.

case_distinction.

rewrite -> cpr_coprodhom.
rewrite <- comp_assoc with (f':=inl).
rewrite -> cpr_inl.
rewrite -> id_l.
rewrite -> f_cpr with (h:=ηv ∘ inr).
rewrite ->2 comp_assoc with (h':=out).
rewrite -> out_mapcofree.
rewrite -> out_unitcofree.
rewrite -> f_cpr with (h:=(η ∘ inl) ∘ inr).
rewrite <-2 comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite <- comp_assoc with (f':=inl ∘ inr).
rewrite ->2 comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite -> comp_assoc with (g':=inl ⊕⊕ id).
rewrite -> cpr_coprodhom.
rewrite -> id_l.
rewrite -> cpr_inr.

rewrite ->2 comp_assoc.
rewrite -> lifting_map.
rewrite <- comp_assoc with (g':=[inl ⊕⊕ id, inl ∘ inr]).
rewrite -> cpr_coprodhom.
rewrite -> coprodhom_inl.

case_distinction.
rewrite -> comp_assoc with (f':=g).
apply f_equal2;trivial.
rewrite -> comp_assoc with (f':=out).
apply f_equal2;trivial.
rewrite -> f_cpr.
rewrite -> comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite <- comp_assoc with (f':=inl).
rewrite -> coprodhom_inl.
rewrite <- comp_assoc with (h':=inl).
rewrite ->2 comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite -> comp_assoc with (g':=inr).
rewrite <- comp_assoc with (g':=inl ⊕⊕ id).
rewrite -> coprodhom_inr.
rewrite -> id_l.
rewrite -> lifting_map.
unfold coprodhom.
rewrite -> f_cpr.
rewrite ->2 comp_assoc.
trivial.

trivial.


rewrite -> comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite <- comp_assoc with (f':=inr).
rewrite -> cpr_inr.
rewrite <-2 comp_assoc with (h':=η).
rewrite ->2 comp_assoc with (g':=η).
rewrite ->2 kl2.
rewrite -> comp_assoc with (g':=inr).
rewrite <- comp_assoc with (f':=inr).
rewrite -> cpr_inr.
rewrite -> comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite <-2 comp_assoc with (f':=inr).
rewrite -> coprodhom_inr.
rewrite -> id_l.
rewrite ->2 comp_assoc.
trivial.
Qed.
*)

Theorem proving_naturality : forall x y z (f : x ~> (coext T a b (y ⊕ x)))(g : y ~> (coext T a b z)), 
    g § ∘ iter_cofree f = iter_cofree ([(ηv ∘ inl) § ∘ g  , ηv ∘ inr] § ∘ f).
Proof. 
intros.
rewrite <- mapcofree.

rewrite -> itercofree_triangular.
symmetry.
rewrite -> itercofree_triangular.

rewrite -> proving_naturality_h2.

symmetry.

apply unfolding_guarded2.

apply proving_naturality_h1.

apply guardedtriangular_def.

rewrite -> comp_assoc.
rewrite <- proving_kl3.
rewrite -> f_cpr.
rewrite -> comp_assoc.
rewrite -> liftingcofree_mapcofree.
rewrite -> cpr_inl.
rewrite -> proving_kl1.
rewrite -> id_r.
rewrite -> comp_assoc.
rewrite -> proving_kl2.
rewrite -> cpr_inr.
rewrite <- proving_unfolding at 1.
rewrite -> comp_assoc.
rewrite <- proving_kl3.
rewrite -> f_cpr.
rewrite -> proving_kl2.
reflexivity.

Qed.



(* --- *)

Theorem proving_dinaturality : forall x y z (g: x ~> (coext T a b (y ⊕ z))) (h : z ~> (coext T a b (y ⊕ x))),
    iter_cofree ([ηv ∘ inl , h] § ∘ g) =
    [ ηv , iter_cofree ([ηv ∘ inl , g] § ∘ h) ] § ∘ g.
Proof.
intros.
set (s:=[ ηv ∘ inl , h ] § ∘ g).
set (t:=[ ηv ∘ inl , g ] § ∘ h).
set (w:=[ ηv, iter_cofree t] § ∘ g).

assert (H0: [ηv, w] § ∘ ▷ s = [ηv, iter_cofree t] § ∘ [ ηv ∘ inl , ▷ t] § ∘ g).
set (p:=(map ((id (a:=y) ⊕⊕ id (a:=a) ×× [ηv ∘ inl, h] § ^^ id (a:=b)) ⊕⊕ id (a:=z)))).
set (q:=(map ((id (a:=y) ⊕⊕ id (a:=a) ×× [ηv ∘ inl, g] § ^^ id (a:=b)) ⊕⊕ id (a:=x)))).

assert (Hp: ((map ([inl ⊕⊕ id, inl ∘ inr])) ∘ out ∘ s) † = 
              ([η ∘ inl, (map ([inl ⊕⊕ id, inl ∘ inr])) ∘ out ∘ h] * ∘ 
              p ∘ (map ([inl ⊕⊕ id, inl ∘ inr])) ∘ out ∘ g) †).
apply f_equal1.
unfold s.
rewrite -> comp_assoc.
apply f_equal2;trivial.
rewrite <- comp_assoc.
rewrite -> lifting1.
rewrite -> comp_assoc.
apply f_equal2;trivial.
rewrite -> map_lifting.
rewrite -> f_cpr.
rewrite -> f_cpr.
rewrite -> comp_assoc with (h':=out).
rewrite -> out_unitcofree.
rewrite -> f_cpr.
rewrite <- comp_assoc with (f':=inl).
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite <- comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite -> coprodhom_inl.
rewrite <- comp_assoc with (g':=inr).
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite <- comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=inr).
rewrite -> cpr_inr.
unfold p.
rewrite <- comp_assoc with (f':=map ([inl ⊕⊕ id, inl ∘ inr])).
rewrite -> map_comp.
rewrite -> f_cpr.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=inl).
rewrite -> coprodhom_inl.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=inl).
rewrite -> coprodhom_inl.
rewrite <- comp_assoc with (f':=inr).
rewrite -> coprodhom_inr.
rewrite -> lifting_map.
apply f_equal1.
rewrite -> f_cpr.
rewrite -> cpr_coprodhom.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
reflexivity.

assert (Hq: ((map ([inl ⊕⊕ id, inl ∘ inr])) ∘ out ∘ t) † = 
              ([η ∘ inl, (map ([inl ⊕⊕ id, inl ∘ inr])) ∘ out ∘ g] * ∘ 
              q ∘ (map ([inl ⊕⊕ id, inl ∘ inr])) ∘ out ∘ h) †).
apply f_equal1.
unfold t.
rewrite -> comp_assoc.
apply f_equal2;trivial.
rewrite <- comp_assoc.
rewrite -> lifting1.
rewrite -> comp_assoc.
apply f_equal2;trivial.
rewrite -> map_lifting.
rewrite -> f_cpr.
rewrite -> f_cpr.
rewrite -> comp_assoc with (h':=out).
rewrite -> out_unitcofree.
rewrite -> f_cpr.
rewrite <- comp_assoc with (f':=inl).
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite <- comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite -> coprodhom_inl.
rewrite <- comp_assoc with (g':=inr).
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite <- comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=inr).
rewrite -> cpr_inr.
unfold q.
rewrite <- comp_assoc with (f':=map ([inl ⊕⊕ id, inl ∘ inr])).
rewrite -> map_comp.
rewrite -> f_cpr.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=inl).
rewrite -> coprodhom_inl.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=inl).
rewrite -> coprodhom_inl.
rewrite <- comp_assoc with (f':=inr).
rewrite -> coprodhom_inr.
rewrite -> lifting_map.
apply f_equal1.
rewrite -> f_cpr.
rewrite -> cpr_coprodhom.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
reflexivity.


(* left hand side *)
apply out_cong.
rewrite -> comp_assoc.
rewrite -> lifting1 at 1.
unfold triangular at 1.
rewrite <- comp_assoc with (h':=tuo).
rewrite <- comp_assoc with (g':=out).
rewrite -> comp_assoc with (g':=tuo).
(* since the introduction of cont, this doesn't work anymore TODO *)
Admitted.
(*
rewrite -> out_tuo_is_id.
rewrite -> id_r.
rewrite -> comp_assoc.
rewrite -> lifting_map.
rewrite -> cpr_coprodhom.
rewrite <- comp_assoc with (f':=inl).
rewrite -> cpr_inl.
rewrite -> out_unitcofree.
rewrite -> id_l. (* this equals T (id + id ×× ([ηv, w]) § ^^ id), not T (inl + ...) *)

rewrite -> Hp.

rewrite <- comp_assoc with (g':=p).
rewrite <- comp_assoc with (f':=g).
rewrite <- comp_assoc with (f':=out ∘ g).
rewrite -> dinaturality.

unfold p.
rewrite <- comp_assoc with (h':=map ((id ⊕⊕ id ×× ([ηv ∘ inl, h]) § ^^ id) ⊕⊕ id)).
rewrite -> comp_assoc with (g':=map ((id ⊕⊕ id ×× ([ηv ∘ inl, h]) § ^^ id) ⊕⊕ id)).
rewrite -> lifting_map.
rewrite -> cpr_coprodhom.
rewrite -> id_l.

rewrite -> comp_assoc.
rewrite <- kl3.
rewrite -> f_cpr.
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite -> cpr_coprodhom.
rewrite -> id_l.
rewrite <- comp_assoc with (h':=η ∘ inr).
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
rewrite <- proving_kl3.
rewrite -> f_cpr.
rewrite -> comp_assoc with (g':=ηv).
rewrite -> proving_kl2.
rewrite -> cpr_inl. (* how does one get iter_cofree t here ? *)


(* right hand side *)
rewrite -> comp_assoc with (h':=out).
rewrite -> comp_assoc with (h':=out).
rewrite -> lifting1.

rewrite <- comp_assoc with (g':=out).
rewrite <- comp_assoc with (g':=out).
rewrite -> lifting1.

assert (H: (([out ∘ [ηv ∘ inl, ▷t], (η ∘ inr) ∘ id ×× ([ηv ∘ inl, ▷t]) § ^^ id]) *
    ∘ (out ∘ g) = ([η ∘ inl ⊕⊕ id ×× ([ηv ∘ inl, ▷t]) § ^^ id, out ∘ ▷t] * 
    ∘ map ([inl ⊕⊕ id, inl ∘ inr])) ∘ (out ∘ g))).
apply f_equal2;trivial.
rewrite -> lifting_map.
rewrite -> f_cpr.
rewrite -> f_cpr.
rewrite -> cpr_coprodhom.
rewrite <- comp_assoc with (f':=inl).
rewrite -> coprodhom_inl.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=inl).
rewrite -> comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite <- comp_assoc with (f':=inr).
rewrite -> coprodhom_inr.
rewrite -> comp_assoc with (h':=out).
rewrite -> out_unitcofree.
rewrite -> comp_assoc.
reflexivity.

rewrite <- comp_assoc with (f':=g).
rewrite <- comp_assoc with (f':=g).
rewrite -> H.
clear H.

rewrite <- comp_assoc with (g':=map ([inl ⊕⊕ id, inl ∘ inr])).
rewrite -> comp_assoc with (f':=(map ([inl ⊕⊕ id, inl ∘ inr]) ∘ (out ∘ g))).
rewrite <- kl3.
rewrite -> f_cpr.
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite -> cpr_coprodhom.
rewrite <- comp_assoc with (h':=η ∘ inr).
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
rewrite <- comp_assoc with (f':=inl).
rewrite -> cpr_inl.
rewrite -> out_unitcofree. (* again T(id + ..) not T(inl + ..) *)
rewrite <- proving_kl3.
rewrite -> f_cpr.
rewrite -> comp_assoc with (f':=inl).
rewrite -> proving_kl2.
rewrite -> cpr_inl.
rewrite <- unfolding_triangular1.


apply f_equal2;trivial.
apply f_equal1.

assert (H1: ([ηv, w]) § ∘ h = iter_cofree t).
unfold w.
unfold t.
symmetry.
rewrite <- proving_unfolding at 1.
rewrite -> comp_assoc.
apply f_equal2;trivial.
rewrite <- proving_kl3.
apply f_equal1.
rewrite -> f_cpr.
rewrite -> comp_assoc with (g':=ηv).
rewrite -> proving_kl2.
rewrite -> cpr_inl.
reflexivity.

rewrite -> H1.
apply f_equal2;trivial.


(* left hand side *)
rewrite -> naturality.
rewrite -> f_cpr.
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite <- comp_assoc with (g':=inr).
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.

rewrite -> comp_assoc.
rewrite <- kl3.
rewrite -> f_cpr.
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite -> cpr_inl.

rewrite -> comp_assoc with (g':=map ((id ⊕⊕ id ×× ([ηv ∘ inl, h]) § ^^ id) ⊕⊕ id)).
rewrite -> lifting_map.
rewrite -> cpr_coprodhom.
rewrite -> cpr_coprodhom.
rewrite -> id_l.
rewrite -> id_l.
rewrite <- comp_assoc with (f':=id ×× ([ηv ∘ inl, h]) § ^^ id).
rewrite <- comp_assoc with (f':=id ×× ([ηv ∘ inl, h]) § ^^ id).
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.

(* page 22 at the top step 2/3, very unclean way to do things, TODO: make it clean *)
assert (H2: (([[(η ∘ inl) ∘ inl, (η ∘ inl) ∘ (inr ∘ id ×× ([ηv, w]) § ^^ id)],
  ([[(η ∘ inl) ∘ inl,
    (η ∘ inl) ∘ (inr ∘ id ×× (([ηv, w]) § ∘ ([ηv ∘ inl, h]) §) ^^ id)],
   η ∘ inr]) * ∘ (map ([inl ⊕⊕ id, inl ∘ inr]) ∘ (out ∘ g))]) *
 ∘ (map ([inl ⊕⊕ id, inl ∘ inr]) ∘ (out ∘ h))) † = 
  map (id ⊕⊕ id ×× ([ηv, iter_cofree t]) § ^^ id) ∘ 
  ([η ∘ inl ∘ id ⊕⊕ id ×× [ηv ∘ inl, g] § ^^ id, map ([inl ⊕⊕ id, inl ∘ inr]) ∘ out ∘ g] * ∘
  map ([inl ⊕⊕ id, inl ∘ inr]) ∘ out ∘ h) †).
symmetry.
unfold map at 1.
rewrite -> naturality.
apply f_equal1.
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite <- comp_assoc with (f':=h).
rewrite <- comp_assoc with (f':=out ∘ h).
rewrite -> comp_assoc with (f':=(map ([inl ⊕⊕ id, inl ∘ inr]) ∘ (out ∘ h))).
apply f_equal2;trivial.
rewrite <- kl3.
apply f_equal1.
rewrite -> f_cpr.
rewrite <- comp_assoc with (h':=η).
rewrite <- comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite -> comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite <- comp_assoc with (f':=id ⊕⊕ id ×× ([ηv ∘ inl, g]) § ^^ id).
rewrite <- comp_assoc with (f':=id ⊕⊕ id ×× ([ηv ∘ inl, g]) § ^^ id).
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
rewrite <- proving_kl3.
rewrite -> f_cpr.
rewrite -> comp_assoc with (g':=ηv).
rewrite -> proving_kl2.
rewrite -> cpr_inl.
rewrite <- proving_kl3.
rewrite -> f_cpr.
rewrite -> comp_assoc with (g':=ηv).
rewrite -> proving_kl2.
rewrite -> cpr_inl.
unfold coprodhom.
rewrite -> id_l.
rewrite -> id_l.
repeat rewrite <- comp_assoc with (h':=η).
repeat rewrite <- f_cpr.

rewrite -> H1.
unfold w.
rewrite <- comp_assoc with (f':=g).
reflexivity.

rewrite -> H2.
clear H2.

(* right hand side *)
unfold triangular.
rewrite <- comp_assoc with (h':=tuo).
rewrite <- comp_assoc with (g':=out).
rewrite -> comp_assoc with (g':=tuo).
rewrite -> out_tuo_is_id.
rewrite -> id_r.

rewrite -> comp_assoc with (g':=map (inl ⊕⊕ id)).
rewrite -> lifting_map.
rewrite -> lifting_map.

rewrite -> cpr_coprodhom.
rewrite <- comp_assoc with (g':=[ηv, iter_cofree t]).
rewrite -> cpr_inl.
rewrite -> out_unitcofree.
rewrite -> id_l.

rewrite -> Hq.


rewrite <- comp_assoc with (f':=h).
rewrite <- comp_assoc with (g':=map ([inl ⊕⊕ id, inl ∘ inr])).
apply f_equal2.
unfold coprodhom.
rewrite -> id_l.
unfold map.
rewrite -> f_cpr.
rewrite -> comp_assoc.
reflexivity.

apply f_equal1.
rewrite -> comp_assoc with (f':=out ∘ h).
apply f_equal2;trivial.
unfold q.
rewrite <- comp_assoc with (f':=map ([inl ⊕⊕ id, inl ∘ inr])).
rewrite -> map_comp.
rewrite -> lifting_map.
apply f_equal1.
rewrite -> comp_assoc with (g':=(id ⊕⊕ id ×× ([ηv ∘ inl, g]) § ^^ id) ⊕⊕ id).
rewrite -> cpr_coprodhom.
rewrite -> id_l.
reflexivity.

symmetry.
apply unfolding_triangular2.

rewrite -> H0.

rewrite <- proving_kl3.
rewrite -> f_cpr.
rewrite -> comp_assoc with (f':=inl).
rewrite -> proving_kl2.
rewrite -> cpr_inl.
rewrite <- unfolding_triangular1.
unfold w.
reflexivity.

Qed.
*)


(*
(* --- *)

Theorem proving_codiagonal : forall x y (g: x ~> (coext T a b (y ⊕ (x ⊕ x)))),
    iter_cofree (lifting_cofree (ηv ∘ id ⊕⊕ ∇) ∘ g) = iter_cofree (iter_cofree g).
Admitted.

(* --- *)
*)


Theorem proving_uniformity_guarded : forall x y z (f : x ~> coext T a b (y ⊕ x)) (g: z ~> coext T a b (y ⊕ z)) (h: z ~> x),
    guarded g ->
    f ∘ h = lifting_cofree (ηv ∘ id ⊕⊕ h) ∘ g ->
    iter_cofree f ∘ h = iter_cofree g.
Proof.
intros.
apply unfolding_guarded2.
apply H.
assert (H1: ([ηv, iter_cofree f ∘ h]) § = ([ηv, iter_cofree f]) § ∘ (ηv ∘ id ⊕⊕ h) §).
rewrite <- proving_kl3.
rewrite -> comp_assoc.
rewrite -> proving_kl2.
rewrite -> cpr_coprodhom.
rewrite -> id_l.
reflexivity.
rewrite -> H1.
rewrite <- comp_assoc.
rewrite <- H0.
rewrite -> comp_assoc.
rewrite -> proving_unfolding.
reflexivity.
Qed.

Theorem proving_uniformity : forall x y z (f : x ~> coext T a b (y ⊕ x)) (g: z ~> coext T a b (y ⊕ z)) (h: z ~> x),
    f ∘ h = lifting_cofree (ηv ∘ id ⊕⊕ h) ∘ g ->
    iter_cofree f ∘ h = iter_cofree g.
Proof.
intros.

assert (H1: (map ([inl ⊕⊕ id, inl ∘ inr]) ∘ out ∘ f) † ∘ h = 
              map (id ⊕⊕ id ×× map_cofree (id ⊕⊕ h) ^^ id) ∘ 
              (map ([inl ⊕⊕ id, inl ∘ inr]) ∘ out ∘ g) †).

symmetry.
unfold map at 1.
rewrite -> naturality.
symmetry.
apply uniformity.
rewrite <- comp_assoc.
rewrite -> H.
rewrite <- comp_assoc with (g':=out).
rewrite -> comp_assoc with (h':=out).
rewrite -> lifting1.
rewrite -> comp_assoc with (h':=out).
rewrite -> out_unitcofree.

rewrite <- comp_assoc with (f':=g).
rewrite <- comp_assoc with (f':=g).
rewrite -> comp_assoc with (f':=out ∘ g).
rewrite -> comp_assoc with (f':=out ∘ g).
rewrite -> comp_assoc with (f':=out ∘ g).
apply f_equal2;trivial.

rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite -> lifting_map.
rewrite <- kl3.
rewrite -> map_lifting.
apply f_equal1.
rewrite -> f_cpr.
rewrite <- comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite -> comp_assoc with (g':=inl).
rewrite <- comp_assoc with (h':=η).
rewrite -> cpr_inl.
rewrite <- comp_assoc with (h':=η).
rewrite -> coprodhom_comp.
rewrite -> id_r.
rewrite -> id_l.
rewrite <- comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite -> comp_assoc with (g':=inr).
rewrite <- comp_assoc with (h':=η).
rewrite -> cpr_inr.
rewrite -> f_cpr.
rewrite -> cpr_coprodhom.
rewrite <- comp_assoc with (f':=inl).
rewrite -> coprodhom_inl.
rewrite ->2 id_l.
rewrite ->2 comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite <-2 comp_assoc with (f':=inr).
rewrite -> coprodhom_inr.
rewrite -> f_cpr.
rewrite <-3 comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite ->2 comp_assoc with (g':=inl).
rewrite <-2 comp_assoc with (f':=inl).
rewrite -> coprodhom_inl.
rewrite -> id_l.
rewrite -> f_cpr.
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite -> comp_assoc with (g':=inl).
rewrite <- comp_assoc with (g':=id ⊕⊕ h).
rewrite -> coprodhom_inl.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite -> comp_assoc with (g':=inr).
rewrite <- comp_assoc with (g':=id ⊕⊕ h).
rewrite -> coprodhom_inr.
rewrite -> mapcofree.
unfold coprodhom.
rewrite -> f_cpr.
repeat rewrite -> comp_assoc.
reflexivity.

assert (H2: (▷f) ∘ h = map_cofree (id ⊕⊕ h) ∘ ▷g).
unfold triangular.
rewrite <- comp_assoc.
rewrite -> H1.
rewrite ->2 comp_assoc.
apply f_equal2;trivial.
(* introduce new lemma for this ? see also lemma 22 in the paper *)
apply out_cong.
rewrite -> comp_assoc with (g':=map_cofree (id ⊕⊕ h)).
rewrite -> out_mapcofree.
rewrite ->2 comp_assoc with (h':=out).
rewrite -> out_tuo_is_id.
rewrite -> id_r.
(* since the introduction of cont, this doesn't work anymore TODO *)
Admitted.
(*
rewrite <- comp_assoc with (g':=out).
rewrite -> comp_assoc with (g':=tuo).
rewrite -> out_tuo_is_id.
rewrite -> id_r.
rewrite ->2 map_comp.
rewrite ->2 coprodhom_comp.
rewrite -> id_l.
rewrite -> coprodhom_inl.
rewrite -> id_l.
rewrite -> id_r.
rewrite -> id_l.
reflexivity.


rewrite -> itercofree_triangular.
symmetry.
rewrite -> itercofree_triangular.
symmetry.
apply proving_uniformity_guarded.
apply guardedtriangular_def.
rewrite <- mapcofree.
apply H2.

Qed.
*)


(* --- *)
Theorem proving_str1 : forall (x y : Obj),
    pr2 = (ηv ∘ pr2) § ∘ τv (x:=x) (y:=y) (a:=a) (b:=b).
Proof.
intros.
rewrite <- mapcofree.
(*
assert (pr2 (a:=x) (b:=coext T a b y) = map_cofree (pr2 (a:=x) (b:=y)) ∘ (map_cofree (pair bang id) ∘ pr2)).
rewrite -> comp_assoc.
rewrite -> mapcofree_comp.
rewrite -> pr2_pair.
rewrite -> mapcofree_id.
rewrite -> id_r.
trivial.

rewrite -> H.
*)
Admitted.

Theorem proving_str2 : forall (x y z : Obj),
    (ηv ∘ prod_assoc1)§ ∘ τv (x:=(x × y)) (y:=(coext T a b (coext T a b z))) (a:=a) (b:=b) = 
    τv ∘ id ×× τv ∘ prod_assoc1.
Admitted.

Theorem proving_str3 :forall (x y : Obj),
    τv (x:=x) (y:=y) (a:=a) (b:=b) ∘ id ×× ηv = ηv.
Admitted.

Theorem proving_str4 : forall x y (f: coext T a b x ~> coext T a b (coext T a b y)),
    (τv ∘ id ×× f) § ∘ τv = τv ∘ id (a:=x) ×× f §.
Admitted.

(* --- *)


Definition ηv' (x : Obj) :=
ηv (x:=x) (a:=a) (b:=b).

Definition lifting_cofree' (x y : Obj) (f: x ~> coext T a b y) :=
lifting_cofree (x:=x) (y:=y) (a:=a) (b:=b) f.

Definition iter_cofree' (x y : Obj) (f: x ~> coext T a b (y ⊕ x)) :=
coit ([[η ∘ inl, (map ([inl ⊕⊕ id, inl ∘ inr]) ∘ out ∘ f) †], η ∘ inr]* ∘ out) ∘ 
ηv ∘ inr.

Definition τv' (x y : Obj) := 
τv (x:=x) (y:=y) (a:=a) (b:=b).

(* Proof that a cofree extension is an ElgotMonad *)
Instance cofree : ElgotMonad Obj Hom (coext T a b) := {
    η := ηv';
    lifting := lifting_cofree';
    iter := iter_cofree';
    τ := τv'
}.

Proof.

intros.
apply dist1.
intros.
apply prod_assoc2.
intros.
apply coprod_assoc1.
intros.
apply coprod_assoc2.

apply comp_assoc.

intros.
apply id_l.
intros.
apply id_r.

apply proving_kl1.

apply proving_kl2.

apply proving_kl3.

apply proving_unfolding.

apply proving_naturality.

apply proving_dinaturality.

(* codiagonal *)

(* uniformity *)

(* str1 *)
(* str2 *)
(* str3 *)
(* str4 *)

(* compcpr *)
(* inlcpr *)
(* inrcpr *)
(* inlinrisid *)

(* comppair *)
(* pr1pair *)
(* pr2pair *)
(* pr1pr2isid *)

(* curryevid *)
(* ev_law *)
(* curry1 *)

(* TODO *)
Admitted.



End ContextCofreeElgotMonad.
