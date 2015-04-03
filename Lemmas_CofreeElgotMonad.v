Add LoadPath "~/Schreibtisch/svnba/Elgot/Coq/".
Require Import Coq_Steroids.
Require Import ElgotMonad.
Require Import Lemmas_ElgotMonad.
Require Import CofreeElgotMonad.
Require Import Setoid.
Open Scope elgot_scope.
Section Lemmas.
Context `(CofreeElgotMonad).

(* Lemmas proven in the following:

fusion:
  u ∘ v = map (id ⊕⊕ id ×× v ^^ id) ∘ w ->
    coit w = (coit u) ∘ v.

coit_of_out_is_id:
  coit (out) = id

tuo_out_is_id:
  tuo ∘ out = id

out_tuo_is_id:
  out ∘ tuo = id

out_cong:
  out ∘ f = out ∘ g -> f = g

out_mapcofree:
  out ∘ map_cofree f = 
    map (f ⊕⊕ id ×× map_cofree f ^^ id) ∘ out

out_unitcofree:
  out ∘ ηv = η  ∘ inl

mapcofree_id:
  map_cofree (a:=a) (b:=b) (id (a:=x)) = id

mapcofree_comp:
  map_cofree f ∘ map_cofree g = map_cofree (f ∘ g)

mapcofree:
  map_cofree f = (ηv ∘ f) §

mapcofree_unitcofree
  map_cofree u ∘ ηv = ηv ∘ u

mapcofree_coit (fusion!)
  map_cofree s ∘ coit t = coit (map (s ⊕⊕ id) ∘ t)

mapcofree_liftingcofree (fusion!)
  map_cofree s ∘ t § = coit (([map(s ⊕⊕ id ×× map_cofree inr ^^ id) ∘ out ∘ [t, ηv],
       η ∘ inr]) * ∘ out) ∘ map_cofree inl

mapcofree_liftingcofree_unfolded (fusion!)
  map_cofree s ∘ (coit
     (([(map (id ⊕⊕ id ×× map_cofree inr ^^ id) ∘ out) ∘ [t, ηv],
       η ∘ inr]) * ∘ out) ∘ map_cofree inl) = coit (([map(s ⊕⊕ id ×× map_cofree inr ^^ id) ∘ out ∘ [t, ηv],
       η ∘ inr]) * ∘ out) ∘ map_cofree inl

liftingcofree_unfoldtocpr: 
  f § =  [f, ηv] § ∘ map_cofree inl

liftingdef_with_inr:
  coit (([(map (id ⊕⊕ id ×× map_cofree inr ^^ id) ∘ out)
                 ∘ [t, ηv], η ∘ inr]) * ∘ out) ∘ map_cofree inr = id

lifting1:
  out ∘ t § = [out ∘ t, η ∘ inr ∘ id ×× t § ^^ id]* ∘ out

lifting2: 
  out ∘ s = [out ∘ t, η ∘ inr ∘ id ×× s ^^ id]* ∘ out ->
    s = t §

guardedtriangular: 
  guarded f u -> ▷ f = f

guardedtriangular_def: 
  guarded (▷ f) u.

itercofree_triangular: 
  iter_cofree f = iter_cofree (▷ f)

liftingcofree_tuo: 
  [ηv, t] § ∘ tuo = tuo ∘ [[η ∘ inl, out ∘ t], η ∘ inr ∘ id ×× [ηv, t] § ^^ id] *

unfolding_guarded1:
  guarded f -> iter_cofree f = [ηv, iter_cofree f] § ∘ f

unfolding_guarded2:
  guarded f -> g = [ηv, g] § ∘ f -> g = iter_cofree f

unfolding_triangular1: 
  iter_cofree f = [ηv, iter_cofree f] § ∘ ▷ f

unfolding_triangular2:
  g = [ηv, g] § ∘ ▷ f -> g = iter_cofree f

out_itercofree:
  out ∘ iter_cofree f = ([η ∘ inl, (η ∘ inr) ∘ id ×× [ηv, iter_cofree f] § ^^ id]) *
    ∘ ((map ([inl ⊕⊕ id, inl ∘ inr]) ∘ out) ∘ f) †

*)



Lemma fusion : forall
(A B a b x : Obj) 
(u: B ~> T (x ⊕ a × (exp B b))) 
(v: A ~> B) 
(w: A ~> T (x ⊕ a × (exp A b))),
  u ∘ v = map (id ⊕⊕ id ×× v ^^ id) ∘ w ->
    coit w = (coit u) ∘ v.
Proof.
intros.
symmetry.
apply coit2.
rewrite -> comp_assoc with (h':= out).
rewrite -> coit1.
rewrite <- comp_assoc with (f':=v).
rewrite -> H0.
rewrite -> comp_assoc with (f':=w).
rewrite -> map_comp.
apply f_equal2; trivial.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
reflexivity.
Qed.


Lemma coit_of_out_is_id : forall
(A x a b : Obj),
coit (out (x:=x) (a:=a) (b:=b)) = id.
Proof.
intros.
symmetry.
apply coit2.
rewrite -> id_l.
rewrite -> exphom_id.
rewrite -> prodhom_id.
rewrite -> coprodhom_id.
rewrite -> map_id.
rewrite -> id_r.
reflexivity.
Qed.

Lemma tuo_out_is_id : forall
(x a b : Obj),
tuo (x:=x) (a:=a) (b:=b) ∘ out = id.
Proof.
intros.
unfold tuo.
rewrite <- fusion with (w:=out).
rewrite -> coit_of_out_is_id.
reflexivity.
trivial.
reflexivity.
Qed.

Lemma out_tuo_is_id : forall
(x a b : Obj),
out (x:=x) (a:=a) (b:=b) ∘ tuo = id.
Proof.
intros.
unfold tuo.
rewrite -> coit1.
rewrite -> map_comp.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
rewrite -> tuo_out_is_id.
rewrite -> exphom_id.
rewrite -> prodhom_id.
rewrite -> coprodhom_id.
rewrite -> map_id.
reflexivity.
Qed.


Lemma out_cong : forall
(x y a b : Obj) 
(f: x ~> coext T a b y) 
(g: x ~> coext T a b y),
  out ∘ f = out ∘ g -> f = g.
Proof.
intros.
transitivity (tuo ∘ out ∘ f).
rewrite -> tuo_out_is_id.
rewrite -> id_r; trivial.
transitivity (tuo ∘ out ∘ g).
rewrite <- comp_assoc.
rewrite H0.
rewrite <- comp_assoc; trivial.
rewrite -> tuo_out_is_id.
rewrite -> id_r; trivial.
Qed.

Lemma tuo_cong : forall
(x y a b : Obj) 
(f: x ~> T (y ⊕ a × (coext T a b y) $ b)) 
(g: x ~> T (y ⊕ a × (coext T a b y) $ b)),
  tuo ∘ f = tuo ∘ g -> f = g.
Proof.
intros.
assert (out ∘ tuo ∘ f = out ∘ tuo ∘ g).
rewrite <-2 comp_assoc.
congruence.
rewrite -> out_tuo_is_id in H1.
rewrite ->2 id_r in H1; trivial.
Qed.

Lemma out_mapcofree : forall
(x y a b : Obj) 
(f: x ~> y),
  out ∘ map_cofree f = 
    map (f ⊕⊕ id ×× map_cofree f ^^ id) ∘ out (a:=a) (b:=b).
Proof.
intros.

unfold map_cofree.
rewrite -> coit1.
rewrite -> comp_assoc.
apply f_equal2; trivial.
rewrite -> map_comp.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> id_r.
reflexivity.
Qed.

Lemma out_unitcofree : forall
(x a b : Obj),
  out (a:=a) (b:=b) ∘ ηv = η  ∘ inl (a:=x).
Proof.
intros.
unfold ηv.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> out_tuo_is_id.
rewrite -> id_r.
trivial.
Qed.


Lemma mapcofree_id : forall
(x a b : Obj),
map_cofree (a:=a) (b:=b) (id (a:=x)) = id.
Proof.
intros.
unfold map_cofree.
rewrite -> coprodhom_id.
rewrite -> map_id.
rewrite -> id_r.
rewrite -> coit_of_out_is_id; trivial.
Qed.



Lemma mapcofree_comp : forall
(x y z a b : Obj) 
(f: y ~> z) 
(g: x ~> y),
  map_cofree f ∘ map_cofree g = map_cofree (a:=a) (b:=b) (f ∘ g).
Proof.
intros.
unfold map_cofree.
apply coit2.
rewrite -> comp_assoc with (h':=out).
rewrite -> coit1.
rewrite -> comp_assoc with (f':=out).
rewrite -> map_comp.
rewrite <- comp_assoc with (g':=out).
rewrite -> coit1.
rewrite -> comp_assoc with (f':=out).
rewrite -> map_comp.
rewrite -> comp_assoc with (f':=out).
rewrite -> map_comp.
rewrite -> comp_assoc with (f':=out).
rewrite -> map_comp.
apply f_equal2; trivial.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> id_r.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> id_r.
rewrite -> coprodhom_comp.
unfold cont.
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> id_r.
rewrite -> exphom_comp.
reflexivity.
Qed.


Lemma mapcofree_unitcofree : forall
(x y a b : Obj) (f: x ~> y),
map_cofree (a:=a) (b:=b) f ∘ ηv = ηv ∘ f.
Proof.
intros.
unfold map_cofree.
apply out_cong.
rewrite -> comp_assoc.
rewrite -> coit1.
rewrite -> comp_assoc with (h':=out).
rewrite -> out_unitcofree.
rewrite -> comp_assoc with (f':=out).
rewrite -> map_comp.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> id_r.
rewrite <- comp_assoc with (g':=out).
rewrite -> out_unitcofree.
rewrite -> comp_assoc with (f':=inl).
rewrite -> map_unit.
rewrite <- comp_assoc with (f':=inl).
rewrite -> coprodhom_inl.
rewrite -> comp_assoc.
reflexivity.
Qed.


Lemma mapcofree_coit : forall
(x y z a b : Obj) (f: y ~> z) (g: x ~> T (y ⊕ a × x $ b)),
map_cofree f ∘ coit g = coit (map (f ⊕⊕ id) ∘ g).
Proof.
intros.
unfold map_cofree.
rewrite <- fusion with (w:= map (f ⊕⊕ id) ∘ g).
reflexivity.
rewrite <- comp_assoc.
rewrite -> coit1.
rewrite -> comp_assoc.
rewrite -> map_comp.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> id_r.
rewrite -> comp_assoc.
rewrite -> map_comp.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> id_r.
reflexivity.
Qed.


Lemma mapcofree_liftingcofree : forall
(x y z a b : Obj) (f: y ~> z) (g: x ~> coext T a b y),
map_cofree f ∘ g § = coit (([map(f ⊕⊕ id ×× map_cofree inr ^^ id) ∘ out ∘ [g, ηv],
       η ∘ inr]) * ∘ out) ∘ map_cofree inl.
Proof. 
intros.
unfold lifting_cofree.
rewrite -> comp_assoc with (h':=map_cofree f).
rewrite -> mapcofree_coit.
apply f_equal2; trivial.
rewrite -> comp_assoc with (h':=map (f ⊕⊕ id)).
rewrite -> map_lifting.
rewrite -> f_cpr.
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite <- comp_assoc with (f':=inr).
rewrite -> coprodhom_inr.
rewrite -> id_l.
rewrite ->2 comp_assoc.
rewrite -> map_comp.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> id_r.
reflexivity.
Qed.


Lemma mapcofree_liftingcofree_unfolded : forall
(x y z a b : Obj) (f: y ~> z) (g: x ~> coext T a b y),
map_cofree f ∘ (coit
     (([(map (id ⊕⊕ id ×× map_cofree inr ^^ id) ∘ out) ∘ [g, ηv],
       η ∘ inr]) * ∘ out) ∘ map_cofree inl) = coit (([map(f ⊕⊕ id ×× map_cofree inr ^^ id) ∘ out ∘ [g, ηv],
       η ∘ inr]) * ∘ out) ∘ map_cofree inl.
Proof. 
apply mapcofree_liftingcofree. 
Qed.


Lemma liftingcofree_unfoldtocpr : forall
(x y a b : Obj) (f: x ~> coext T a b y),
f § = [f, ηv] § ∘ map_cofree inl.
Proof.
intros.
unfold lifting_cofree.
apply f_equal2; trivial.
symmetry.
apply coit2.
rewrite -> comp_assoc.
rewrite -> coit1.
rewrite -> comp_assoc.
rewrite -> map_lifting.
rewrite <- comp_assoc with (f':=map_cofree inl).
rewrite -> out_mapcofree.
rewrite -> comp_assoc.
rewrite -> lifting_map.
rewrite <- comp_assoc with (f':=inl ⊕⊕ id ×× map_cofree inl ^^ id).
rewrite -> cpr_coprodhom.
rewrite <- comp_assoc with (f':=inl).
rewrite -> cpr_inl.
rewrite -> comp_assoc.
apply f_equal2; trivial.

rewrite -> map_lifting.
rewrite -> f_cpr.
rewrite -> f_cpr with (h:=η ∘ inr).
rewrite <- comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite <- comp_assoc with (h':=η).
rewrite <- comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=inr).
rewrite -> coprodhom_inr.
rewrite -> coprodhom_inr.
rewrite <- comp_assoc with (h':=inr).
rewrite -> prodhom_comp.
rewrite -> id_l.

rewrite -> exphom_comp.
apply f_equal1.
apply f_equal2; trivial.

rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> map_comp.

rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> map_comp.
apply f_equal2; trivial.
apply f_equal2; trivial.

apply f_equal1.


rewrite -> coprodhom_comp.
rewrite -> coprodhom_comp.

rewrite -> id_l.


rewrite -> prodhom_comp.
rewrite -> prodhom_comp.

rewrite -> id_l.

apply f_equal2; trivial.
apply f_equal2; trivial.

rewrite -> exphom_comp.
rewrite -> exphom_comp.

apply f_equal2; trivial.

rewrite <- comp_assoc.
rewrite <- comp_assoc.

rewrite -> mapcofree_comp.

transitivity (coit (out (a:=a) (b:=b)(x:=y))).
symmetry.
apply fusion.

rewrite <- comp_assoc.

rewrite -> out_mapcofree.
rewrite -> comp_assoc.

apply f_equal2; trivial.

rewrite -> lifting_map.
rewrite -> cpr_coprodhom.

rewrite <- comp_assoc.
rewrite <- comp_assoc.

rewrite -> cpr_inr.
rewrite -> out_unitcofree.

rewrite -> comp_assoc.

rewrite -> map_unit.

rewrite <- comp_assoc.

rewrite -> coprodhom_inl.
rewrite -> id_l.

rewrite <- comp_assoc.
rewrite <- f_cpr.
unfold map.
unfold coprodhom.
rewrite -> id_l.
trivial.

apply fusion.

rewrite <- comp_assoc.

rewrite -> out_mapcofree.
rewrite -> comp_assoc.

apply f_equal2; trivial.

rewrite -> lifting_map.
rewrite -> cpr_coprodhom.

rewrite <- comp_assoc.
rewrite <- comp_assoc.

rewrite -> comp_assoc with (g':=inl).


rewrite -> cpr_inl.
rewrite -> cpr_inr.
rewrite -> out_unitcofree.

rewrite -> comp_assoc.

rewrite -> map_unit.

rewrite <- comp_assoc.

rewrite -> coprodhom_inl.
rewrite -> id_l.

rewrite <- comp_assoc.
rewrite <- f_cpr.
unfold map.
unfold coprodhom.
rewrite -> id_l.
trivial.

Qed.

Lemma liftingdef_with_inr : forall 
(x y a b : Obj) (f: x ~> coext T a b y),
coit (([(map (id ⊕⊕ id ×× map_cofree inr ^^ id) ∘ out)
                 ∘ [f, ηv], η ∘ inr]) * ∘ out) ∘ map_cofree inr = id.
Proof.
intros.
rewrite <- coit_of_out_is_id; trivial.
symmetry.
apply fusion.
rewrite <- comp_assoc.
rewrite -> out_mapcofree.
rewrite -> comp_assoc.
rewrite -> lifting_map.
rewrite -> cpr_coprodhom.
rewrite <- comp_assoc with (f':=inr).
rewrite -> cpr_inr.
rewrite <- comp_assoc with (f':=ηv).
rewrite -> out_unitcofree.
rewrite -> comp_assoc with (f':=inl).
rewrite -> map_unit.
rewrite <- comp_assoc with (f':=inl).
rewrite -> coprodhom_inl.
rewrite -> id_l.
rewrite <- comp_assoc with (g':=inr).
rewrite <- f_cpr.
unfold map.
unfold coprodhom.
rewrite -> id_l.
reflexivity.
Qed.


Lemma lifting1 : forall
(x y a b : Obj) (f: x ~> coext T a b y),
out ∘ f § = [out ∘ f, η ∘ inr ∘ id ×× f § ^^ id]* ∘ out.
Proof.
intros.
unfold lifting_cofree.
rewrite -> comp_assoc.
rewrite -> coit1.

rewrite <- comp_assoc.
rewrite <- comp_assoc with (f':=map_cofree inl).
rewrite -> out_mapcofree.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
apply f_equal2; trivial.

rewrite <- comp_assoc.
rewrite -> lifting_map.
rewrite -> cpr_coprodhom.
rewrite -> map_lifting.

apply f_equal1.

rewrite <- comp_assoc with (f':=inl).
rewrite -> cpr_inl.

rewrite -> f_cpr.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> map_comp.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.

rewrite -> liftingdef_with_inr.
rewrite -> exphom_id.
rewrite -> prodhom_id.
rewrite -> coprodhom_id.
rewrite -> map_id.
rewrite -> id_r.


rewrite <- comp_assoc with (g':=inr).
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite -> comp_assoc with (g':=inr).
rewrite <- comp_assoc with (h':=η).
rewrite -> coprodhom_inr.
rewrite -> comp_assoc with (g':=inr).
rewrite <- comp_assoc with (f':=id ×× map_cofree inl ^^ id).
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
reflexivity.
Qed.


Lemma lifting2 : forall
(x y a b : Obj) (f: x ~> coext T a b y) (g: coext T a b x ~> coext T a b y),
  out ∘ g = [out ∘ f, η ∘ inr ∘ id ×× g ^^ id]* ∘ out ->
    g = f §.
Proof.
intros.

(* The idea is to introduce such w: T_a^b x + T_a^b y -> T_a^b y
    that w inl = g and w inr = id *)

remember (coit ([[(map (id ⊕⊕ id ×× inr^^id)) ∘ out ∘ f, 
                    η ∘ inr ∘ id ×× inl^^id]* ∘ out, 
                  (map (id ⊕⊕ id ×× inr^^id)) ∘ out])) as w eqn:W.

assert ([g, id] = [f§, id]).
transitivity w.

rewrite -> W.
apply coit2.
rewrite ->2 f_cpr.
case_distinction.

rewrite -> comp_assoc.
rewrite -> map_lifting.
rewrite -> f_cpr.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> map_comp.

rewrite -> coprodhom_comp.
rewrite -> prodhom_comp.
rewrite -> exphom_comp.
rewrite ->2 id_l.

rewrite -> cpr_inr.
rewrite -> exphom_id.
rewrite -> prodhom_id.
rewrite -> coprodhom_id.
rewrite -> map_id.

rewrite -> id_r.

rewrite <- comp_assoc with (h' := η).
rewrite -> comp_assoc with (g' := η).

rewrite -> map_unit.

rewrite -> comp_assoc with (g' := inr).
rewrite <- comp_assoc with (h' := η).

rewrite -> coprodhom_inr.

rewrite -> comp_assoc with (h' := η).
rewrite <- comp_assoc with (h' := η ∘ inr).

rewrite -> prodhom_comp.

rewrite -> id_r.

rewrite -> exphom_comp.
rewrite -> cpr_inl.
exact H0.

rewrite -> id_l.
rewrite -> comp_assoc.
rewrite -> map_comp.

rewrite -> coprodhom_comp.
rewrite -> prodhom_comp.
rewrite -> exphom_comp.

rewrite ->2 id_l.
rewrite -> cpr_inr.

rewrite -> exphom_id.
rewrite -> prodhom_id.
rewrite -> coprodhom_id.
rewrite -> map_id.

rewrite -> id_r.
reflexivity.

rewrite -> W.
symmetry.
apply coit2.

rewrite -> f_cpr.
rewrite -> id_l.
rewrite -> f_cpr.

rewrite ->2 comp_assoc.
rewrite -> map_comp.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
rewrite -> cpr_inr.
rewrite -> exphom_id.
rewrite -> prodhom_id.
rewrite -> coprodhom_id.
rewrite -> map_id.
rewrite -> id_r.
apply f_equal2;trivial.

rewrite -> map_lifting.
rewrite -> f_cpr.
rewrite -> comp_assoc with (f':=f).
rewrite -> comp_assoc.
rewrite -> map_comp.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
rewrite -> cpr_inr.
rewrite -> exphom_id.
rewrite -> prodhom_id.
rewrite -> coprodhom_id.
rewrite -> map_id.
rewrite -> id_r.

rewrite <- comp_assoc with (g':=inr).
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite -> comp_assoc with (g':=inr).
rewrite <- comp_assoc with (h':=η).
rewrite -> coprodhom_inr.
rewrite <-2 comp_assoc with (f':=id ×× inl ^^ id).
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
rewrite -> cpr_inl.
rewrite -> comp_assoc.
apply lifting1.
trivial.

apply f_equal1 with (f:= fun x => x ∘ inl) in H1.
rewrite ->2 cpr_inl in H1; trivial.

Qed.


Lemma guardedtriangular : forall 
(x y z a b : Obj) (f': x ~> coext T a b (y ⊕ x)), 
guarded f' -> ▷ f' = f'.
Proof.
intros.
unfold guarded in H0.
apply out_cong.

unfold triangular.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> out_tuo_is_id.
rewrite -> id_r.
rewrite <- comp_assoc with (g':=out).

inversion H0 as [u' H1].

rewrite -> H1.
apply f_equal1.
rewrite -> comp_assoc.
rewrite -> map_comp.
rewrite -> cpr_coprodhom.
rewrite -> coprodhom_inl.
rewrite -> id_l.
rewrite <- f_cpr.
rewrite -> inl_inr_is_id.
rewrite -> id_l.
rewrite -> mapinl_f_iter.
reflexivity.
Qed.


(* ▷ f is guarded by definition *)
Lemma guardedtriangular_def : forall
(x y a b : Obj) (f: x ~> coext T a b (y ⊕ x)),
guarded (▷ f).
Proof.
intros.
unfold guarded.
unfold triangular.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> out_tuo_is_id.
rewrite -> id_r.
rewrite <- comp_assoc with (g':=out).
apply ex_intro with (x:=(map ([inl ⊕⊕ id, inl ∘ inr]) ∘ (out ∘ f)) †).
reflexivity.
Qed.


Lemma itercofree_triangular : forall
(x y a b : Obj) (f: x ~> coext T a b (y ⊕ x)),
iter_cofree f = iter_cofree (▷ f).
Proof.
intros.
unfold triangular.
unfold iter_cofree.

rewrite <- comp_assoc with (h':=tuo).
rewrite -> comp_assoc with (g':=tuo).
rewrite <- comp_assoc with (f':=tuo).
rewrite -> out_tuo_is_id.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=map (inl ⊕⊕ id)).
rewrite -> map_comp.
rewrite -> cpr_coprodhom.
rewrite -> id_l.
rewrite -> coprodhom_inl.
rewrite <- f_cpr.
rewrite -> inl_inr_is_id.
rewrite -> id_l.
rewrite -> mapinl_f_iter.
reflexivity.
Qed.


Lemma liftingcofree_tuo : forall
(x y a b : Obj) (t:x ~> coext T a b y),
[ηv, t] § ∘ tuo = 
  tuo ∘ [[η ∘ inl, out ∘ t], 
η ∘ inr ∘ id ×× [ηv, t] § ^^ id] *.
Proof.
intros.
unfold lifting_cofree.
apply out_cong.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> coit1.
rewrite <-2 comp_assoc with (f':=map_cofree inl).
rewrite -> out_mapcofree.
rewrite <-3 comp_assoc with (f':=tuo).
rewrite -> out_tuo_is_id.
rewrite -> id_l.
rewrite <- comp_assoc.
rewrite -> lifting_map.
rewrite -> cpr_coprodhom.
rewrite <-2 comp_assoc with (f':=inl).
rewrite -> cpr_inl.

rewrite -> comp_assoc with (h':=out).
rewrite -> out_tuo_is_id.
rewrite -> id_r.

rewrite -> map_lifting.
apply f_equal1.
rewrite -> f_cpr.
rewrite ->2 comp_assoc.
rewrite -> map_comp.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.

rewrite -> comp_assoc with (f':=[[ηv, t], ηv]).
rewrite -> liftingdef_with_inr.
rewrite -> exphom_id.
rewrite -> prodhom_id.
rewrite -> coprodhom_id.
rewrite -> map_id.
rewrite -> id_r.
rewrite -> f_cpr.
rewrite -> out_unitcofree.
apply f_equal1.

rewrite <- comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=η).
rewrite -> map_unit.
rewrite -> comp_assoc with (g':=inr).
rewrite <- comp_assoc with (h':=η).
rewrite -> coprodhom_inr.
rewrite -> comp_assoc with (g':=inr).
rewrite <- comp_assoc with (h':=η ∘ inr).
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
reflexivity.
Qed.


Lemma unfolding_guarded1 :  forall
(x y a b : Obj) (f: x ~> coext T a b (y ⊕ x)),
guarded f ->
iter_cofree f = [ηv, iter_cofree f] § ∘ f.
Proof.
intros.
unfold guarded in H0.
inversion H0 as [u' H1].


(* Some preparation *)

remember (coit (([[η ∘ inl, u'], η ∘ inr]) * ∘ out)) as w eqn:W.
assert (iter_cofree f = w ∘ ηv ∘ inr).
unfold iter_cofree.

rewrite <- comp_assoc with (f':=inr).
rewrite <- comp_assoc with (f':=inr).
apply f_equal1 with (f:= fun x => x ∘ (ηv ∘ inr)).
rewrite <- comp_assoc with (g':=out).
rewrite -> H1.

rewrite -> comp_assoc.
rewrite -> map_comp.
rewrite -> cpr_coprodhom.
rewrite -> coprodhom_inl.
rewrite -> id_l.
rewrite <- f_cpr.
rewrite -> inl_inr_is_id.
rewrite -> id_l.
rewrite -> mapinl_f_iter.
rewrite -> W; trivial.

assert (ηv = (w ∘ ηv) ∘ inl).
rewrite -> W.
apply out_cong.
rewrite -> out_unitcofree.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> coit1.
rewrite -> comp_assoc with (f':=out).
rewrite -> map_lifting.
rewrite <- comp_assoc with (g':=out).
rewrite -> out_unitcofree.
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite <- comp_assoc.
rewrite <- comp_assoc.
rewrite -> comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite -> cpr_inl.
rewrite -> comp_assoc with (f':=inl).
rewrite -> map_unit.
rewrite <- comp_assoc.
rewrite -> coprodhom_inl.
rewrite -> id_l; trivial.

(* Main part *)


unfold iter_cofree at 1.

rewrite <- comp_assoc with (g':=out).
rewrite -> H1.

rewrite -> comp_assoc.
rewrite -> map_comp.
rewrite -> cpr_coprodhom.
rewrite -> coprodhom_inl.
rewrite -> id_l.
rewrite <- f_cpr.
rewrite -> inl_inr_is_id.
rewrite -> id_l.
rewrite -> mapinl_f_iter.

apply out_cong.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> coit1.

rewrite -> comp_assoc with (f':=f).
rewrite -> lifting1.

rewrite <- comp_assoc with (f':=f).

rewrite -> comp_assoc with (f':=out).
rewrite <- comp_assoc with (g':=out).
rewrite out_unitcofree.
rewrite -> comp_assoc with (f':=inl).
rewrite <- comp_assoc with (f':=η).
rewrite -> kl2.
rewrite <- comp_assoc with (f':=inl).
rewrite -> cpr_inl.
rewrite <- comp_assoc with (f':=inr).
rewrite -> cpr_inr.

(* since the introduction of cont, this doesn't work anymore TODO *)
Admitted.
(*
rewrite -> H1.

rewrite -> comp_assoc with (f':=u').
rewrite -> lifting_map.
unfold map at 1.

apply f_equal1 with (f:= fun x => x* ∘ u').
unfold coprodhom.
rewrite ->2 f_cpr.
case_distinction.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=inl).
rewrite -> cpr_inl.
rewrite <- comp_assoc with (f':=inl).
rewrite -> cpr_inl.
rewrite out_unitcofree; trivial.

rewrite -> id_l.
rewrite -> cpr_inr.
rewrite <- comp_assoc with (g':=inr).
apply f_equal1 with (f:= fun x => η ∘ (inr ∘ id ×× x ^^ id)).
rewrite <- W.
rewrite -> H2.
rewrite -> H3.
rewrite <- f_cpr.
rewrite -> inl_inr_is_id.
rewrite -> id_l.

(* Curious fact: w = (w ∘ ηv) §. May be needed in the future. *)

apply lifting2.
rewrite -> W at 1.

rewrite coit1.
rewrite <- W.

rewrite -> comp_assoc with (f':=out).
rewrite map_lifting.
unfold map at 1.
apply f_equal1 with (f:= fun x => x* ∘ out).
rewrite -> f_cpr.
case_distinction.
rewrite -> W at 2.
rewrite -> comp_assoc with (h':=out).
rewrite coit1.
rewrite <- W.
rewrite -> comp_assoc with (f':=out).
rewrite <- comp_assoc with (g':=out).
rewrite out_unitcofree.
rewrite -> comp_assoc with (g':=η).
rewrite <- comp_assoc with (f':=η).
rewrite -> kl2.
rewrite <- comp_assoc with (f':=inl).
rewrite -> cpr_inl.
unfold map; trivial.
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite <- comp_assoc.
rewrite -> coprodhom_inr.
rewrite <- comp_assoc; trivial.
Qed.
*)


Lemma unfolding_guarded2 :  forall
(x y a b : Obj) (f: x ~> coext T a b (y ⊕ x)) (g: x ~> coext T a b y),
guarded f -> g = [ηv, g] § ∘ f -> g = iter_cofree f.
Proof.
intros.

rewrite -> H1.
rewrite <- guardedtriangular with (f':=f) at 1;trivial.
unfold triangular.
rewrite ->2 comp_assoc.
rewrite -> liftingcofree_tuo.
unfold iter_cofree.

apply out_cong.
rewrite ->3 comp_assoc.
rewrite -> out_tuo_is_id.
rewrite -> id_r.
rewrite -> lifting_map.
rewrite -> cpr_coprodhom.
rewrite -> cpr_inl.
rewrite -> id_l.

rewrite ->2 comp_assoc.
rewrite -> coit1.
rewrite <-2 comp_assoc with (f':=ηv).
rewrite -> out_unitcofree.
rewrite -> comp_assoc with (g':=η).
rewrite -> kl2.
rewrite -> cpr_inl.
rewrite <- comp_assoc with (f':=inr).
rewrite -> cpr_inr.
apply f_equal2;trivial.
unfold map at 1.
apply f_equal1.
rewrite <- comp_assoc with (h':=η).
rewrite <- f_cpr.
apply f_equal2;trivial.
unfold coprodhom at 1.
rewrite -> id_l.
apply f_equal2;trivial.
apply f_equal2;trivial.
apply f_equal2;trivial.
apply f_equal2;trivial.

(* --- *)

apply coit2.
unfold lifting_cofree.
rewrite -> comp_assoc.
rewrite -> coit1.
rewrite <-3 comp_assoc.
rewrite -> out_mapcofree.
rewrite ->4 comp_assoc.
apply f_equal2;trivial.
rewrite ->2 map_lifting.
rewrite -> lifting_map.
apply f_equal1.
rewrite <- comp_assoc.
rewrite -> cpr_coprodhom.
rewrite <- comp_assoc with (f':=inl).
rewrite -> cpr_inl.

case_distinction.
rewrite ->2 comp_assoc.
rewrite -> map_comp.
rewrite -> coprodhom_comp.
rewrite -> id_l.
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
rewrite -> liftingdef_with_inr.
rewrite -> exphom_id.
rewrite -> prodhom_id.
rewrite -> coprodhom_id.
rewrite -> map_id.
rewrite -> id_r.

case_distinction.
rewrite -> out_unitcofree.
rewrite -> comp_assoc.
rewrite -> map_unit.
rewrite <- comp_assoc.
rewrite -> coprodhom_inl.
rewrite -> id_l.
trivial.

rewrite -> H1 at 1.
rewrite <- guardedtriangular with (f':=f) at 1;trivial.
unfold triangular.
rewrite <- comp_assoc with (h':=tuo).
rewrite -> comp_assoc with (g':=tuo).
rewrite -> liftingcofree_tuo.
rewrite ->3 comp_assoc.
rewrite -> out_tuo_is_id.
rewrite -> id_r.
rewrite -> lifting_map.
rewrite -> cpr_coprodhom.
rewrite -> cpr_inl.
rewrite -> id_l.
apply f_equal2;trivial.
unfold map at 1.
apply f_equal1.
apply coprodsplit.
rewrite -> cpr_inl.
rewrite <- comp_assoc with (f':=inl).
rewrite -> coprodhom_inl.
rewrite -> id_l.
trivial.
rewrite -> cpr_inr.
rewrite <- comp_assoc with (f':=inr).
rewrite -> coprodhom_inr.
rewrite -> comp_assoc with (h':=η).
trivial.
(* solved, because right side was equal, but the lifting unfolded *)

rewrite <- comp_assoc with (h':=η).
rewrite ->2 comp_assoc with (g':=η).
rewrite ->2 map_unit.
rewrite <-2 comp_assoc with (h':=η).
rewrite -> comp_assoc with (g':=inr).
rewrite ->2 coprodhom_inr.
rewrite <- comp_assoc with (h':=inr).
rewrite -> prodhom_comp.
rewrite -> id_l.
rewrite -> exphom_comp.
reflexivity.
Qed.



Lemma unfolding_triangular1 : forall
(x y a b : Obj) (f: x ~> coext T a b (y ⊕ x)),
iter_cofree f = [ηv, iter_cofree f] § ∘ ▷ f.
Proof.
intros.
pose proof guardedtriangular_def (_) (_) (_) (_) (f).
pose proof unfolding_guarded1 (_) (_) (_) (_) (▷f).
rewrite <- itercofree_triangular in H1.
apply H1.
apply H0.
Qed.




Lemma unfolding_triangular2 : forall
(x y a b : Obj) (f: x ~> coext T a b (y ⊕ x)) (g: x ~> coext T a b y),
g = [ηv, g] § ∘ ▷ f ->
g = iter_cofree f.
Proof.
intros.
rewrite -> itercofree_triangular.
apply unfolding_guarded2.
apply guardedtriangular_def.
apply H0.
Qed.




Lemma out_itercofree : forall 
(x y a b : Obj) (f: x ~> coext T a b (y ⊕ x)),
out ∘ iter_cofree f = ([η ∘ inl,
    (η ∘ inr) ∘ id ×× [ηv, iter_cofree f] § ^^ id]) *
∘ ((map ([inl ⊕⊕ id, inl ∘ inr]) ∘ out) ∘ f) †.
Proof.
intros.
rewrite -> unfolding_triangular1 at 1.
rewrite -> comp_assoc.
rewrite -> lifting1.
unfold triangular.
rewrite <- comp_assoc with (h':=tuo).
rewrite -> comp_assoc with (g':=tuo).
rewrite <- comp_assoc with (f':=tuo).
rewrite -> out_tuo_is_id.
rewrite -> id_l.
rewrite -> comp_assoc with (g':=map (inl ⊕⊕ id)).
rewrite -> lifting_map.
rewrite -> cpr_coprodhom.
rewrite <- comp_assoc with (f':=inl).
rewrite -> cpr_inl.
rewrite -> out_unitcofree.
rewrite -> id_l.
reflexivity.
Qed.



Lemma strength1 : forall
(x y a b : Obj),
out ∘ τv (x:=x) (y:=y) (a:=a) (b:=b) = map (id ⊕⊕ id ×× τv ^^ id) ∘ map δ ∘ τ ∘ (id ×× out).
Proof.
intros.
unfold τv.
rewrite -> coit1.
rewrite ->2 comp_assoc.
reflexivity.
Qed.


Lemma strength2 : forall
(x y a b : Obj) (f: x × (coext T a b y) ~> coext T a b (x × y)),
out ∘ f = map (id ⊕⊕ id ×× f ^^ id) ∘ map δ ∘ τ ∘ (id ×× out) ->
f = τv.
Proof.
intros.
unfold τv.
apply coit2.
rewrite ->2 comp_assoc.
apply H0.
Qed.

End Lemmas.