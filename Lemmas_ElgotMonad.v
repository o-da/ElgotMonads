Add LoadPath "~/Schreibtisch/svnba/Elgot/Coq/".
Require Import ElgotMonad.
Open Scope elgot_scope.
Section Lemmas.
Context `(ElgotMonad).

(* Lemmas proven in the following:

map_id:
  map id (a:=x) = id

map_comp:
   map f ∘ map g = map (f ∘ g)

prodhom_id:
  id (a:=x) ×× id (a:=y) = id

prodhom_comp:
  f ×× h ∘ g ×× i = (f ∘ g) ×× (h ∘ i)

coprodhom_id:
  id (a:=x) ⊕⊕ id (a:=y) = id

coprodhom_comp:
  f ⊕⊕ h ∘ g ⊕⊕ i = (f ∘ g) ⊕⊕ (h ∘ i)

prodhom_pair:
  h ×× i ∘ pair f g = pair (h ∘ f) (i ∘ g)

pr1_prodhom:
  pr1 ∘ f ×× g =  f ∘ pr1

pr2_prodhom:
  pr2 ∘ f ×× g =  g ∘ pr2

cpr_coprodhom:
  [ f , g ] ∘ h ⊕⊕ i = [ f ∘ h , g ∘ i ]

coprodhom_inl:
  f ⊕⊕ g ∘ inl = inl ∘ f

coprodhom_inr:
  f ⊕⊕ g ∘ inr = inr ∘ g

prodhom_id2_l:
  f = h -> f ×× g = h ×× g

prodhom_id2_r:
   g = h -> f ×× g = f ×× h

coprodhom_id2_l:
  f = h -> f ⊕⊕ g = h ⊕⊕ g

coprodhom_id2_r:
  g = h -> f ⊕⊕ g = f ⊕⊕ h

coprodsplit:
  p ∘ inl = q ∘ inl -> p ∘ inr = q ∘ inr -> p = q

prodsplit:
  pr1 ∘ p = pr1 ∘ q -> pr2 ∘ p = pr2 ∘ q -> p = q

curry_of_uncurry:
  curry (uncurry f) = f

uncurry_of_curry:
  uncurry (curry f) = f

uncurry1:
  uncurry p = uncurry q -> p = q

curry2:
  curry p = curry q -> p = q

exphom_id:
  id ^^ id = id

exphom_id2:
  g = h -> g ^^ f = h ^^ f

curry_ev_comp:
  curry (f ∘ ev) ∘ curry (g ∘ ev) = curry (f ∘ g ∘ ev)

f_times_id_is_curry_f_ev:
  f ^^ id = curry (f ∘ ev)

exphom_comp:
  f ^^ id ∘ g ^^ id = (f ∘ g) ^^ id 

lifting_map:
  f * ∘ map g = (f ∘ g) *

map_unit:
  map f ∘ η = η ∘ f

map_lifting:
  map f ∘ g * = (map f ∘ g)*

map_id2:
  f = id -> map f = id

mapinl_f_iter:
  (map inl ∘ f) † = f

*)

Lemma map_id : forall
(x : Obj),
map id (a:=x) = id.
Proof.
intros.
unfold map.
rewrite -> id_l.
rewrite -> kl1.
reflexivity.
Qed.

Lemma map_comp : forall
(x y z : Obj) (f: y ~> z) (g: x ~> y),
map f ∘ map g = map (f ∘ g).
Proof.
intros.
unfold map.
rewrite <- kl3.
rewrite -> comp_assoc.
rewrite -> kl2.
rewrite -> comp_assoc.
reflexivity.
Qed.


Lemma prodhom_id : forall
(x y : Obj),
id (a:=x) ×× id (a:=y) = id.
Proof.
intros.
unfold prodhom.
rewrite -> id_r.
rewrite -> id_r.
rewrite -> pr1_pr2_is_id.
reflexivity.
Qed.


Lemma prodhom_comp : forall 
(x y z a b c : Obj) (f: y ~> z) (g: x ~> y) (h: b ~> c) (i: a ~> b),
f ×× h ∘ g ×× i = (f ∘ g) ×× (h ∘ i).
Proof.
intros.
unfold prodhom.
rewrite -> pair_f.
rewrite <- comp_assoc.
rewrite -> pr1_pair.
rewrite <- comp_assoc.
rewrite -> pr2_pair.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
reflexivity.
Qed.

Lemma coprodhom_id : forall
(x y : Obj),
id (a:=x) ⊕⊕ id (a:=y) = id.
Proof.
intros.
unfold coprodhom.
rewrite -> id_l.
rewrite -> id_l.
rewrite -> inl_inr_is_id.
reflexivity.
Qed.


Lemma coprodhom_comp : forall 
(x y z a b c : Obj) (f: y ~> z) (g: x ~> y) (h: b ~> c) (i: a ~> b),
f ⊕⊕ h ∘ g ⊕⊕ i = (f ∘ g) ⊕⊕ (h ∘ i).
Proof.
intros.
unfold coprodhom.
rewrite -> f_cpr.
rewrite -> comp_assoc.
rewrite -> cpr_inl.
rewrite -> comp_assoc.
rewrite -> cpr_inr.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
reflexivity.
Qed.

Lemma prodhom_pair : forall 
(v w x y z : Obj) (f : x ~> y) (g: x ~> z) (h: y ~> x) (i: z ~> x),
h ×× i ∘ pair f g = pair (h ∘ f) (i ∘ g).
Proof.
intros.
unfold prodhom.
rewrite -> pair_f.
rewrite <- comp_assoc.
rewrite <- comp_assoc.
rewrite -> pr1_pair.
rewrite -> pr2_pair.
reflexivity.
Qed.


Lemma pr1_prodhom : forall 
(a b c d : Obj) (f : a ~> b) (g: c ~> d),
pr1 ∘ f ×× g =  f ∘ pr1.
Proof.
intros.
unfold prodhom.
rewrite -> pr1_pair.
reflexivity.
Qed.

Lemma pr2_prodhom : forall 
(a b c d : Obj) (f : a ~> b) (g: c ~> d),
pr2 ∘ f ×× g =  g ∘ pr2.
Proof.
intros.
unfold prodhom.
rewrite -> pr2_pair.
reflexivity.
Qed.


Lemma cpr_coprodhom : forall 
(v w x y z : Obj) (f : x ~> z) (g: y ~> z) (h: v ~> x) (i: w ~> y),
[ f , g ] ∘ h ⊕⊕ i = [ f ∘ h , g ∘ i ].
Proof.
intros.
unfold coprodhom.
rewrite -> f_cpr.
rewrite -> comp_assoc.
rewrite -> comp_assoc.
rewrite -> cpr_inl.
rewrite -> cpr_inr.
reflexivity.
Qed.


Lemma coprodhom_inl : forall 
(a b c d : Obj) (f : a ~> b) (g: c ~> d),
(f ⊕⊕ g) ∘ inl = inl ∘ f.
Proof.
intros.
unfold coprodhom.
rewrite -> cpr_inl.
reflexivity.
Qed.

Lemma coprodhom_inr : forall 
(a b c d : Obj) (f : a ~> b) (g: c ~> d),
f ⊕⊕ g ∘ inr = inr ∘ g.
Proof.
intros.
unfold coprodhom.
rewrite -> cpr_inr.
reflexivity.
Qed.


Lemma coprodsplit : forall
(a b c : Obj) (p: a ⊕ b ~> c) (q: a ⊕ b ~> c),
p ∘ inl = q ∘ inl -> p ∘ inr = q ∘ inr -> p = q.
Proof.
intros.
rewrite <- id_l.
symmetry.
rewrite <- id_l.
rewrite <- inl_inr_is_id.
rewrite -> f_cpr.
rewrite -> f_cpr.
rewrite -> H0.
rewrite -> H1.
reflexivity.
Qed.


Lemma prodsplit : forall
(a b c : Obj) (p: c ~> a × b) (q: c ~> a × b),
pr1 ∘ p = pr1 ∘ q -> pr2 ∘ p = pr2 ∘ q -> p = q.
Proof.
intros.
rewrite <- id_r.
symmetry.
rewrite <- id_r.
rewrite <- pr1_pr2_is_id.
rewrite -> pair_f.
rewrite -> pair_f.
rewrite -> H0.
rewrite -> H1.
reflexivity.
Qed.


Lemma curry_of_uncurry : forall
(a b c : Obj) (f: a ~> c $ b),
curry (uncurry f) = f.
Proof.
intros.
unfold uncurry.
rewrite <- curry1.
rewrite -> curry_ev_is_id.
rewrite -> id_r.
reflexivity.
Qed.


Lemma uncurry_of_curry : forall
(a b c : Obj) (f: a × b ~> c),
uncurry (curry f) = f.
Proof.
intros.
unfold uncurry.
rewrite <- ev1.
reflexivity.
Qed.


Lemma uncurry1 : forall
(a b c : Obj) (p: a ~> c $ b) (q: a ~> c $ b),
uncurry p = uncurry q -> p = q.
Proof.
intros.
rewrite <- curry_of_uncurry.
symmetry.
rewrite <- curry_of_uncurry.
rewrite -> H0.
reflexivity.
Qed.


Lemma curry2 : forall
(a b c : Obj) (p: a × b ~> c) (q: a × b ~> c),
curry p = curry q -> p = q.
Proof.
intros.
rewrite <- uncurry_of_curry.
symmetry.
rewrite <- uncurry_of_curry.
rewrite -> H0.
reflexivity.
Qed.


Lemma exphom_id : forall
(x y : Obj),
id (a:=x) ^^ id (a:=y) = id.
Proof.
intros.
unfold exphom.
rewrite -> id_r.
rewrite -> prodhom_id.
rewrite -> id_l.
rewrite -> curry_ev_is_id.
rewrite -> prodhom_id.
rewrite -> id_l.
rewrite -> curry_ev_is_id.
reflexivity.
Qed.


Lemma curry_ev_comp : forall 
(x y z b : Obj) (f: y ~> z) (g: x ~> y),
curry (f ∘ ev) ∘ curry (g ∘ ev) = curry (f ∘ g ∘ ev (b:=b)).
Proof.
intros.
rewrite -> curry1.
rewrite <- comp_assoc.
rewrite <- ev1.
rewrite -> comp_assoc.
reflexivity.
Qed.

Lemma f_times_id_is_curry_f_ev : forall
(a b c : Obj) (f: a ~> b),
f ^^ id = curry (f ∘ ev (b:=c)).
Proof.
intros.
unfold exphom.
rewrite <- curry1.
rewrite -> curry_ev_is_id.
rewrite -> id_r.
rewrite -> prodhom_id.
rewrite -> id_l.
reflexivity.
Qed.


Lemma exphom_comp : forall
(x y z b : Obj) (f: y ~> z) (g: x ~> y),
f ^^ id ∘ g ^^ id = (f ∘ g) ^^ id (a:=b).
Proof.
intros.
repeat rewrite -> f_times_id_is_curry_f_ev.
apply curry_ev_comp.
Qed.


Lemma lifting_map : forall 
(x y z : Obj) (f: y ~> T z) (g: x ~> y),
f * ∘ map g = (f ∘ g) *.
Proof.
intros.
unfold map.
rewrite <- kl3.
rewrite -> comp_assoc.
rewrite -> kl2.
reflexivity.
Qed.


Lemma map_unit : forall
(x y : Obj) (f: x ~> y),
map f ∘ η = η ∘ f.
Proof.
intros.
unfold map.
rewrite -> kl2.
reflexivity.
Qed.

Lemma map_lifting : forall
(x y z : Obj) (f: y ~> z) (g: x ~> T y),
map f ∘ g * = (map f ∘ g)*.
Proof.
intros.
unfold map.
rewrite <- kl3.
reflexivity.
Qed.


Lemma mapinl_f_iter : forall
(x y : Obj) (f: x ~> T y),
(map inl ∘ f) † = f.
Proof.
intros.
rewrite <- unfolding.
rewrite -> comp_assoc.
rewrite -> lifting_map.
rewrite -> cpr_inl.
rewrite -> kl1.
rewrite -> id_r.
reflexivity.
Qed.

End Lemmas.

(* Tactics definitions *)

Ltac case_distinction := 
apply coprodsplit; 
[try rewrite <-2 comp_assoc with (f':=inl) | try rewrite <-2 comp_assoc with (f':=inr)];
[try rewrite ->2 cpr_inl | try rewrite ->2 cpr_inr].
