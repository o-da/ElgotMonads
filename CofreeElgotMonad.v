Add LoadPath "~/Schreibtisch/svnba/Elgot/Coq/".
Require Import ElgotMonad.
Require Import Lemmas_ElgotMonad.
Open Scope elgot_scope.

(* Lemma 3.6 *)
Class CofreeElgotMonad (Obj: Type) (Hom: Obj -> Obj -> Type) (T: Obj -> Obj) (E: ElgotMonad Obj Hom T) := {
    coext : (Obj -> Obj) -> Obj -> Obj -> Obj -> Obj;
    cont (a b x : Obj) : Obj := a × x $ b;

    out : forall (x a b: Obj),
        coext T a b x ~> T (x ⊕ cont a b (coext T a b x));
    coit : forall x a b A (f: A ~> T (x ⊕ cont a b A)),
        A ~> coext T a b x;


    tuo (x a b : Obj) : T (x ⊕ cont a b (coext T a b x)) ~> coext T a b x := coit _ _ _ _ (map (id ⊕⊕ (id ×× ((out x a b) ^^ id))));

    ηv (x a b : Obj) : x ~> coext T a b x := ((tuo _ _ _) ∘ η ∘ inl);

    map_cofree (x y a b : Obj) (f: x ~> y) : coext T a b x ~> coext T a b y :=
        (coit _ _ _ _ (map (f ⊕⊕ id) ∘ (out _ _ _)));

    lifting_cofree (x y a b : Obj) (f: x ~> coext T a b y) : coext T a b x ~> coext T a b y :=
        (coit _ _ _ _ ([map (id ⊕⊕ id ××  (map_cofree _ _ _ _ inr) ^^ id) ∘ (out _ _ _) ∘ [f, (ηv _ _ _)],
        η ∘ inr] * ∘ (out _ _ _)) ∘ (map_cofree _ _ _ _ inl));

    triangular (x y a b : Obj) (f: x ~> coext T a b (y ⊕ x)) : x ~> coext T a b (y ⊕ x) :=
        (tuo _ _ _) ∘ map (inl ⊕⊕ id) ∘ (map ([inl ⊕⊕ id, inl ∘ inr]) ∘ (out _ _ _) ∘ f) †;


    iter_cofree (x y a b : Obj) (f: x ~> coext T a b (y ⊕ x)) : x ~> coext T a b y :=
        coit _ _ _ _ ([[η ∘ inl, (map ([inl ⊕⊕ id, inl ∘ inr]) ∘ (out _ _ _) ∘ f) †], η ∘ inr]* ∘ (out _ _ _)) ∘ (ηv _ _ _ ) ∘ inr;



    δ (x y z a b : Obj) : x × (y ⊕ cont a b z) ~> (x × y) ⊕ cont a b (x × z);
    τv (x y a b : Obj) : x × (coext T a b y) ~> coext T a b (x × y) :=
        coit _ _ _ _ (map (δ _ _ _ _ _) ∘ τ ∘ (id ×× (out _ _ _)));
       


    coit1 : forall x a b A (f: A ~> T (x ⊕ cont a b A)),
        (out _ _ _) ∘ (coit _ _ _ _ f) = 
          (map (id ⊕⊕ id ×× (coit _ _ _ _ f) ^^ id)) ∘ f;

    coit2 : forall x a b A (f: A ~> T (x ⊕ cont a b A)) (g: A ~> coext T a b x),
        (out _ _ _) ∘ g = 
          (map (id ⊕⊕ id ×× g ^^ id)) ∘ f ->
        g = (coit _ _ _ _ f)

(*   
    strengthcofree1 : forall x y a b,
        (out _ _ _) ∘ (τv _ _ _ _) = map (id ⊕⊕ (id ×× (τv _ _ _ _) ^^ id)) ∘ map (dist2) ∘ τ ∘ (id ×× (out _ _ _)); 

    strengthcofree2 : forall x y a b (g: x × coext T a b y ~> coext T a b (x × y)),
        (out _ _ _) ∘ g = map (id ⊕⊕ id ×× g ^^ id) ∘ map (dist2) ∘ τ ∘ (id ×× (out _ _ _))
          g = (τv _ _ _ _)
*)
(*
    codiag_assoc_helper_cofree : forall w x y z a b (f: w ~> coext T a b ((x ⊕ y) ⊕ z)), w ~> coext T a b (x ⊕ (y ⊕ z))
*)
}.

Arguments out [Obj Hom0 T E CofreeElgotMonad x a b].
Arguments coit [Obj Hom0 T E CofreeElgotMonad x a b A] f.
Arguments tuo [Obj Hom0 T E CofreeElgotMonad x a b].
Arguments ηv [Obj Hom0 T E CofreeElgotMonad x a b].
Arguments map_cofree [Obj Hom0 T E CofreeElgotMonad x y a b] f.
Arguments lifting_cofree [Obj Hom0 T E CofreeElgotMonad x y a b] f.
Arguments iter_cofree [Obj Hom0 T E CofreeElgotMonad x y a b] f.
Arguments triangular [Obj Hom0 T E CofreeElgotMonad x y a b] f.
Arguments δ [Obj Hom0 T E CofreeElgotMonad x y z a b].
Arguments τv [Obj Hom0 T E CofreeElgotMonad x y a b].

Notation "a §" := (lifting_cofree a) (at level 35) :elgot_scope.
Notation "▷ a" := (triangular a)     (at level 35) :elgot_scope.

Section Guardedness.
Context `(C: CofreeElgotMonad).

Definition guarded
  (x y z a b : Obj) 
  (f: x ~> coext T a b (y ⊕ z)) 
  : Prop :=
    exists (u : x ~> T (y ⊕ cont a b (coext T a b (y ⊕ z)))),
    out ∘ f = map (inl ⊕⊕ id) ∘ u.

End Guardedness.

Arguments guarded [Obj Hom0 T E C x y z a b] f.
