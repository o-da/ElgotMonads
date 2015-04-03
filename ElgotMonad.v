(*Reserving Notations*)
Reserved Notation "a ~> b" (at level 70, right associativity).
Reserved Notation "a × b" (at level 14).
Reserved Notation "a ⊕ b" (at level 15).
Reserved Notation "a $ b" (at level 13).
Reserved Notation "a ×× b" (at level 44).
Reserved Notation "a ⊕⊕ b" (at level 45).
Reserved Notation "a ^^ b" (at level 43).
Reserved Notation "[ a , b ]" (at level 51).
Reserved Notation "< a , b >" (at level 50).
Reserved Notation "a ∘ b" (at level 65).
Reserved Notation "a *" (at level 35).
Reserved Notation "a †" (at level 36).

(* TODO: pair notation not working *)
Class ElgotMonad (Obj : Type) (Hom: Obj -> Obj -> Type) (T : Obj -> Obj) := 
{ 
  (* Type constructors *)
  Hom  where "a ~> b" := (Hom a b);
  prod : Obj -> Obj -> Obj  where "a × b" := (prod a b);
  coprod : Obj -> Obj -> Obj  where "a ⊕ b" := (coprod a b);
  exp : Obj -> Obj -> Obj  where "a $ b" := (exp a b);
  terminal_obj : Obj;


  (* primitives *)

  (* composition *)
  comp : forall a b c (f: b ~> c) (g: a ~> b), (a ~> c)  
    where "a ∘ b" := (comp _ _ _ a b);
  (* id' *)
  id : forall a, a ~> a;
  (* pair and copair *)
  pair : forall a b c (f : a ~> b) (g: a ~> c), a ~> (prod b c)  
    where "< a , b >" := (pair _ _ _ a b); 
  cpr : forall a b c (f : a ~> c) (g: b ~> c), (coprod a b) ~> c  
    where "[ a , b ]" := (cpr _ _ _ a b);
  (* injections in coproducts *)
  inl : forall a b, a ~> (a ⊕ b);
  inr : forall a b, b ~> (a ⊕ b);
  (* projections from products *)
  pr1 : forall a b, (a × b) ~> a;
  pr2 : forall a b, (a × b) ~> b;
  (* unit *)
  η : forall a, a ~> T a;
  (* Kleisli lifting *)
  lifting : forall a b (f : a ~> T b), T a ~> T b 
    where "a *" := (lifting _ _ a);
  (* strength *)
  τ : forall a b, (a × T b) ~> T (a × b);
  (* iteration *)
  iter : forall a b (f :  a ~> T (b ⊕ a)), a ~> T b 
    where "a †" := (iter _ _ a);
  (* strong iteration *)
  (* not yet implemented *)
  ev : forall a b, (a $ b)  × b ~> a;
  curry : forall a b c (f: a × b ~> c), a ~> c $ b;
  (* bang *)
  bang : forall a, a ~> terminal_obj;

  (* definitions *)
  prodhom (a b c d : Obj) (f: a ~> b) (g: c ~> d) : (a × c) ~> (b × d) := 
    pair _ _ _ (f ∘ (pr1 _ _)) (g ∘ (pr2 _ _))
      where "f ×× g" := (prodhom _ _ _ _ f g);
  coprodhom (a b c d : Obj) (f: a ~> b) (g: c ~> d) : (a ⊕ c) ~> (b ⊕ d) :=
    [ (inl _ _) ∘ f , (inr _ _) ∘ g ]
      where "f ⊕⊕ g" := (coprodhom _ _ _ _ f g);
  exphom (a b c d : Obj) (f: a ~> b) (g: d ~> c) : (a $ c) ~> (b $ d) := 
    (curry _ _ _ ((ev _ _)  ∘ (prodhom _ _ _ _ (curry _ _ _ (f ∘ (ev _ _)  ∘ 
    (prodhom _ _ _ _ (id _) g))) (id _))))
      where "f ^^ g" := (exphom _ _ _ _ f g);
  post_comp (x y b : Obj) (f: x ~> y) : (x $ b) ~> (y $ b) :=
    curry _ _ _ (f ∘ (ev _ _));
  codiag (a : Obj) : a ⊕ a ~> a :=
    [ (id _) , (id _) ]; 
  map (a b : Obj) (f: a ~> b) : T a ~> T b :=
    ((η _) ∘ f)*;
  ret (a b : Obj) (f: a ~> b) : a ~> T b :=
    (η _) ∘ f;
  uncurry (a b c : Obj) (f: a ~> c $ b) : a × b ~> c := 
    (ev _ _) ∘ (f ×× (id _));

  dist1 : forall x y z, (z × y) ⊕ (z × x) ~> z × (y ⊕ x);
  dist2 : forall x y z, z × (y ⊕ x) ~> (z × y) ⊕ (z × x);
  prod_assoc1 : forall a b c, (a × b) × c ~> a × (b × c);
  prod_assoc2 : forall a b c, a × (b × c) ~> (a × b) × c;
  coprod_assoc1 : forall a b c, (a ⊕ b) ⊕ c ~> a ⊕ (b ⊕ c);
  coprod_assoc2 : forall a b c, a ⊕ (b ⊕ c) ~> (a ⊕ b) ⊕ c;
  codiag_assoc_helper : forall a b c x (f: x ~> T ((a ⊕ b) ⊕ c)), x ~> T (a ⊕ (b ⊕ c));


  (* laws *)

  (* composition is associative *)
  comp_assoc : forall a b c d (f' : a ~> b) (g' : b ~> c) (h' : c ~> d), 
    h' ∘ (g' ∘ f') = (h' ∘ g') ∘ f';
  (* left and right side identity *)
  id_l : forall a b (f : a ~> b), 
    f ∘ (id _) = f;
  id_r : forall a b (f : a ~> b), 
    (id _) ∘ f = f;
  (* laws of Kleisli triple for unit and lifting *)
  kl1 : forall a, 
    (η a) * = id (T a);
  kl2 : forall a b (f: a ~> T b), 
    f * ∘ (η _) = f;
  kl3 : forall a b c (f : b ~> T c) (g : a ~> T b), 
    (f * ∘ g) * = f * ∘ g *;
  (* laws of an Elgot Monad *)
  unfolding : forall a b (f : a ~> T (b ⊕ a)), 
    [ (η _) , f † ] * ∘ f = f †;
  naturality : forall a b c (f : a ~> T (b ⊕ a))(g : b ~> T c), 
    g * ∘ f † = ([ ((η _) ∘ (inl _ _))* ∘ g  , ((η _) ∘ (inr _ _)) ] * ∘ f) †;
  dinaturality : forall a b c (g : a ~> T (b ⊕ c)) (h : c ~> T (b ⊕ a)),
    ([ (η _) ∘ (inl _ _) , h ] * ∘ g) † =
    [ (η _) , ([ (η _) ∘ (inl _ _) , g ] * ∘ h) † ] * ∘ g;
  codiagonal : forall a b (g: a ~> T (b ⊕ a ⊕ a)),
    (((η _) ∘ (id _) ⊕⊕ (codiag _))* ∘ (codiag_assoc_helper _ _ _ _ g)) † = g † †;
  uniformity : forall a b c (f : a ~> T (b ⊕ a)) (g: c ~> T (b ⊕ c)) (h: c ~> a),
    f ∘ h = ((η _) ∘ (id _) ⊕⊕ h)* ∘ g ->
    f † ∘ h = g †;
  (* strength is compatible with iteration *)
  strength_iteration : forall a b (f: a ~> T (b ⊕ a)), 
    (τ _ _) ∘ (id _) ×× (f †) = 
    (((η _) ∘ (dist2 _ _ _))* ∘ (τ _ _) ∘ (id a) ×× f) †;
  (* strongiteration *)
  (* not yet implemented *)
  (* laws for strength *)
  str1 : forall a b,
    pr2 a (T b) = ((η _) ∘ (pr2 _ _))* ∘ (τ _ _);
  str2 : forall a b c,
    ((η _) ∘ (prod_assoc1 _ _ _))* ∘ (τ (prod a b) (T (T c))) = (τ _ _) ∘ (id _) ×× (τ _ _) ∘ (prod_assoc1 _ _ _);
  str3 : forall a b,
    (τ a b) ∘ (id _) ×× (η _) = η _;
  str4 : forall a b (f: (T a) ~> T (T b)),
    ((τ _ _) ∘ (id _) ×× f) * ∘ (τ _ _) = (τ _ _) ∘ (id a) ×× f *;

  f_cpr : forall a b c d (f: c ~> d) (g: a ~> c) (h: b ~> c),
    f ∘ [ g , h ] = [ f ∘ g , f ∘ h ];
  cpr_inl : forall a b c (f: a ~> c) (g: b ~> c),
    [f , g] ∘ (inl _ _) = f;
  cpr_inr : forall a b c (f: a ~> c) (g: b ~> c),
    [f , g] ∘ (inr _ _) = g;
  inl_inr_is_id : forall (a b : Obj),
    [(inl a b), (inr _ _)] = id _;

  pair_f : forall a b c d (f: b ~> c) (g: b ~> d) (h: a ~> b),
    pair _ _ _ f g ∘ h = pair _ _ _ (f ∘ h) (g ∘ h);
  pr1_pair : forall a b c (f : a ~> b) (g: a ~> c),
    pr1 _ _ ∘ pair _ _ _ f g = f;
  pr2_pair : forall a b c (f : a ~> b) (g: a ~> c),
    pr2 _ _ ∘ pair _ _ _ f g = g;
  pr1_pr2_is_id : forall (a b : Obj),
    pair _ _ _ (pr1 _ _) (pr2 a b) = (id _);

  curry_ev_is_id : forall a b,
    curry _ _ _ (ev a b) = id _;
  ev1 : forall a b c (f: a × b ~> c),
    f = (ev _ _) ∘ (curry _ _ _ f ×× (id _));
  curry1 : forall a b c d (f: d ~> a) (g: a × b ~> c),
    (curry _ _ _ g) ∘ f = curry _ _ _ (g ∘ f ×× (id _));

  bang_axiom : forall a (f: a ~> terminal_obj),
    f = bang _
   

}.

Parameter Object : forall Obj (hom : Obj -> Obj -> Type) (T : Obj -> Obj), ElgotMonad Obj hom T -> Type.
Coercion Object : ElgotMonad >-> Sortclass.

Bind Scope elgot_scope with ElgotMonad.

Arguments id [Obj Hom0 T ElgotMonad a].
Arguments inl [Obj Hom0 T ElgotMonad a b].
Arguments inr [Obj Hom0 T ElgotMonad a b].
Arguments pr1 [Obj Hom0 T ElgotMonad a b].
Arguments pr2 [Obj Hom0 T ElgotMonad a b].
Arguments τ [Obj Hom0 T ElgotMonad a b].
Arguments ev [Obj Hom0 T ElgotMonad a b].
Arguments curry [Obj Hom0 T ElgotMonad a b c] f.
Arguments η [Obj Hom0 T ElgotMonad a].
Arguments bang [Obj Hom0 T ElgotMonad a].

Arguments cpr [Obj Hom0 T ElgotMonad a b c] f g.
Arguments pair [Obj Hom0 T ElgotMonad a b c] f g.
Arguments comp [Obj Hom0 T ElgotMonad a b c] f g.
Arguments lifting [Obj Hom0 T ElgotMonad a b] f.
Arguments iter [Obj Hom0 T ElgotMonad a b] f.

Arguments prodhom [Obj Hom0 T ElgotMonad a b c d] f g.
Arguments coprodhom [Obj Hom0 T ElgotMonad a b c d] f g.
Arguments exphom [Obj Hom0 T ElgotMonad a b c d] f g.
Arguments post_comp [Obj Hom0 T ElgotMonad x y] b f.
Arguments codiag [Obj Hom0 T ElgotMonad a].
Arguments map [Obj Hom0 T ElgotMonad a b] f.
Arguments ret [Obj Hom0 T ElgotMonad a b] f.
Arguments uncurry [Obj Hom0 T ElgotMonad a b c] f.

Arguments dist1 [Obj Hom0 T ElgotMonad x y z].
Arguments dist2 [Obj Hom0 T ElgotMonad x y z].
Arguments prod_assoc1 [Obj Hom0 T ElgotMonad a b c].
Arguments prod_assoc2 [Obj Hom0 T ElgotMonad a b c].
Arguments coprod_assoc1 [Obj Hom0 T ElgotMonad a b c].
Arguments coprod_assoc2 [Obj Hom0 T ElgotMonad a b c].


Notation "a ^ b" := (exp a b)                    :elgot_scope.
Notation "a ~> b" := (Hom a b)                   :elgot_scope.
Notation "a × b" := (prod a b)                   :elgot_scope.
Notation "a ⊕ b" := (coprod a b)                 :elgot_scope.
Notation "a $ b" := (exp a b)                    :elgot_scope.
Notation "[ a , b ]" := (cpr a b)                :elgot_scope.
Notation "< a , b >" := (pair a b)               :elgot_scope.
Notation "a ∘ b" := (comp a b)                   :elgot_scope.
Notation "a *" := (lifting a)                    :elgot_scope.
Notation "a †" := (iter a)                       :elgot_scope.
Notation "f ×× g" := (prodhom f g)               :elgot_scope.
Notation "f ⊕⊕ g" := (coprodhom f g)             :elgot_scope.
Notation "f ^^ g" := (exphom f g)                :elgot_scope.
Notation "∇" := codiag              (at level 11):elgot_scope.


