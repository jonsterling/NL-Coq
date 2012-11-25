Require Import String EquivDec Bool Datatypes.
Set Implicit Arguments.

Module Utilities.
  Ltac derive_eq := intros x y; change ({x = y} + {x <> y}); decide equality.
  Definition option_flatMap {a b : _} (f : a -> option b) (x : option a) :=
    match x with
      | Some x => f x
      | None   => None
    end.
End Utilities.

Module CoreTheory.
  Import Utilities.

  (** We'll start with a few syntactic categories. This is of course
  not sufficient to do real syntax, but it will do for now. *)
  Inductive category := D | N | V.
  Instance cat_eq_eqdec : EqDec category eq. derive_eq. Defined.

  (** Each constituent is marked by a set of features; in our current
  theory, features are just a syntactic category, and specifications
  for internal and external arguments. *)

  Inductive arg (rep : Set) :=
    | sat   : arg rep
    | unsat : rep -> arg rep.
  Arguments sat [rep].

  Definition arguments (rep : Set) := option (arg rep * (option (arg rep))).
  Inductive features : Set := { cat : category ; args : arguments features }.

  (** In our current theory, there are two kinds of arguments:
  internal and external; an internal argument is lower in the tree
  than the head, whereas an external argument is higher. We provide
  selectors for arguments. *)

  Inductive position := internal | external.
  Instance pos_eq_eqdec : EqDec position eq. derive_eq. Defined.

  Definition argument_at (p : position) (fs : features) :=
    match p with
      | internal => option_map fst (args fs)
      | external => option_flatMap snd (args fs)
    end.

  (** This is where it starts to get interesting. We need a predicate
  that decides whether or not the features [hfs] of the head license
  the features [fs] of a constituent which wishes to be merged to it
  at some position [p]. The predicate is satisfied if [fs] is
  saturated, and there is an argument [arg] at [p] in [hfs] whose
  category is equal to the category of [fs]. *)

  (** We can say that a node is saturated at a position if there is no
  specification for an argument present. This is because these
  specifications are erased after each merge. *)

  Definition saturated_at (p : position) (fs : features) :=
    match argument_at p fs with
      | Some sat => true
      | _ => false
    end.

  (** First, we determine if a merge is even plausible: for C-merge,
  the internal argument must not already be saturated; for S-merge,
  the internal argument must be saturated, and the external argument
  must not be. *)

  Definition saturated_up_to (p : position) (fs : features) :=
    match p with
      | external => saturated_at internal fs
      | _ => true
    end.

  Definition can_merge_at (p : position) (fs : features) :=
    negb (saturated_at p fs) && (saturated_up_to p fs).

  (** Now, we can check if the merge will be successful, given the
  syntactic category of each of the participants. *)

  Definition selects (p : position) (hfs : features) (fs : features) :=
    match argument_at p hfs with
      | Some (unsat a) => cat a ==b cat fs
      | _ => false
    end.

  (** Finally, we are ready to model nodes. A node is indexed by its
  features, and may be either a head (minimal projection), or the
  result of a [merge] (merging of a complement into internal argument
  position, or merging of a specifier into external argument position)
  The type of the [merge] constructor is computed at position [p] as
  follows:

  We require a proof that the head selects for the new node. The
  resulting node inherits the category of the head, and has its [iArg]
  saturated; if [p] is external, that means that the [eArg] has also
  been saturated. *)

  Definition saturate_at (p : position) (hfs : features) : arguments features :=
    match p with
      | external => Some (sat, Some sat)
      | internal => Some (sat, argument_at external hfs)
    end.

  Inductive node : features -> Set :=
  | head : forall (_ : string) (fs : features), node fs
  | merge : forall (p : position) {hfs : _} {fs : _},
              node hfs -> node fs
              -> Is_true (selects p hfs fs && can_merge_at p hfs)
              -> node {| cat := cat hfs ; args := saturate_at p hfs |}.


  (** As a bonus, we provide a function to fold a node into a string. *)
  Fixpoint to_string {fs : _} (n : node fs) :=
    match n with
      | head s _ => s
      | merge internal _ _ h c _ => append (to_string h) (append " " (to_string c))
      | merge external _ _ h s _ => append (to_string s) (append " " (to_string h))
    end.

End CoreTheory.

Module Notations.
  Import CoreTheory.

  (** Let's make some convenient notation for merges. Note that [I] is
  the single constructor for the type [True], and serves as the
  proof-witness that the head selects the merged node. *)

  Notation " head |- comp " := (merge internal head comp I)
                               (right associativity, at level 100).
  Notation " spec -| head " := (merge external head spec I)
                               (left associativity, at level 101).

  Definition mkArg (c : category) := unsat (Build_features c None).
  Notation " <| i |> "     := (Some (mkArg i, None)).
  Notation " <| i , e |> " := (Some (mkArg i, Some (mkArg e))).

End Notations.
  
Module Examples.
  Import CoreTheory.
  Import Notations.

  (** Let's build up a lexicon. *)
  Definition dog     := head "dog"  {| cat := N ; args := None |}.
  Definition love    := head "love" {| cat := V ; args := <| D , D |> |}.
  Definition the     := head "the"  {| cat := D ; args := <| N |> |}.
  Definition fst_prn := head "I"    {| cat := D ; args := None |}.

  (** We can now build up some phrases. If they type check, then they
  are grammatical within our theory. *)

  Definition the_dog        := the |- dog.
  Definition love_the_dog   := love |- the |- dog.
  Definition I_love_the_dog := fst_prn -| love |- the |- dog.

  (** The last phrase that we constructed represents the following tree:
           V
          / \
         /   \
        /     \
       I      V
             / \
            /   \
           /     \
         love    D
                / \
               /   \
              /     \
             the    dog
   *)

  (** Evaluating our phrase as a string yields ["I love the dog"]. *)
  Eval simpl in to_string I_love_the_dog.

End Examples.
