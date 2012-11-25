Require Import String EquivDec.
Set Implicit Arguments.

Section CoreTheory.

  (** We'll start with a few syntactic categories. This is of course
  not sufficient to do real syntax, but it will do for now. *)
  Inductive category := D | N | V.

  (** Each constituent is marked by a set of features; in our current
  theory, features are just a syntactic category, and specifications
  for internal and external arguments. *)

  Inductive features : Set :=
      { cat : category ;
        iArg : option features ;
        eArg : option features
      }.


  (** Coq allows us to derive decidable equality for categories. This will prove useful below. *)
  Theorem eq_cat_dec (a : category) (b : category) : {a = b} + {a <> b}.
  Proof.
    decide equality.
  Defined.
  Program Instance cat_eq_eqdec : EqDec category eq := eq_cat_dec.

  (** In our current theory, there are two kinds of arguments:
  internal and external; an internal argument is lower in the tree
  than the head, whereas an external argument is higher. We provide
  selectors for arguments. *)

  Inductive position := internal | external.
  Definition argument_at (p : position) :=
    match p with
      | internal => iArg
      | external => eArg
    end.

  (** If a node is saturated, that means that it has no room for
  either an internal or an external argument. *)

  Definition is_saturated (fs : features) :=
    match iArg fs with
      | None =>
        match eArg fs with
          | None => True
          | _    => False
        end
      | _ => False
    end.
  
  (** This is where it starts to get interesting. We need a predicate
  that decides whether or not the features [hfs] of the head license
  the features [fs] of a constituent which wishes to be merged to it
  at some position [p]. The predicate is satisfied if [fs] is
  saturated, and there is an argument [arg] at [p] in [hfs] whose
  category is equal to the category of [fs]. *)

  Fixpoint can_merge_at (hfs : features) (p : position) :=
    match p with
      | internal => match iArg hfs with
                     | Some _ => True
                     | None   => False
                   end
      | external => match iArg hfs with
                   | Some _ => False
                   | None => match eArg hfs with
                              | Some _ => True
                              | None   => False
                            end
                 end
    end.

  Fixpoint selects (p : position) (hfs : features) (fs : features) :=
    match argument_at p hfs with
      | Some arg =>
        match cat arg == cat fs with
          | left  _ => match is_saturated fs with
                        | True => can_merge_at hfs p
                      end
          | right _ => False
        end
      | None => False
    end.

  (** We now compute the type of a merge at position [p]. We require a
  proof that the head selects for the new node. The resulting node
  inherits the category of the head, and has its [iArg] saturated; if
  [p] is external, that means that the [eArg] has also been
  saturated. *)

  Definition gen_merge (N : features -> Set) (p : position) :=
    forall (hfs : _) (fs : _)
      (h : N hfs) (n : N fs)
      (sel : selects p hfs fs),
      N {| cat := cat hfs ;
           iArg := None ;
           eArg := match p with
                    | internal => eArg hfs
                    | external => None
                  end
        |}.

  (** Finally, we are ready to model nodes. A node is indexed by its
  features, and may be either a head (minimal projection), or the
  result of a [cmerge] (merging of a complement into internal argument
  position), or the result of an [smerge] (merginf of a specifier into
  external argument position). The types of the latter two
  constructors are computed using [gen_merge] above. *)

  Inductive node : features -> Set :=
  | head : forall (s : string), forall (fs : features), node fs
  | cmerge : gen_merge node internal
  | smerge : gen_merge node external.

  (** As a bonus, we provide a function to fold a node into a string. *)
  Fixpoint to_string {fs : _} (n : node fs) : string :=
    match n with
      | head s _ => s
      | cmerge _ _ h c _ => append (to_string h) (append " " (to_string c))
      | smerge _ _ h s _ => append (to_string s) (append " " (to_string h))
    end.

End CoreTheory.

Section Examples.

  (** Let's make some convenient notation for merges. Note that [I] is
  the single constructor for the type [True], and serves as the
  proof-witness that the head selects the merged node. *)

  Notation " head |- comp " := (cmerge head comp I)
                               (right associativity, at level 100).
  Notation " spec -| head " := (smerge head spec I)
                               (left associativity, at level 101).
  
  (** Let's build up a lexicon. *)
  Definition dog :=
    head "dog"
         {| cat := N ; iArg := None ; eArg := None |}.

  Definition love :=
    head "love"
         {| cat  := V ;
            iArg := Some {| cat := D ; iArg := None ; eArg := None |} ;
            eArg := Some {| cat := D ; iArg := None ; eArg := None |}
         |}.

 
  Definition the :=
    head "the"
         {| cat  := D ;
            iArg := Some {| cat := N ; iArg := None ; eArg := None |} ;
            eArg := None
         |}.

  Definition I :=
    head "I"
         {| cat := D ; iArg := None ; eArg := None |}.

  (** We can now build up some phrases. If they type check, then they
  are grammatical within our theory. *)

  Definition the_dog := the |- dog.
  Definition love_the_dog := love |- the |- dog.
  Definition I_love_the_dog := I -| love |- the |- dog.

  Eval simpl in to_string fuck.

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