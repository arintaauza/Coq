Open Scope list_scope.

Inductive alpha : Set := M : alpha | I : alpha | U : alpha.
Definition word : Set := list alpha.
Check length.

Definition word_M : list alpha := M :: nil.
Definition word_MI := M::I::nil.
Definition word_MU := M::U::nil.
Definition word_I := I::nil.
Definition word_IU := I::U::nil.
Definition word_III := I::I::I::nil.
Definition word_U := U::nil.
Definition word_UU := U::U::nil.


Inductive lang : word -> Prop :=
  | axiom :
      lang word_MI
  | rule1 : forall x,
      lang (x ++ word_I) -> lang (x ++ word_IU)
  | rule2 : forall x,
      lang (word_M ++ x) -> lang (word_M ++ x ++ x)
  | rule3 : forall x y,
      lang (x ++ word_III ++ y) -> lang (x ++ word_U ++ y)
  | rule4 : forall x y, 
      lang (x ++ word_UU ++ y) -> lang (x ++ y).

  Definition hd_error (l:word) : option alpha :=
    match l with
      | nil => None
      | x :: _ => Some x
    end.

Lemma commence_par_M :
  forall m : word, lang m -> hd_error m = Some M.
Proof.
intros.
induction H.
  - simpl. reflexivity.
  - destruct x.
    + simpl in *. 
    (* *)
    discriminate. 
    (* on a faux dans l'hypothèse donc 
    chouet on peut tout prouver avec.
    on peut aussi utiliser assumption. *)
    + simpl in *. assumption.
  - simpl. assumption.
  - destruct x.
    + simpl in *. discriminate.
    + simpl in *. assumption.
  - destruct x.
    + simpl in *. discriminate.
    + simpl in *. assumption.
Qed.


Inductive Z3 : Set := Z0 : Z3 | Z1 : Z3 | Z2 : Z3.

