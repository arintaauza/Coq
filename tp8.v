Parameter T : Set.

Inductive clos1 (R : T -> T -> Prop) : T ->  T -> Prop :=
   | cl1_base : forall x y, R x y -> clos1 R x y
   | cl1_refl : forall x, clos1 R x x
   | cl1_trans : forall x y z, clos1 R x y -> clos1 R y z -> clos1 R x z.

Check clos1_ind.

Lemma sym : forall (R : T -> T -> Prop),
  (forall x y, R x y -> R y x) ->
  (forall x y, clos1 R x y -> clos1 R y x).
Proof.
intros R Sym n m H. induction H.
  - apply cl1_base. apply Sym. assumption.
  - apply cl1_refl.
  - apply cl1_trans with y.
    + assumption.
    + assumption.
Qed.


Inductive clos2 (R : T -> T -> Prop) : T -> T -> Prop :=
   | cl2_refl : forall x, clos2 R x x
   | cl2_next : forall x y z, clos2 R x y -> R y z -> clos2 R x z.

Lemma refl_1 :
  forall (R : T -> T -> Prop) x y, clos2 R x y -> clos1 R x y.
Proof.
intros.
induction H.
  - apply cl1_refl.
  - apply cl1_trans with y.
    + assumption.
    + apply cl1_base. assumption.
Qed.

Lemma exo2_2 :
  forall (R : T -> T -> Prop) x y, R x y -> clos2 R x y.
Proof.
intros.
apply cl2_next with x.
  - apply cl2_refl.
  - assumption.
Qed.

Lemma exo2_3 :
  forall (R : T -> T -> Prop) x y z,
  clos2 R x y -> clos2 R y z -> clos2 R x z.
Proof.
intros.
induction H0.
  - assumption.
  - apply cl2_next with y. (* auto pour laisser Coq conclure *)
    + apply IHclos2. assumption.
    + assumption.
Qed.

Lemma exo2_4 :
  forall (R : T -> T -> Prop) x y, clos1 R x y -> clos2 R x y.
intros.
induction H.
  - apply exo2_2. assumption.
  - apply cl2_refl.
  - apply exo2_3 with y.
    + assumption.
    + assumption.
Qed.

Lemma exo2_5 :
  forall (R : T -> T -> Prop) x y,
  clos1 (clos1 R) x y <-> clos1 R x y.
Proof.
intros.

