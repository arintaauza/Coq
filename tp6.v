Open Scope list_scope.

Lemma exo1_1 :
forall (A : Type) (l : list A), nil ++ l = l.
Proof.
intros.
simpl.
reflexivity.
Qed.

Lemma exo1_1copy :
forall (A : Type) (l : list A), nil ++ l = l.
Proof.
intros.
simpl.
reflexivity.
Qed.

Lemma exo1_2 :
forall (A : Type) (l : list A), l ++ nil = l.
Proof.
intros.
induction l.
 - simpl. reflexivity.
 - simpl.  f_equal. apply IHl.
Qed.


Lemma exo1_2copy :
forall (A : Type) (l : list A), l ++ nil = l.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

Lemma exo1_2_bis :
forall (A : Type) (l : list A), l ++ nil = l.
Proof.
intros.
induction l.
 - simpl. reflexivity.
 - simpl. rewrite IHl. reflexivity.
Qed.


Lemma associativity :
forall (A : Type) (l1 l2 l3 : list A), (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
intros.
induction l1.
 - simpl. reflexivity.
 - simpl. f_equal. apply IHl1.
Qed.
Print length.
Check length.

Lemma associativitycopy :
forall (A : Type) (l1 l2 l3 : list A), (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
intros.
induction l1. simpl. auto.
simpl. rewrite IHl1. auto.
Qed.


Fixpoint length {A:Type}(l : list A) : nat :=
match l with
| nil       => 0
| cons x tl => 1 + length tl
end.

Fixpoint lengthcopy {A:Type}(l : list A) : nat :=
match l with
 | nil => 0
 | a::l' => S(length l')
end.

Compute lengthcopy (1::2::3::nil).

Lemma exo2_3 :
forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2.
Proof.
intros.
induction l1; simpl.
 - reflexivity.
 - f_equal. apply IHl1.
Qed.

Lemma exo2_3copy :
forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2.
Proof.
intros.
induction l1.
simpl. auto.
simpl. f_equal. apply IHl1.
Qed.


Fixpoint rev_append {A : Type} (l1 l2 : list A) : list A :=
match l1 with
 | nil => l2
 | cons a tl => cons a (rev_append tl l2)
end.

Compute cons 1 (1::2::nil).

Fixpoint rev_appendcopy {A : Type} (l1 l2 : list A) : list A :=
match l1 with
 | nil => l2
 | cons a l => (rev_appendcopy l l2) ++ cons a nil
end. 

Compute rev_appendcopy (1::2::3::4::nil) (5::6::nil).

Fixpoint reverse {A : Type} (l : list A) : list A :=
match l with
 | nil => nil
 | a::l => (reverse l) ++ a::nil
end.

Definition reversevopy {A : Type} (l : list A) : list A :=
rev_appendcopy l nil.

Compute reversevopy (1::2::3::4::nil).

Lemma rev_append_length :
forall (A : Type) (l l': list A), length (rev_append l l') = length l + length l'.
Proof.
intros.
induction l; simpl. 
 - reflexivity.
 - f_equal. apply IHl.
Qed.

Lemma plusOne :
forall (A: Type) (l : list A) (a : A), 
length (l ++ (a::nil)) = S (length l) .
Proof.
intros.
induction l.
simpl. auto.
simpl. f_equal. apply IHl.
Qed.


Lemma rev_append_lengthcopy :
forall (A : Type) (l l': list A), length (rev_appendcopy l l') = length l + length l'.
Proof.
intros.
induction l; simpl; auto. 
rewrite plusOne. f_equal. apply IHl.
Qed.

Lemma exo3_2copy :
forall (A : Type) (l : list A), length (reversevopy l) = length l.
Proof.
intros. unfold reversevopy. simpl. rewrite rev_append_lengthcopy.
simpl. auto.
Qed.

Lemma exo3_2 :
forall (A : Type) (l : list A), length (reverse l) = length l.
Proof.
intros.
induction l; simpl.
 - reflexivity.
 - f_equal. rewrite <- IHl. unfold reverse. unfold rev_append. apply (length l).
   rewrite rev_append_length. simpl. unfold length.


unfold length. apply rev_append_length. simpl.  unfold reverse. unfold rev_append.  apply rev_append_length with (l' := nil). unfold reverse. rewrite rev_append.