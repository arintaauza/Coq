Lemma exo1_1 : 
forall m : nat, 0 + m = m.
Proof.
intros.
reflexivity.
Qed.

Lemma exo1_2 :
forall m n : nat, S n + m = S (n + m).
Proof.
intros.
simpl.
f_equal.
Qed.

Lemma plus_n_0 :
forall n, n + 0 = n.
Proof.
intros.
induction n.
 - simpl. reflexivity.
 - simpl. f_equal. apply IHn.
Qed.

Lemma plus_n_Sm :
forall n m, n + S m = S (n + m).
Proof.
intros.
induction n.
 - simpl. f_equal.
 - simpl. f_equal. apply IHn.
Qed.

Lemma exo2_1 :
forall m : nat, 0 * m = 0.
Proof.
intros.
reflexivity.
Qed.

Lemma exo2_1_2 :
forall m n : nat, S n * m = m + n * m.
Proof.
intros.
reflexivity.
Qed.

Lemma exo2_2 :
forall m : nat, m * 0 = 0.
Proof.
intros.
induction m; simpl.
 - reflexivity.
 - apply IHm.
Qed.


Lemma associative :
forall n m p : nat, (n + m) + p = n + (m + p).
Proof.
intros.
induction n; simpl.
 - reflexivity.
 - f_equal. apply IHn.
Qed.

Lemma commutativite :
forall n m: nat, n + m = m +n.
Proof.
intros.
induction m; simpl.
 - apply plus_n_0.
 - rewrite plus_n_Sm. f_equal. apply IHm.
Qed.

Lemma exo2_2_2 :
forall m n : nat, n * S m = n + n * m.
Proof.
intros.
induction n; simpl.
 - reflexivity.
 - f_equal. rewrite IHn. rewrite <- 2 associative. f_equal. apply commutativite.
Qed.

Lemma distributivite :
forall n m p : nat, (n + m) * p = n * p + m * p.
Proof.
intros.
induction n; simpl.
 - reflexivity.
 - rewrite IHn. rewrite <- associative. reflexivity.
Qed.

Lemma mul_commutativite :
forall n m : nat, n * m = m * n.
Proof.
intros.
induction m; simpl.
 - apply exo2_2.
 - rewrite <- IHm. apply exo2_2_2.
Qed.

Lemma mul_associativite :
forall n m p : nat, n * (m * p) = (n * m) * p.
Proof.
intros.
induction n; simpl.
 - reflexivity.
 - rewrite IHn. rewrite distributivite. reflexivity.
Qed.

Definition le (n m : nat) := exists p, n + p = m.

Lemma le_refl : forall n, le n n.
Proof.
intros.
exists 0.
apply plus_n_0.
Qed.

Lemma le_trans : forall n m p, le n m -> le m p -> le n p.
Proof.
intros.
destruct H.
destruct H.
destruct H0.
exists (x + x0).
rewrite <- associative.
apply H.
Qed.

Lemma le_antisym : forall n m, le n m -> le m n -> n = m.
Proof.
intros.
destruct H.
destruct H.
induction n; simpl.
 - destruct H0.