Lemma exo1_3 :
forall A B : Prop, A /\ B <-> B /\ A.
Proof.
split.
- intro. destruct H. split. assumption. assumption.
- intro. destruct H. split. assumption. assumption.
Qed.

Lemma exo1_6 :
forall A B C : Prop, (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
split.
- intro. destruct H. destruct H.
  + left. assumption.
  + right. left. assumption.
  + right. right. assumption.
- intro. destruct H.
  + left. left. assumption.
  + destruct H. left. right. assumption. right. assumption.
Qed.