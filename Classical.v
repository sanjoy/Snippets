Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 
Notation "P /\ Q" := (and P Q) : type_scope.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.


Definition pierce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q). 

Theorem pierce_classic: pierce <-> classic.
Proof.
  unfold iff. unfold pierce. unfold classic. unfold not.
  split.

  (** From Pierce to Classic *)
  intros Pierce P Classic.
  assert ((P -> False) -> P) as P_False_P.
    intros P_False. 
    apply Classic in P_False. 
    inversion P_False. (** P_False is false now *)
  apply Pierce in P_False_P. (** P_False_P is now P *)
  apply P_False_P.

  (** From Classic to Pierce *)
  intros Classic P Q P_Q_P.
  assert ((P -> False) -> False) as P_Classic.
    intros P_False.
    assert (P -> Q) as P_Q.
      intros Given_P.
      apply P_False in Given_P.
      inversion Given_P. (** Given_P is false *)
    apply P_Q_P in P_Q. (** P_Q_P is now P *)
    apply P_False in P_Q.
    apply P_Q.
  apply Classic in P_Classic. (** P_Classic is P now *)
  apply P_Classic.
Qed.

Theorem classic_de_morgan : classic <-> de_morgan_not_and_not.
Proof.
  unfold iff. unfold classic. unfold de_morgan_not_and_not. unfold not.
  split.

  (** From Classic to De Morgan *)
  intros Classic P Q P_False_Q_False_False.
  apply Classic.
  intros P_Or_Q_False.

  assert ((P -> False) /\ (Q -> False)).
    split.
    (** P is False *)
    intros.
    apply or_introl with (Q:=Q) in H.
    apply P_Or_Q_False in H. apply H.

    (** Q is False *)
    intro.
    apply or_intror with (P:=P) in H.
    apply P_Or_Q_False in H. apply H.

  apply P_False_Q_False_False in H. apply H.

  (** From De Morgan to Classic *)
  intros De_Morgan P Classic.

  assert ((P -> False) /\ (P -> False) -> False).
    intros.
    inversion H as [P_False0 P_False1]. 
      apply Classic in P_False0. apply P_False0.

  apply De_Morgan in H. 
  inversion H as [Ans_0 | Ans_1].
    apply Ans_0. 
    apply Ans_1.
Qed.  


Theorem classic_excluded_middle : classic <-> excluded_middle.
Proof.
  unfold iff. unfold classic. unfold excluded_middle. unfold not.
  split.

  (** Classic to Excluded Middle *)
  intros Classic P.
  apply Classic.
  intros H.
  assert ((P -> False) -> False) as P_False_False.
    intro P_False.
    apply or_intror with (P:=P) in P_False.
    apply H in P_False.
    apply P_False.
  apply Classic in P_False_False.
  apply or_introl with (Q:=(P -> False)) in P_False_False.
  apply H in P_False_False.
  apply P_False_False.

  (** Excluded Middle to Classic *)
  intros H Prp Double_Neg.
  specialize H with Prp.
  inversion H as [P | NegP].
  (** P is true *)
  apply P.
  (** P is false *)
  apply Double_Neg in NegP. inversion NegP.
Qed.


Theorem excluded_middle_implies_to_or : excluded_middle <-> implies_to_or.
Proof.
  unfold iff. unfold excluded_middle. unfold implies_to_or. unfold not.
  split.
  
  intros Excluded_Middle P Q Implication.
  specialize Excluded_Middle with P.
  inversion Excluded_Middle.
    apply Implication in H. right. apply H.
    left. apply H.

  intros Implies_To_Or P.
  specialize Implies_To_Or with P P.
  assert (P -> P).
    intros. apply H.
  apply Implies_To_Or in H.
  inversion H as [HL | HR]. 
    right. apply HL.
    left. apply HR.
Qed.
